# validate — the membership-decision arm of typechecking, with closed inputs.
#
# validateClosed is the two-armed decision procedure: decide membership with the
# kernel oracle, then either let the value pass or raise the typeCheck effect:
#
#   validateClosed t v context reason path diagError =
#     if decide t v then pure v
#     else send "typeCheck" { type = t; context; value = v; reason; path; diagError; }
#
# It is the minimal generalization of the auto-derived validateAt (which computes
# context/reason/path/diagError from the type it walks) to a form that takes those
# four as closed inputs. The decision is host-layer: `decide` is the Nix oracle
# `elaborate.decide : Hoas -> NixVal -> Bool`, and pure/send build the host
# Computation, so the derived membership El collapses — a pass is `pure v`, a
# rejection is the suspended `send`. There is no dependent El obligation after the
# send (a Computation is an untyped host value), so the rejection arm simply
# suspends; no membership witness is ever forged.
#
# The decision is made here, so the typeCheck payload carries the kernel type term
# itself and the caller-supplied reason/path/diagError; a consumer reads the
# diagnostic from those rather than re-deciding. The auto-derived validateAt path,
# whose payload carries a full surface type, remains the one driven by the stock
# strict/collecting/... handlers.
#
# validateK is the kernel-internal counterpart: a closed producer
#   validateK R t reason path carrier x : freeFx (EffTypeCheck R) Resp Unit
# emitting one `report` op whose decision is the KType decider on the carrier
# (`decide t x`), not a host bool. Returns Unit; an El witness on success would
# need propositional equality the substrate lacks, so the decision rides in the op.
{ fx, api, ... }:

let
  H = fx.tc.hoas;
  app = H.app;

  decide = fx.tc.elaborate.decide;
  pure = fx.kernel.pure;
  send = fx.kernel.send;

  validateClosed = t: v: context: reason: path: diagError:
    if decide t v
    then pure v
    else send "typeCheck" {
      type = t;
      inherit context reason path diagError;
      value = v;
    };

  KT = fx.tc.kernel.ktype;
  K = fx.experimental.desc-interp.kernel;
  DescD = fx.experimental.desc-interp.desc;
  EffErr = fx.experimental.desc-interp.effects.error;
  TC = fx.experimental.desc-interp.effects.typecheck;
  EffTC = TC.EffTypeCheck;
  Resp = TC.Resp;

  reportAt = R: reason: path: carrier: passed:
    app (app (app (app (app EffTC.report R) reason) path) carrier) passed;

  validateK = R: t: reason: path: carrier: x:
    let eff = app EffTC.T R; resp = app Resp R; in
    K.bind eff resp H.unit H.unit
      (K.send eff resp (reportAt R reason path carrier (app (KT.decide t) x)))
      (_: K.pure eff resp H.unit H.tt);

  # Propositional equality over Bool on the public EqDT surface (eq /
  # reflDT / j). The El-returning certifier needs to carry the Bool
  # decision proof from the case-split into the membership witness, so it
  # works with real `Eq Bool` evidence rather than the bootstrap layer.
  boolT = H.bool;
  eqB = a: b: H.eq boolT a b;
  reflB = a: H.reflDT boolT a;
  # symB a b (e : a = b) : b = a.
  symB = a: b: e:
    H.j boolT a (H.lam "c" boolT (c: H.lam "_" (eqB a c) (_: eqB c a))) (reflB a) b e;
  # transportP a b (e : a = b) (ma : P a) : P b — moves a P-witness along
  # a Bool equality, the step that turns `decide t x = true` into the
  # membership component `P (decide t x)` of `El t`.
  transportP = a: b: e: ma:
    H.j boolT a (H.lam "c" boolT (c: H.lam "_" (eqB a c) (_: KT.P c))) ma b e;
  # boolCaseEq lev b C pt pf : C, with the per-branch decision proof in
  # hand — pt : (b = true) -> C, pf : (b = false) -> C. Motive
  # Q x = (b = x) -> C; boolElim picks the branch, then is fed reflB b.
  boolCaseEq = lev: b: C: pt: pf:
    let Q = H.lam "x" boolT (x: H.forall "_" (eqB b x) (_: C)); in
    app (H.boolElim lev Q pt pf b) (reflB b);

  effErr = R: app EffErr.EffError.T R;
  respErr = R: app EffErr.Resp_strict R;
  freeErr = R: a: H.mu (DescD.freeFxApp (effErr R) (respErr R) a) H.tt;

  # validateEl — the El-returning certifier, the membership-witness dual
  # of validateK. Given a candidate carrier x : beta t, it produces the
  # dependent membership witness El t when the KType decider accepts, and
  # otherwise aborts carrying the caller-supplied payload (type R).
  #
  #   validateEl R t payload x : freeErr R (El t)
  #
  # The accept arm transports the decision proof `decide t x = true` into
  # the membership component P (decide t x), yielding the pair
  # (x, witness) : El t. The reject arm rides EffError's strict response
  # (Resp_strict R op ≡ Void): the raise's continuation receives a Void
  # and is discharged by `absurd`, so the never-taken success value is
  # produced from ⊥ — no membership witness is ever forged. R is opaque;
  # the kernel does not format diagnostics, exactly as validateK ferries
  # its carrier R.
  validateEl = R: t: payload: x:
    let
      eff = effErr R;
      resp = respErr R;
      El = KT.El t;
      dtx = app (KT.decide t) x;
      C = freeErr R El;
      errOp = app (app EffErr.EffError.error R) payload;
      pass = H.lam "_eq" (eqB dtx H.true_) (eq:
        K.pure eff resp El
          (H.ann (H.pair x (transportP H.true_ dtx (symB dtx H.true_ eq) H.tt)) El));
      fail = H.lam "_eq" (eqB dtx H.false_) (_:
        K.bind eff resp H.void El
          (K.send eff resp errOp)
          (v: H.absurd C v));
    in
    boolCaseEq 1 dtx C pass fail;
in
{
  scope = {
    validate = api.namespace {
      description = "fx.tc.kernel.validate: the membership-decision arm of typechecking. validateClosed t v context reason path diagError decides membership with the kernel oracle (elaborate.decide) and either returns `pure v` or raises the host `typeCheck` effect with the caller-supplied diagnostics — the closed-input generalization of the auto-derived validateAt. validateK R t reason path carrier x is the kernel-internal report producer: it emits one kernel `report` op whose decision is the KType decider applied to the carrier (`decide t x`), returning `freeFx (EffTypeCheck R) Resp Unit` for the kernel handlers to fold. validateEl R t payload x is the kernel-internal certifier — the membership-witness dual of validateK: it produces the dependent witness `El t` when `decide t x` accepts, and otherwise aborts on EffError's strict (Void-response) raise carrying the opaque payload, so no witness is ever forged; returns `freeFx (EffError R) Resp_strict (El t)`.";
      value = {
        inherit validateClosed validateK validateEl;
      };
    };
  };

  tests =
    let
      H = fx.tc.hoas;
      decideOracle = fx.tc.elaborate.decide;
      isPure = fx.comp.isPure;
      run = fx.trampoline.run;
      foundation = fx.types.foundation;
      mkType = foundation.mkType;
      refine = foundation.refine;
      stdValidate = foundation.validate;
      collecting = fx.effects.typecheck.policy.collecting;
      strict = fx.effects.typecheck.policy.strict;
      Field = fx.diag.positions.Field;

      intT = mkType { name = "Int"; kernelType = H.int_; };
      t = intT._kernel;
      # A closed diagnostic, supplied to validateClosed as an opaque input.
      de = fx.diag.error.mkGenericError {
        type = "Int";
        context = "Int";
        value = "nope";
        msg = "type check failed";
      };
      vc = validateClosed t;

      natT = refine intT (x: x >= 0);
      grid = [ 42 (-1) "x" 0 7 ];

      # validateK fixtures
      Tr = fx.experimental.desc-interp.trampoline;
      DescD = fx.experimental.desc-interp.desc;
      reflect = fx.tc.kernel.reflect;
      evK = h: fx.tc.eval.eval [ ] (H.elab h);
      convH = a: b: fx.tc.conv.conv 0 (evK a) (evK b);
      convState = r: exp: fx.tc.conv.conv 0 r.state (evK exp);
      chkK = ty: h: !((H.checkHoas ty h) ? error);

      # Reason value rebuilt structurally (its constructors are not exported).
      ReasonV = H.datatype "Reason" [
        (H.con "shapeMismatch" [ ])
        (H.con "missingField" [ ])
        (H.con "extraField" [ ])
        (H.con "predicateFailed" [ ])
        (H.con "deferredPi" [ ])
      ];
      rPredK = ReasonV.predicateFailed;
      pathNilK = H.ann H.nil TC.Path;
      Rk = H.unit;
      carrierK = H.tt;

      # A bool-id refinement and a positive-Int code, both kernel-decidable.
      tBoolK = KT.refine (KT.iota H.bool) (H.lam "x" H.bool (x: x));
      posKType = reflect.ktypeOf reflect.intPositive;

      collStK = TC.atType_collecting Rk;
      strictStK = TC.atType_strict Rk;
      runTCk = st: prog: init:
        Tr.run st.eff st.resp H.unit { inherit (st) handler dispatch; } prog init;
      strictThrewK = r: !(builtins.tryEval (builtins.seq (r.state.tag or "?") true)).success;
      initCollK = H.ann H.nil (H.listOf Rk);
      strictInitK = H.ann H.tt H.unit;
      oneFail = H.ann (H.cons carrierK H.nil) (H.listOf Rk);
      vProgK = t: x: validateK Rk t rPredK pathNilK carrierK x;
      progTyK = H.mu (DescD.freeFxApp (app EffTC.T Rk) (app Resp Rk) H.unit) H.tt;

      # validateEl (El-returning certifier) fixtures. The certifier itself
      # and its equality/transport machinery are top-level; the tests only
      # need a closed Π-form to check and a strict-handler run harness.
      vElTy = R: t: H.forall "x" (KT.beta t) (_: freeErr R (KT.El t));
      vElTm = R: t: payload: H.lam "x" (KT.beta t) (x: validateEl R t payload x);
      errSt = EffErr.atType_strict H.unit H.unit;
      runErr = prog:
        Tr.run errSt.eff errSt.resp (KT.El tBoolK)
          { inherit (errSt) handler dispatch evalOp; } prog strictInitK;
      errThrew = prog: !(builtins.tryEval (builtins.seq (runErr prog).value true)).success;

      # Decomposition fixtures for the strict-run claim. validateEl is
      # app(boolElim)-headed, so it resolves to a desc-con only under kernel
      # reduction; the trampoline is a shallow syntactic walker that reads the
      # desc-con head directly and never reduces. So the end-to-end claim is
      # split: a conv equation pins each arm of validateEl to a syntactic
      # free-monad program, and the strict handler's behavior is exercised on
      # that program. The reject arm reduces to rejectProg (an EffError raise
      # on the strict Void response, its continuation discharged by absurd),
      # the accept arm to pureProg (its accept conv is validateel-pass-conv).
      errOpEl = app (app EffErr.EffError.error Rk) carrierK;
      rejectProg = K.bind (effErr Rk) (respErr Rk) H.void (KT.El tBoolK)
        (K.send (effErr Rk) (respErr Rk) errOpEl)
        (v: H.absurd (freeErr Rk (KT.El tBoolK)) v);
      pureProg = K.pure (effErr Rk) (respErr Rk) (KT.El tBoolK)
        (H.ann (H.pair H.true_ H.tt) (KT.El tBoolK));
    in
    {
      # Pass arm: decide = true reduces to `pure v` (the membership-witness pair
      # collapses to the value, since P true carries no data).
      "validate-pass-is-return" = {
        expr = let c = vc 42 "Int" "shape-mismatch" [ ] de; in isPure c && c.value == 42;
        expected = true;
      };
      # A passing validation sends no effect, so a collecting run stays empty.
      "validate-pass-no-effect-under-collecting" = {
        expr = (run (vc 42 "Int" "shape-mismatch" [ ] de) collecting [ ]).state;
        expected = [ ];
      };

      # Fail arm: decide = false suspends at the typeCheck effect carrying the
      # closed payload.
      "validate-fail-is-send" = {
        expr =
          let c = vc "nope" "Int" "shape-mismatch" [ ] de;
          in [ (isPure c) c.effect.name c.effect.param.reason c.effect.param.value ];
        expected = [ false "typeCheck" "shape-mismatch" "nope" ];
      };
      # The caller-supplied diagError and path flow through verbatim.
      "validate-fail-carries-diagError" = {
        expr = (vc "nope" "Int" "shape-mismatch" [ ] de).effect.param.diagError.layer.tag;
        expected = "Generic";
      };
      "validate-fail-carries-path" = {
        expr = (vc "nope" "Int" "shape-mismatch" [ (Field "a") ] de).effect.param.path;
        expected = [ (Field "a") ];
      };

      # The validator agrees with the bare decider at every witness.
      "validate-decide-agreement" = {
        expr = builtins.map (x: decideOracle t x == isPure (vc x "Int" "shape-mismatch" [ ] de)) grid;
        expected = [ true true true true true ];
      };

      # The rejection arm under the stock handlers: strict throws, collecting
      # resumes false and records the failure — the substrate realization of the
      # otherwise-impossible El branch.
      "validate-strict-throws-on-failure" = {
        expr = (builtins.tryEval (run (intT.validate "x") strict null).value).success;
        expected = false;
      };
      "validate-collecting-resumes-false-on-failure" = {
        expr =
          let r = run (intT.validate "x") collecting [ ];
          in builtins.length r.state == 1 && r.value == false;
        expected = true;
      };

      # Host correspondence: a real rejected validateAt under collecting yields
      # the documented error-record shape.
      "validate-roundtrip-collecting-keys" = {
        expr = builtins.attrNames (builtins.head (run (intT.validate "x") collecting [ ]).state);
        expected = [ "actual" "context" "message" "path" "reason" "typeName" ];
      };

      # The auto-derived diagError discriminates the failing layer: a refinement
      # guard failure is Contract/predicate-failed, a shape failure is Generic.
      "validate-diagError-layer-contract" = {
        expr = (natT.validate (-1)).effect.param.diagError.layer.tag;
        expected = "Contract";
      };
      "validate-diagError-reason-predicate-failed" = {
        expr = (natT.validate (-1)).effect.param.reason;
        expected = "predicate-failed";
      };
      "validate-diagError-layer-generic" = {
        expr = (intT.validate "x").effect.param.diagError.layer.tag;
        expected = "Generic";
      };

      # The standalone 3-arg validate carries no diagError — the load-bearing
      # distinction from the auto-derived path.
      "validate-standalone-no-diagError" = {
        expr = (stdValidate intT 7 "ctx").effect.param ? diagError;
        expected = false;
      };

      # The codomain is the report-stream Unit.
      "validatek-well-typed" = {
        expr = chkK progTyK (vProgK tBoolK H.true_);
        expected = true;
      };
      # The decision is the KType decider, not a host literal.
      "validatek-decision-kernel-true" = {
        expr = convH (app (KT.decide tBoolK) H.true_) H.true_;
        expected = true;
      };
      "validatek-decision-kernel-false" = {
        expr = convH (app (KT.decide tBoolK) H.false_) H.false_;
        expected = true;
      };
      "validatek-collecting-pass-empty" = {
        expr = convState (runTCk collStK (vProgK tBoolK H.true_) initCollK) initCollK;
        expected = true;
      };
      "validatek-collecting-fail-records" = {
        expr = convState (runTCk collStK (vProgK tBoolK H.false_) initCollK) oneFail;
        expected = true;
      };
      "validatek-strict-pass-no-throw" = {
        expr = !(strictThrewK (runTCk strictStK (vProgK tBoolK H.true_) strictInitK));
        expected = true;
      };
      "validatek-strict-fail-throws" = {
        expr = strictThrewK (runTCk strictStK (vProgK tBoolK H.false_) strictInitK);
        expected = true;
      };
      # The internalizable Int fragment fires through the same path.
      "validatek-posint-pass" = {
        expr = convState (runTCk collStK (vProgK posKType (H.intLit 1)) initCollK) initCollK;
        expected = true;
      };
      "validatek-posint-fail" = {
        expr = convState (runTCk collStK (vProgK posKType (H.intLit (-1))) initCollK) oneFail;
        expected = true;
      };
      "validatek-posint-strict-throws-on-neg" = {
        expr = strictThrewK (runTCk strictStK (vProgK posKType (H.intLit (-1))) strictInitK);
        expected = true;
      };

      # ---- validateEl: the El-returning certifier ----------------------

      # The Bool-equality transport that carries `decide t x = true` into
      # the membership component computes: P-witness moves along refl to tt.
      "validateel-transport-refl-computes" = {
        expr = convH (transportP H.true_ H.true_ (reflB H.true_) H.tt) H.tt;
        expected = true;
      };

      # The certifier is a well-typed closed kernel term: a dependent
      # function beta t -> FreeFx (EffError R) (El t), at the bool-id
      # refinement and the internalizable positive-Int code.
      "validateel-well-typed" = {
        expr = chkK (vElTy Rk tBoolK) (vElTm Rk tBoolK carrierK);
        expected = true;
      };
      "validateel-well-typed-posint" = {
        expr = chkK (vElTy Rk posKType) (vElTm Rk posKType carrierK);
        expected = true;
      };
      # Parametric in the payload type: a non-trivial R (the diagnostic the
      # reject arm carries) checks just as well — R is opaque to the kernel.
      "validateel-well-typed-payload" = {
        expr = chkK (vElTy H.nat tBoolK) (vElTm H.nat tBoolK (H.natLit 0));
        expected = true;
      };

      # Accept-path conv-equation: decide t x = true ⊢ validateEl t x ≡
      # pure (x, witness); the transport collapses the membership component
      # to tt, so the witness is the pair (x, tt) : El t.
      "validateel-pass-conv" = {
        expr = convH (validateEl Rk tBoolK carrierK H.true_)
          (K.pure (effErr Rk) (respErr Rk) (KT.El tBoolK)
            (H.ann (H.pair H.true_ H.tt) (KT.El tBoolK)));
        expected = true;
      };
      "validateel-posint-pass-conv" = {
        expr = convH (validateEl Rk posKType carrierK (H.intLit 1))
          (K.pure (effErr Rk) (respErr Rk) (KT.El posKType)
            (H.ann (H.pair (H.intLit 1) H.tt) (KT.El posKType)));
        expected = true;
      };

      # The accept arm reduces to a Pure node; the reject arm to an Impure
      # (raise) node — the case-split genuinely discriminates on the decider.
      "validateel-pass-is-pure" = {
        expr = (evK (validateEl Rk tBoolK carrierK H.true_)).d.tag;
        expected = "VBootInl";
      };
      "validateel-fail-is-impure" = {
        expr = (evK (validateEl Rk tBoolK carrierK H.false_)).d.tag;
        expected = "VBootInr";
      };

      # Under the strict EffError handler, the end-to-end "validateEl runs to
      # witness-or-throw" claim splits into a kernel-reduction part (conv) and
      # a handler-behavior part on the resulting syntactic program.

      # The reject arm reduces to the canonical EffError raise carrying the
      # opaque payload op — the kernel-reduction half of "reject aborts".
      "validateel-reject-conv-send" = {
        expr = convH (validateEl Rk tBoolK carrierK H.false_) rejectProg;
        expected = true;
      };
      # The strict handler aborts on that raise — the Void response leaves the
      # success continuation undischargeable, so the El branch is never forged.
      "validateel-strict-aborts-on-reject" = {
        expr = errThrew rejectProg;
        expected = true;
      };
      # The strict handler returns on the accept's Pure form (accept ≡ pureProg
      # is validateel-pass-conv) — the membership witness survives, no abort.
      "validateel-strict-returns-on-accept" = {
        expr = !(errThrew pureProg);
        expected = true;
      };
    };
}
