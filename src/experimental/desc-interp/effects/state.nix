# State effect over `experimental.desc-interp.kernel.send`. Kernel-resident
# `EffState : Π(S:U). U` (three constructors) plus kernel-term
# `handle_State : Π(S A:U). Π(op:EffState S). Π(_s:S).
#   Sum (Σ _r:Resp_State[S,op], S) (Σ _a:A, S)`. The trampoline bridge
# (`trampoline.nix:run`) head-normalises `handle_State` at run-entry and
# kernel-evals per Impure node.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.desc-interp.kernel;

  # `modify`'s `fn:S→S` is an ordinary data field (function-typed value),
  # not a `piField` — no extra Π-binder over downstream positions.
  EffState =
    H.datatypeP "EffState" [{ name = "S"; kind = H.u 0; }] (ps:
      let S = builtins.elemAt ps 0; in [
        (H.con "get" [ ])
        (H.con "put" [ (H.field "param" S) ])
        (H.con "modify" [ (H.field "fn" (H.forall "_" S (_: S))) ])
      ]);

  EffStateTy = H.forall "S" (H.u 0) (_S: H.u 0);

  getAt = S: H.implicitApp EffState.get S;
  putPrefixAt = S: H.implicitApp EffState.put S;
  putAt = S: param: H.app (putPrefixAt S) param;
  modifyPrefixAt = S: H.implicitApp EffState.modify S;
  modifyAt = S: fn: H.app (modifyPrefixAt S) fn;
  elimAt = k: S: H.implicitApp (EffState.elim k) S;

  Resp_StateTy =
    H.forall "S" (H.u 0) (S:
      H.forall "_op" (H.app EffState.T S) (_op: H.u 0));

  # `get → S`, `put → Unit`, `modify → Unit`. Iota fires at each known
  # constructor, so e.g. `Resp_State S (get S) ≡ S` by conv.
  # `H.ann`-wrapped so kernel inference can recover the type at use sites.
  Resp_State = H.ann
    (H.lam "S" (H.u 0) (S:
      let Es = H.app EffState.T S; in
      H.lam "op" Es (op:
        H.app
          (H.app
            (H.app
              (H.app
                (H.app
                  (elimAt 1 S)
                  (H.lam "_op" Es (_op: H.u 0)))
                S)
              (H.lam "_param" S (_p: H.unit)))
            (H.lam "_fn" (H.forall "_" S (_: S)) (_f: H.unit)))
          op)))
    Resp_StateTy;

  handle_StateTy =
    H.forall "S" (H.u 0) (S:
      H.forall "A" (H.u 0) (A:
        H.forall "op" (H.app EffState.T S) (op:
          H.forall "_s" S (_s:
            H.sum
              (H.sigma "_r" (H.app (H.app Resp_State S) op) (_r: S))
              (H.sigma "_a" A (_a: S))))));

  # Left summand = resume (response + new state); right = abort (return
  # value + new state). State never aborts → all three cases are `inl`.
  handle_State = H.ann
    (H.lam "S" (H.u 0) (S:
      H.lam "A" (H.u 0) (A:
        let
          Es = H.app EffState.T S;
          respFor = op: H.app (H.app Resp_State S) op;
          leftFor = op: H.sigma "_r" (respFor op) (_r: S);
          right = H.sigma "_a" A (_a: S);
          motive = H.lam "op" Es (op:
            H.forall "_s" S (_s:
              H.sum (leftFor op) right));
          # resume with `_s`, state unchanged.
          onGet =
            H.lam "_s" S (_s:
              HI.inlAtExplicit H.levelZero (leftFor (getAt S)) right
                (H.pair _s _s));
          # resume with `tt`, state := `param`.
          onPut =
            H.lam "_param" S (_param:
              H.lam "_s" S (_s:
                HI.inlAtExplicit H.levelZero (leftFor (putAt S _param)) right
                  (H.pair H.tt _param)));
          # resume with `tt`, state := `fn _s`.
          onModify =
            H.lam "_fn" (H.forall "_" S (_: S)) (_fn:
              H.lam "_s" S (_s:
                HI.inlAtExplicit H.levelZero (leftFor (modifyAt S _fn)) right
                  (H.pair H.tt (H.app _fn _s))));
        in
        H.lam "op" Es (op:
          H.app
            (H.app
              (H.app
                (H.app
                  (H.app
                    (elimAt 0 S)
                    motive)
                  onGet)
                onPut)
              onModify)
            op))))
    handle_StateTy;

  # Monomorphises `(EffState, Resp_State)` at `(S, A)` and ships the
  # `{ eff; resp; get; put; modify; handler; dispatch }` record. `handler`
  # is the kernel term fully type-applied to `(S, A)`, ready for
  # `(op, state)`. `dispatch` is the Nix-side interpreter that reads
  # the kernel-eval'd Sum result and emits a `{ action; newState; … }`
  # step decision for the trampoline.
  #
  # `outputVal` shape — `Sum (Σ (Resp_State op) S) (Σ A S)` encodes as
  # `VDescCon{VBootInl|VBootInr, VPair(VPair(payload, state), VTt)}`:
  # `.fst` is the Σ pair (resp or A, paired with new state), `.snd` is
  # `VTt` (single-field constructor padding). State always resumes;
  # the inr arm exists only to make the Sum total.
  atType = S: A:
    let
      eff = H.app EffState.T S;
      resp = H.app Resp_State S;
      handler = H.app (H.app handle_State S) A;
      send_ = K.send eff resp;
      dispatch = ctx:
        let
          outputVal = ctx.outputVal;
          side = outputVal.d.tag;
          pair = outputVal.d.val.fst;
        in
        if side == "VBootInl" then {
          action = "resume";
          response = pair.fst;
          newState = pair.snd;
        }
        else if side == "VBootInr" then {
          action = "abort";
          value = pair.fst;
          newState = pair.snd;
        }
        else throw "experimental.descInterp.effects.state.dispatch: expected VBootInl/VBootInr at outputVal.d.tag, got '${side}'";

      # Shared op skeletons + prefix Vals. Let-bound once per `atType S A`
      # so smart constructors below see the same Nix references on every
      # call — `_opTag` keys the bridge's `evalOp` cache in O(1).
      getOp = getAt S;
      putPrefix = putPrefixAt S;
      modifyPrefix = modifyPrefixAt S;
      getOpVal = fx.tc.eval.eval [ ] (H.elab getOp);
      putPrefixVal = fx.tc.eval.eval [ ] (H.elab putPrefix);
      modifyPrefixVal = fx.tc.eval.eval [ ] (H.elab modifyPrefix);

      # `evalOp op → Val`: tag-keyed O(1) replacement for the trampoline's
      # default `eval [] (H.elab op)`. For `state-get` the entire op Val is
      # cached; for `state-put` / `state-modify` only the constructor
      # prefix is cached and `vApp prefixVal (eval arg)` skips the prefix
      # eval per Impure node. Fall-through (untagged ops, or unknown tag)
      # uses the generic eval path.
      evalOp = op:
        let t = op._opTag or null; in
        if t == "state-get" then getOpVal
        else if t == "state-put"
        then
          fx.tc.eval.vApp putPrefixVal
            (fx.tc.eval.eval [ ] (H.elab op.arg))
        else if t == "state-modify"
        then
          fx.tc.eval.vApp modifyPrefixVal
            (fx.tc.eval.eval [ ] (H.elab op.arg))
        else fx.tc.eval.eval [ ] (H.elab op);

      # Shortcut path — partial-evaluation residual for `handle_State`
      # at each canonical op. Soundness chain: `state-shortcut-laws.nix`
      # certifies `handle_State S A op s ≡_kernel mkResumeAt … r s` by
      # H.refl; `extract.nix` certifies `eval (mkResumeAt …) ≡_Val
      # extract.Resume`. The trampoline branches on a non-null
      # `handlerShortcut` Val before falling back to the kernel handler.
      #
      # Per-canonical-op metadata Vals are precomputed once per
      # `atType S A`. `get`'s leftSig differs from `put`/`modify`'s
      # because `Resp_State S (get S) ≡ S` whereas `Resp_State S
      # (put S _) ≡ Unit ≡ Resp_State S (modify S _)`.
      Extract = fx.experimental.desc-interp.extract;
      rightSigHoas = H.sigma "_a" A (_: S);
      rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
      getLeftSigHoas = H.sigma "_r" S (_: S);
      getLeftSigVal = fx.tc.eval.eval [ ] (H.elab getLeftSigHoas);
      getSumDescVal = Extract.sumDescValOf getLeftSigHoas rightSigHoas;
      unitLeftSigHoas = H.sigma "_r" H.unit (_: S);
      unitLeftSigVal = fx.tc.eval.eval [ ] (H.elab unitLeftSigHoas);
      unitSumDescVal = Extract.sumDescValOf unitLeftSigHoas rightSigHoas;
      ttVal = fx.tc.eval.eval [ ] (H.elab H.tt);

      handlerShortcut = op: stateVal:
        let t = op._opTag or null; in
        if t == "state-get" then
          Extract.extract
            (Extract.Resume
              getSumDescVal
              getLeftSigVal
              rightSigVal
              stateVal
              stateVal)
        else if t == "state-put" then
          let paramVal = fx.tc.eval.eval [ ] (H.elab op.arg); in
          Extract.extract (Extract.Resume
            unitSumDescVal
            unitLeftSigVal
            rightSigVal
            ttVal
            paramVal)
        else if t == "state-modify" then
          let
            fnVal = fx.tc.eval.eval [ ] (H.elab op.arg);
            newStateVal = fx.tc.eval.vApp fnVal stateVal;
          in
          Extract.extract (Extract.Resume
            unitSumDescVal
            unitLeftSigVal
            rightSigVal
            ttVal
            newStateVal)
        else null;
    in
    {
      inherit eff resp handler dispatch evalOp handlerShortcut;
      get = send_ (getOp // { _opTag = "state-get"; });
      put = s: send_ ((putAt S s) // { _opTag = "state-put"; });
      modify = fn: send_ ((modifyAt S fn) // { _opTag = "state-modify"; });
    };

in
{
  scope = {
    state = api.namespace {
      description = "state effect over descInterp's FreeFx kernel — EffState kernel datatype + kernel-term handle_State; smart constructors + `{ handler; dispatch }` bridge record via `atType S A` factory.";
      doc = ''
        Pair with `experimental.desc-interp.trampoline.run`:

        ```nix
        let st = state.atType H.nat H.nat;
        in run st.eff st.resp H.nat
             { inherit (st) handler dispatch; }
             program initialState
        ```
      '';

      value = {
        EffState = api.leaf {
          value = EffState;
          description = "EffState : Π(S:U₀). U₀ — kernel datatype with three constructors (`get`, `put(param:S)`, `modify(fn:S→S)`). Built via `H.datatypeP`; macro-derived `.T`, `.D`, `.elim`, and per-constructor introducers.";
          tests = {
            "EffState-D-is-datatype-desc" = {
              expr = (fx.tc.eval.eval [ ] (H.elab (H.app EffState.D H.nat)))._descRef.kind;
              expected = "datatype-desc";
            };
            "EffState-get-at-nat-checks" = {
              expr = !((H.checkHoas (H.app EffState.T H.nat) (getAt H.nat)) ? error);
              expected = true;
            };
            "EffState-put-at-nat-checks" = {
              expr = !((H.checkHoas
                (H.app EffState.T H.nat)
                (putAt H.nat H.zero))
              ? error);
              expected = true;
            };
            "EffState-put-prefix-evals-to-function" = {
              expr = (fx.tc.eval.eval [ ] (H.elab (putPrefixAt H.nat))).tag;
              expected = "VLam";
            };
          };
        };
        Resp_State = api.leaf {
          value = Resp_State;
          description = "Resp_State S op: response type family for state operations; get returns S, put/modify return Unit.";
        };
        handle_State = api.leaf {
          value = handle_State;
          description = "handle_State S A op s: kernel-resident state handler returning UniRet left/resume results for get, put, and modify.";
        };
        EffStateTy = api.leaf {
          value = EffStateTy;
          description = "Π-type of state's op-identity family: `Π(S:U₀). U₀`.";
          tests = {
            "EffStateTy-well-formed" = {
              expr = !((H.inferHoas EffStateTy) ? error);
              expected = true;
            };
            "EffState-T-checks-against-EffStateTy" = {
              expr = !((H.checkHoas EffStateTy EffState.T) ? error);
              expected = true;
            };
          };
        };

        Resp_StateTy = api.leaf {
          value = Resp_StateTy;
          description = "Π-type of state's per-op response family: `Π(S:U₀). Π(_op:EffState S). U₀`.";
          tests = {
            "Resp_StateTy-well-formed" = {
              expr = !((H.inferHoas Resp_StateTy) ? error);
              expected = true;
            };
            "Resp_State-checks-against-Resp_StateTy" = {
              expr = !((H.checkHoas Resp_StateTy Resp_State) ? error);
              expected = true;
            };
          };
        };

        handle_StateTy = api.leaf {
          value = handle_StateTy;
          description = "Π-type of the state handler: `Π(S A:U₀). Π(op:EffState S). Π(_s:S). Sum (Σ _r:Resp_State[S,op], S) (Σ _a:A, S)`. Always returns the left (resume) summand — state effects never abort.";
          tests = {
            "handle_StateTy-well-formed" = {
              expr = !((H.inferHoas handle_StateTy) ? error);
              expected = true;
            };
            "handle_State-checks-against-handle_StateTy" = {
              expr = !((H.checkHoas handle_StateTy handle_State) ? error);
              expected = true;
            };
          };
        };

        atType = api.leaf {
          value = atType;
          description = "`atType S A` — per-`(S, A)` monomorphisation of `(EffState, Resp_State)` shipping `send`-wrapped smart constructors `get`/`put`/`modify`, the kernel-resident `handler` (= `handle_State` applied to `S` and `A`), and the Nix-side `dispatch` interpreter that reads the kernel-eval'd Sum return value into a `{ action; newState; response?; value?; }` step decision for the trampoline.";
          tests = {
            "atType-nat-nat-get-is-desc-con" = {
              expr = (atType H.nat H.nat).get._htag;
              expected = "desc-con";
            };
            "atType-nat-nat-put-zero-is-desc-con" = {
              expr = ((atType H.nat H.nat).put H.zero)._htag;
              expected = "desc-con";
            };
            "atType-nat-nat-handler-is-app" = {
              expr = (atType H.nat H.nat).handler._htag;
              expected = "app";
            };
            "atType-nat-nat-evalOp-put-zero-is-desc-con" = {
              expr =
                let
                  st = atType H.nat H.nat;
                  op = (putAt H.nat H.zero) // { _opTag = "state-put"; };
                in
                (st.evalOp op).tag;
              expected = "VDescCon";
            };
            "atType-nat-nat-kernel-handler-accepts-put-evalOp" = {
              expr =
                let
                  st = atType H.nat H.nat;
                  op = (putAt H.nat H.zero) // { _opTag = "state-put"; };
                  handlerCore = fx.tc.eval.eval [ ] (H.elab st.handler);
                  stateVal = fx.tc.eval.eval [ ] (H.elab H.zero);
                  outputVal = fx.tc.eval.vApp
                    (fx.tc.eval.vApp handlerCore (st.evalOp op))
                    stateVal;
                in
                outputVal.d.tag;
              expected = "VBootInl";
            };
          };
        };
        getAt = api.leaf {
          value = getAt;
          description = "getAt S — EffState.get with hidden state type supplied.";
        };
        putPrefixAt = api.leaf {
          value = putPrefixAt;
          description = "putPrefixAt S — EffState.put with hidden state type supplied, leaving the explicit state parameter.";
        };
        putAt = api.leaf {
          value = putAt;
          description = "putAt S param — EffState.put with hidden state type and explicit state parameter supplied.";
        };
        modifyPrefixAt = api.leaf {
          value = modifyPrefixAt;
          description = "modifyPrefixAt S — EffState.modify with hidden state type supplied, leaving the explicit function parameter.";
        };
        modifyAt = api.leaf {
          value = modifyAt;
          description = "modifyAt S fn — EffState.modify with hidden state type and explicit function parameter supplied.";
        };
        elimAt = api.leaf {
          value = elimAt;
          description = "elimAt k S — EffState.elim k with hidden state type supplied.";
        };
      };
    };
  };
}
