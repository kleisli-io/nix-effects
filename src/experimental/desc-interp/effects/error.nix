# Error effect over `experimental.desc-interp.kernel.send`. Kernel-resident
# `EffError : Π(E:U). U` with one constructor carrying a polymorphic payload.
# Three handler strategies, each with its own return shape:
#
#   handle_strict     : Π(E State:U).            Π(op). Π(_s). Σ State E
#   handle_collecting : Π(E:U).                  Π(op). Π(_s:List E). Σ (List E) Unit
#   handle_result     : Π(E State A_inner:U).    Π(op). Π(_s). Σ State (Sum E A_inner)
#
# Each `atType_*` factory ships `{ eff; resp; raise; handler; dispatch }`.
# `dispatch` is the Nix-side interpreter that reads the kernel-eval'd
# handler output and produces a `{ action; … }` step decision for the
# trampoline.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.desc-interp.kernel;

  # `payload : E` is consumer-chosen — `H.string` for message-only errors,
  # a record schema for structured `{msg; ctx;}`, etc.
  EffError =
    H.datatypeP "EffError" [{ name = "E"; kind = H.u 0; }] (ps:
      let E = builtins.elemAt ps 0; in [
        (H.con "error" [ (H.field "payload" E) ])
      ]);

  EffErrorTy = H.forall "E" (H.u 0) (_E: H.u 0);

  # Per-strategy response families. All three share the same Π-type;
  # only the body (`Void` vs `Unit`) differs.
  Resp_strictTy =
    H.forall "E" (H.u 0) (E:
      H.forall "_op" (H.app EffError.T E) (_op: H.u 0));
  Resp_collectingTy = Resp_strictTy;
  Resp_resultTy = Resp_strictTy;

  # `error → Void`. `elim 1` because the motive's result `U 0` lives at `U 1`.
  Resp_strict = H.ann
    (H.lam "E" (H.u 0) (E:
      let Ee = H.app EffError.T E; in
      H.lam "op" Ee (op:
        H.app
          (H.app
            (H.app
              (H.app
                (EffError.elim 1)
                E)
              (H.lam "_op" Ee (_op: H.u 0)))
            (H.lam "_payload" E (_p: H.void)))
          op)))
    Resp_strictTy;

  # `error → Unit`.
  Resp_collecting = H.ann
    (H.lam "E" (H.u 0) (E:
      let Ee = H.app EffError.T E; in
      H.lam "op" Ee (op:
        H.app
          (H.app
            (H.app
              (H.app
                (EffError.elim 1)
                E)
              (H.lam "_op" Ee (_op: H.u 0)))
            (H.lam "_payload" E (_p: H.unit)))
          op)))
    Resp_collectingTy;

  # Same body as `Resp_strict` (both non-resumable); bound separately
  # so consumers select by strategy name.
  Resp_result = H.ann
    (H.lam "E" (H.u 0) (E:
      let Ee = H.app EffError.T E; in
      H.lam "op" Ee (op:
        H.app
          (H.app
            (H.app
              (H.app
                (EffError.elim 1)
                E)
              (H.lam "_op" Ee (_op: H.u 0)))
            (H.lam "_payload" E (_p: H.void)))
          op)))
    Resp_resultTy;

  # Strict: returns `Σ State E`. Payload is the surrender value;
  # no Sum because strict never resumes. Dispatch action = `"throw"`.
  handle_strictTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "op" (H.app EffError.T E) (op:
          H.forall "_s" State (_s:
            H.sigma "_state" State (_st: E)))));

  handle_strict = H.ann
    (H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        let
          Ee = H.app EffError.T E;
          motive = H.lam "_op" Ee (_op:
            H.forall "_s" State (_s:
              H.sigma "_state" State (_st: E)));
          onError = H.lam "_payload" E (payload:
            H.lam "_s" State (_s:
              H.pair _s payload));
        in
        H.lam "op" Ee (op:
          H.app
            (H.app
              (H.app
                (H.app
                  (EffError.elim 0)
                  E)
                motive)
              onError)
            op))))
    handle_strictTy;

  # Collecting: returns `Σ (List E) Unit`. State specialised to `List E`;
  # resume cons-es the payload onto the handler state.
  handle_collectingTy =
    H.forall "E" (H.u 0) (E:
      H.forall "op" (H.app EffError.T E) (op:
        H.forall "_s" (H.listOf E) (_s:
          H.sigma "_state" (H.listOf E) (_st: H.unit))));

  handle_collecting = H.ann
    (H.lam "E" (H.u 0) (E:
      let
        Ee = H.app EffError.T E;
        State = H.listOf E;
        motive = H.lam "_op" Ee (_op:
          H.forall "_s" State (_s:
            H.sigma "_state" State (_st: H.unit)));
        onError = H.lam "_payload" E (payload:
          H.lam "_s" State (_s:
            H.pair (HI.consAtExplicit E payload _s) H.tt));
      in
      H.lam "op" Ee (op:
        H.app
          (H.app
            (H.app
              (H.app
                (EffError.elim 0)
                E)
              motive)
            onError)
          op)))
    handle_collectingTy;

  # Result: returns `Σ State (Sum E A_inner)`. Sum lives in the result slot;
  # handler always returns `inl payload`. Dispatch action = `"abort"`.
  handle_resultTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "A_inner" (H.u 0) (A_inner:
          H.forall "op" (H.app EffError.T E) (op:
            H.forall "_s" State (_s:
              H.sigma "_state" State (_st: H.sum E A_inner))))));

  handle_result = H.ann
    (H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        H.lam "A_inner" (H.u 0) (A_inner:
          let
            Ee = H.app EffError.T E;
            motive = H.lam "_op" Ee (_op:
              H.forall "_s" State (_s:
                H.sigma "_state" State (_st: H.sum E A_inner)));
            onError = H.lam "_payload" E (payload:
              H.lam "_s" State (_s:
                H.pair _s (HI.inlAtExplicit H.levelZero E A_inner payload)));
          in
          H.lam "op" Ee (op:
            H.app
              (H.app
                (H.app
                  (H.app
                    (EffError.elim 0)
                    E)
                  motive)
                onError)
              op)))))
    handle_resultTy;

  # UniRet-shaped adapters wrapping each strategy's handler. Reverse
  # dependency on `compose.{uniRetAt, mkResume, mkAbort}` is lazy (the
  # lookups are inside type-signature and lambda bodies).
  C = fx.experimental.desc-interp.compose;

  # strict: always aborts; A := E carries the surrender value.
  uniformOf_strictTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "op" (H.app EffError.T E) (op:
          H.forall "_s" State (_s:
            C.uniRetAt State (H.app EffError.T E) (H.app Resp_strict E) op E))));

  # Direct `EffError.elim 0` dispatch — universal-property presentation.
  # The factorization `mkAbort ∘ ⟨snd, fst⟩ ∘ handle_strict` is an
  # emergent theorem about this map, not its definition. Defining via
  # the eliminator makes the per-canonical-op behavior conv-trivial:
  # one ι (selecting `error`) + two β (payload, _s) at any canonical op.
  uniformOf_strict = H.ann
    (H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        let
          Ee = H.app EffError.T E;
          Resp = H.app Resp_strict E;
          motive = H.lam "_op" Ee (_op:
            H.forall "_s" State (_s:
              C.uniRetAt State Ee Resp _op E));
          onError = H.lam "_payload" E (payload:
            H.lam "_s" State (_s:
              H.app
                (H.app
                  (H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            C.mkAbort
                            State)
                          Ee)
                        Resp)
                      (H.app (H.app EffError.error E) payload))
                    E)
                  payload)
                _s));
        in
        H.lam "op" Ee (op:
          H.app
            (H.app
              (H.app
                (H.app
                  (EffError.elim 0)
                  E)
                motive)
              onError)
            op))))
    uniformOf_strictTy;

  # collecting: always resumes with tt; must dispatch via EffError.elim
  # because mkResume's r-arg type `Resp_collecting E op` is stuck at
  # universal op and only conv-reduces to `Unit` in each constructor
  # branch.
  uniformOf_collectingTy =
    H.forall "E" (H.u 0) (E:
      H.forall "A" (H.u 0) (A:
        H.forall "op" (H.app EffError.T E) (op:
          H.forall "_s" (H.listOf E) (_s:
            C.uniRetAt (H.listOf E) (H.app EffError.T E) (H.app Resp_collecting E) op A))));

  uniformOf_collecting = H.ann
    (H.lam "E" (H.u 0) (E:
      H.lam "A" (H.u 0) (A:
        let
          Ee = H.app EffError.T E;
          State = H.listOf E;
          Resp = H.app Resp_collecting E;
          motive = H.lam "_op" Ee (_op:
            H.forall "_s" State (_s:
              C.uniRetAt State Ee Resp _op A));
          onError = H.lam "_payload" E (payload:
            H.lam "_s" State (_s:
              H.app
                (H.app
                  (H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            C.mkResume
                            State)
                          Ee)
                        Resp)
                      (H.app (H.app EffError.error E) payload))
                    A)
                  H.tt)
                (HI.consAtExplicit E payload _s)));
        in
        H.lam "op" Ee (op:
          H.app
            (H.app
              (H.app
                (H.app
                  (EffError.elim 0)
                  E)
                motive)
              onError)
            op))))
    uniformOf_collectingTy;

  # result: always aborts; A := Sum E A_inner carries the typed result
  # channel. handle_result's snd already IS the Sum E A_inner value.
  uniformOf_resultTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "A_inner" (H.u 0) (A_inner:
          H.forall "op" (H.app EffError.T E) (op:
            H.forall "_s" State (_s:
              C.uniRetAt State (H.app EffError.T E) (H.app Resp_result E) op
                (H.sum E A_inner))))));

  # Direct `EffError.elim 0` dispatch — symmetric with `uniformOf_strict`.
  # The Sum E A_inner channel always carries the inl-injected payload
  # (handler never produces inr); kernel sees this directly at each
  # canonical op via one ι + two β.
  uniformOf_result = H.ann
    (H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        H.lam "A_inner" (H.u 0) (A_inner:
          let
            Ee = H.app EffError.T E;
            Resp = H.app Resp_result E;
            A = H.sum E A_inner;
            motive = H.lam "_op" Ee (_op:
              H.forall "_s" State (_s:
                C.uniRetAt State Ee Resp _op A));
            onError = H.lam "_payload" E (payload:
              H.lam "_s" State (_s:
                H.app
                  (H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              C.mkAbort
                              State)
                            Ee)
                          Resp)
                        (H.app (H.app EffError.error E) payload))
                      A)
                    (HI.inlAtExplicit H.levelZero E A_inner payload))
                  _s));
          in
          H.lam "op" Ee (op:
            H.app
              (H.app
                (H.app
                  (H.app
                    (EffError.elim 0)
                    E)
                  motive)
                onError)
              op)))))
    uniformOf_resultTy;

  # `atType_*` factories surface `{ eff; resp; raise; handler; dispatch }`.
  # `handler` is the polymorphic kernel term pre-applied to type params;
  # `dispatch` reads the kernel-eval'd output and returns a step decision.

  # Shared raise-prefix Val builder. EffError has a single constructor
  # (`error`); the per-strategy atType factories below only differ in
  # the handler/dispatch return shape, not in op construction — so the
  # `_opTag = "error-raise"` tag and `errorPrefixVal` are uniform across
  # strategies. Each factory specialises `errorPrefix` at its own `E`.
  mkRaiseEvalOp = E:
    let
      errorPrefix = H.app EffError.error E;
      errorPrefixVal = fx.tc.eval.eval [ ] (H.elab errorPrefix);
    in
    {
      inherit errorPrefix;
      raiseAtE = e: H.app errorPrefix e;
      evalOp = op:
        if (op._opTag or null) == "error-raise"
        then
          fx.tc.eval.vApp errorPrefixVal
            (fx.tc.eval.eval [ ] (H.elab op.arg))
        else fx.tc.eval.eval [ ] (H.elab op);
    };

  atType_strict = E: State:
    let
      eff = H.app EffError.T E;
      resp = H.app Resp_strict E;
      handler = H.app (H.app handle_strict E) State;
      send_ = K.send eff resp;
      raiseHlp = mkRaiseEvalOp E;
      raise = e: send_ ((raiseHlp.raiseAtE e) // { _opTag = "error-raise"; });
      # outputVal : Σ State E.
      dispatch = ctx:
        let outputVal = ctx.outputVal; in {
          action = "throw";
          newState = outputVal.fst or null;
          error = outputVal.snd or null;
        };
      # Shortcut path — strict's onError branch reduces to `H.pair _s payload`
      # by ι on EffError.elim + β. Soundness chain: `strictRaiseLemma`
      # (kernel H.refl) + emitter `PairRaw` conv test.
      Extract = fx.experimental.desc-interp.extract;
      handlerShortcut = op: stateVal:
        if (op._opTag or null) == "error-raise" then
          let payloadVal = fx.tc.eval.eval [ ] (H.elab op.arg); in
          Extract.extract (Extract.PairRaw stateVal payloadVal)
        else null;
      # UniRet-shaped lift mirroring kernel-side `uniformOf_strict` (A := E;
      # surrender payload rides the abort channel). leftSig uses the reduced
      # `Resp_strict E op ≡ Void` form.
      uniformLeftSigHoas = H.sigma "_r" H.void (_: State);
      uniformLeftSigVal = fx.tc.eval.eval [ ] (H.elab uniformLeftSigHoas);
      uniformRightSigHoas = H.sigma "_a" E (_: State);
      uniformRightSigVal = fx.tc.eval.eval [ ] (H.elab uniformRightSigHoas);
      uniformSumDescVal = Extract.sumDescValOf uniformLeftSigHoas uniformRightSigHoas;
      uniformOfShort = op: stateVal:
        let bareOut = handlerShortcut op stateVal; in
        if bareOut == null then null
        else
          Extract.extract (Extract.Abort
            uniformSumDescVal
            uniformLeftSigVal
            uniformRightSigVal
            bareOut.snd
            bareOut.fst);
    in
    {
      inherit eff resp raise handler dispatch handlerShortcut uniformOfShort;
      inherit (raiseHlp) evalOp;
    };

  atType_collecting = E:
    let
      State = H.listOf E;
      eff = H.app EffError.T E;
      resp = H.app Resp_collecting E;
      handler = H.app handle_collecting E;
      send_ = K.send eff resp;
      raiseHlp = mkRaiseEvalOp E;
      raise = e: send_ ((raiseHlp.raiseAtE e) // { _opTag = "error-raise"; });
      # outputVal : Σ (List E) Unit.
      dispatch = ctx:
        let outputVal = ctx.outputVal; in {
          action = "resume";
          newState = outputVal.fst or null;
          response = outputVal.snd or null;
        };
      # Shortcut path — collecting's onError reduces to
      # `H.pair (H.cons E payload _s) H.tt`. The cons spine is bound
      # once per `atType` as a curried Val closure; `vApp`s at runtime
      # skip elab+eval of the cons each Impure step. Soundness chain:
      # `collectingRaiseLemma` (kernel H.refl) + emitter `PairRaw`
      # conv test.
      Extract = fx.experimental.desc-interp.extract;
      consClosure = fx.tc.eval.eval [ ] (H.elab
        (H.lam "p" E (p:
          H.lam "t" State (t:
            HI.consAtExplicit E p t))));
      ttVal = fx.tc.eval.eval [ ] (H.elab H.tt);
      handlerShortcut = op: stateVal:
        if (op._opTag or null) == "error-raise" then
          let
            payloadVal = fx.tc.eval.eval [ ] (H.elab op.arg);
            newListVal = fx.tc.eval.vApp
              (fx.tc.eval.vApp consClosure payloadVal)
              stateVal;
          in
          Extract.extract (Extract.PairRaw newListVal ttVal)
        else null;
      # UniRet-shaped lift mirroring kernel-side `uniformOf_collecting`
      # (always resumes with `tt`; new state is the cons-list). `A` is the
      # program-return type — caller-supplied at compose-time, so this
      # exposes `uniformOfShortAt = A: …` rather than a fully-bound function.
      # leftSig uses the reduced `Resp_collecting E op ≡ Unit` form.
      uniformLeftSigHoas = H.sigma "_r" H.unit (_: State);
      uniformLeftSigVal = fx.tc.eval.eval [ ] (H.elab uniformLeftSigHoas);
      uniformOfShortAt = A:
        let
          uniformRightSigHoas = H.sigma "_a" A (_: State);
          uniformRightSigVal = fx.tc.eval.eval [ ] (H.elab uniformRightSigHoas);
          uniformSumDescVal = Extract.sumDescValOf uniformLeftSigHoas uniformRightSigHoas;
        in
        op: stateVal:
          let bareOut = handlerShortcut op stateVal; in
          if bareOut == null then null
          else
            Extract.extract (Extract.Resume
              uniformSumDescVal
              uniformLeftSigVal
              uniformRightSigVal
              bareOut.snd
              bareOut.fst);
    in
    {
      inherit State eff resp raise handler dispatch handlerShortcut uniformOfShortAt;
      inherit (raiseHlp) evalOp;
    };

  atType_result = E: State: A_inner:
    let
      eff = H.app EffError.T E;
      resp = H.app Resp_result E;
      handler = H.app (H.app (H.app handle_result E) State) A_inner;
      send_ = K.send eff resp;
      raiseHlp = mkRaiseEvalOp E;
      raise = e: send_ ((raiseHlp.raiseAtE e) // { _opTag = "error-raise"; });
      # outputVal : Σ State (Sum E A_inner).
      dispatch = ctx:
        let outputVal = ctx.outputVal; in {
          action = "abort";
          newState = outputVal.fst or null;
          value = outputVal.snd or null;
        };
      # Shortcut path — result's onError reduces to
      # `H.pair _s (H.inl E A_inner payload)`. The inl spine is bound
      # once per `atType` as a unary Val closure; one `vApp` at runtime
      # skips elab+eval of the inl per Impure step. Soundness chain:
      # `resultRaiseLemma` (kernel H.refl) + emitter `PairRaw` conv test.
      Extract = fx.experimental.desc-interp.extract;
      innerInlClosure = fx.tc.eval.eval [ ] (H.elab
        (H.lam "p" E (p: HI.inlAtExplicit H.levelZero E A_inner p)));
      handlerShortcut = op: stateVal:
        if (op._opTag or null) == "error-raise" then
          let
            payloadVal = fx.tc.eval.eval [ ] (H.elab op.arg);
            innerVal = fx.tc.eval.vApp innerInlClosure payloadVal;
          in
          Extract.extract (Extract.PairRaw stateVal innerVal)
        else null;
      # UniRet-shaped lift mirroring kernel-side `uniformOf_result`
      # (A := Sum E A_inner; the typed result channel rides the abort
      # summand). leftSig uses the reduced `Resp_result E op ≡ Void` form.
      uniformLeftSigHoas = H.sigma "_r" H.void (_: State);
      uniformLeftSigVal = fx.tc.eval.eval [ ] (H.elab uniformLeftSigHoas);
      uniformRightSigHoas = H.sigma "_a" (H.sum E A_inner) (_: State);
      uniformRightSigVal = fx.tc.eval.eval [ ] (H.elab uniformRightSigHoas);
      uniformSumDescVal = Extract.sumDescValOf uniformLeftSigHoas uniformRightSigHoas;
      uniformOfShort = op: stateVal:
        let bareOut = handlerShortcut op stateVal; in
        if bareOut == null then null
        else
          Extract.extract (Extract.Abort
            uniformSumDescVal
            uniformLeftSigVal
            uniformRightSigVal
            bareOut.snd
            bareOut.fst);
    in
    {
      inherit eff resp raise handler dispatch handlerShortcut uniformOfShort;
      inherit (raiseHlp) evalOp;
    };

in
{
  scope = {
    error = api.namespace {
      description = "error effect over descInterp's FreeFx kernel — EffError datatype + three kernel-term handlers (strict/collecting/result) with paired dispatch interpreters.";
      doc = ''
        Pair with `experimental.desc-interp.trampoline.run`:

        ```nix
        let er = error.atType_strict H.string H.nat;
        in run er.eff er.resp H.nat returnTy
             { handler = er.handler; dispatch = er.dispatch; }
             program initialState
        ```

        Strategies differ in handler return shape and dispatch action:

          strict     : Σ State E              → action="throw"
          collecting : Σ (List E) Unit        → action="resume", response=tt
          result     : Σ State (Sum E A_inner)→ action="abort"
      '';

      value = {
        EffError = api.leaf {
          value = EffError;
          description = "EffError : Π(E:U₀). U₀ — kernel datatype with one constructor `error(payload:E)`. Built via `H.datatypeP`; macro-derived `.T`, `.D`, `.elim`, and the `error` introducer.";
          tests = {
            "EffError-D-is-datatype-desc" = {
              expr = (fx.tc.eval.eval [ ] (H.elab (H.app EffError.D H.string)))._descRef.kind;
              expected = "datatype-desc";
            };
            "EffError-error-at-string-checks" = {
              expr = !((H.checkHoas
                (H.app EffError.T H.string)
                (H.app (H.app EffError.error H.string) (H.stringLit "boom")))
              ? error);
              expected = true;
            };
          };
        };
        Resp_strict = api.leaf { value = Resp_strict; description = "Strict error response family; every error op has Void response because strict errors never resume."; };
        Resp_collecting = api.leaf { value = Resp_collecting; description = "Collecting error response family; errors resume with Unit while accumulating payloads in state."; };
        Resp_result = api.leaf { value = Resp_result; description = "Result-channel error response family; errors abort into Sum E A_inner."; };
        handle_strict = api.leaf { value = handle_strict; description = "Kernel strict error handler; maps raise to throw-shaped Σ State E."; };
        handle_collecting = api.leaf { value = handle_collecting; description = "Kernel collecting error handler; conses payloads into List E state and resumes with Unit."; };
        handle_result = api.leaf { value = handle_result; description = "Kernel result error handler; aborts with Sum E A_inner while preserving state."; };

        EffErrorTy = api.leaf {
          value = EffErrorTy;
          description = "Π-type of error's op-identity family: `Π(E:U₀). U₀`.";
          tests = {
            "EffErrorTy-well-formed" = {
              expr = !((H.inferHoas EffErrorTy) ? error);
              expected = true;
            };
            "EffError-T-checks-against-EffErrorTy" = {
              expr = !((H.checkHoas EffErrorTy EffError.T) ? error);
              expected = true;
            };
          };
        };

        Resp_strictTy = api.leaf {
          value = Resp_strictTy;
          description = "Π-type of strict-error's response family: `Π(E:U₀). Π(_op:EffError E). U₀`. Body returns `Void` at every op — strict never resumes.";
          tests = {
            "Resp_strictTy-well-formed" = {
              expr = !((H.inferHoas Resp_strictTy) ? error);
              expected = true;
            };
            "Resp_strict-checks-against-Resp_strictTy" = {
              expr = !((H.checkHoas Resp_strictTy Resp_strict) ? error);
              expected = true;
            };
          };
        };

        Resp_collectingTy = api.leaf {
          value = Resp_collectingTy;
          description = "Π-type of collecting-error's response family: `Π(E:U₀). Π(_op:EffError E). U₀`. Body returns `Unit` — collecting always resumes with `tt`.";
          tests = {
            "Resp_collectingTy-well-formed" = {
              expr = !((H.inferHoas Resp_collectingTy) ? error);
              expected = true;
            };
            "Resp_collecting-checks-against-Resp_collectingTy" = {
              expr = !((H.checkHoas Resp_collectingTy Resp_collecting) ? error);
              expected = true;
            };
          };
        };

        Resp_resultTy = api.leaf {
          value = Resp_resultTy;
          description = "Π-type of result-error's response family: `Π(E:U₀). Π(_op:EffError E). U₀`. Body returns `Void` — result never resumes (abort lives in the program's typed result channel).";
          tests = {
            "Resp_resultTy-well-formed" = {
              expr = !((H.inferHoas Resp_resultTy) ? error);
              expected = true;
            };
            "Resp_result-checks-against-Resp_resultTy" = {
              expr = !((H.checkHoas Resp_resultTy Resp_result) ? error);
              expected = true;
            };
          };
        };

        handle_strictTy = api.leaf {
          value = handle_strictTy;
          description = "Π-type of the strict error handler: `Π(E State:U₀). Π(op:EffError E). Π(_s:State). Σ State E`. Non-resumable — handler surrenders the error payload with the final state. Dispatch action = `\"throw\"`.";
          tests = {
            "handle_strictTy-well-formed" = {
              expr = !((H.inferHoas handle_strictTy) ? error);
              expected = true;
            };
            "handle_strict-checks-against-handle_strictTy" = {
              expr = !((H.checkHoas handle_strictTy handle_strict) ? error);
              expected = true;
            };
          };
        };

        handle_collectingTy = api.leaf {
          value = handle_collectingTy;
          description = "Π-type of the collecting error handler: `Π(E:U₀). Π(op:EffError E). Π(_s:List E). Σ (List E) Unit`. Always resumes — handler accumulates errors into `List E` state, signals resume via `tt`. Dispatch action = `\"resume\"`.";
          tests = {
            "handle_collectingTy-well-formed" = {
              expr = !((H.inferHoas handle_collectingTy) ? error);
              expected = true;
            };
            "handle_collecting-checks-against-handle_collectingTy" = {
              expr = !((H.checkHoas handle_collectingTy handle_collecting) ? error);
              expected = true;
            };
          };
        };

        handle_resultTy = api.leaf {
          value = handle_resultTy;
          description = "Π-type of the result error handler: `Π(E State A_inner:U₀). Π(op:EffError E). Π(_s:State). Σ State (Sum E A_inner)`. Always aborts — handler returns `inl payload` in the Sum-typed result channel. Dispatch action = `\"abort\"`.";
          tests = {
            "handle_resultTy-well-formed" = {
              expr = !((H.inferHoas handle_resultTy) ? error);
              expected = true;
            };
            "handle_result-checks-against-handle_resultTy" = {
              expr = !((H.checkHoas handle_resultTy handle_result) ? error);
              expected = true;
            };
          };
        };

        atType_strict = api.leaf {
          value = atType_strict;
          description = "`atType_strict E State` — per-`(E, State)` monomorphisation of `handle_strict` with a `raise` smart constructor and `dispatch` interpreter pre-built. Pass `{ handler; dispatch; }` to the trampoline.";
          tests = {
            "atType_strict-string-nat-handler-htag" = {
              expr = (atType_strict H.string H.nat).handler._htag;
              expected = "app";
            };
            "atType_strict-string-nat-raise-htag" = {
              expr = ((atType_strict H.string H.nat).raise (H.stringLit "boom"))._htag;
              expected = "desc-con";
            };
          };
        };

        atType_collecting = api.leaf {
          value = atType_collecting;
          description = "`atType_collecting E` — per-`E` monomorphisation of `handle_collecting` (State specialised to `List E`). Exposes the `State` field as a convenience for callers needing `H.nil E` initial values.";
          tests = {
            "atType_collecting-string-handler-htag" = {
              expr = (atType_collecting H.string).handler._htag;
              expected = "app";
            };
          };
        };

        atType_result = api.leaf {
          value = atType_result;
          description = "`atType_result E State A_inner` — per-`(E, State, A_inner)` monomorphisation of `handle_result` with the `Sum E A_inner` result channel pre-built.";
          tests = {
            "atType_result-string-nat-nat-handler-htag" = {
              expr = (atType_result H.string H.nat H.nat).handler._htag;
              expected = "app";
            };
          };
        };

        uniformOf_strictTy = api.leaf {
          value = uniformOf_strictTy;
          description = "Π-type of `uniformOf_strict`: UniRet at A := E (the surrender value rides the abort channel).";
          tests = {
            "uniformOf_strictTy-well-formed" = {
              expr = !((H.inferHoas uniformOf_strictTy) ? error);
              expected = true;
            };
          };
        };

        uniformOf_strict = api.leaf {
          value = uniformOf_strict;
          description = "`uniformOf_strict E State`: UniRet-shaped adapter for `handle_strict`. Projects `Σ State E` into `mkAbort … e s`; always inhabits the right summand.";
          tests = {
            "uniformOf_strict-checks-against-uniformOf_strictTy" = {
              expr = !((H.checkHoas uniformOf_strictTy uniformOf_strict) ? error);
              expected = true;
            };
            "uniformOf_strict-produces-bootInr" = {
              expr =
                let
                  E = H.string;
                  State = H.nat;
                  op = H.app (H.app EffError.error E) (H.stringLit "boom");
                  t = H.app
                    (H.app
                      (H.app
                        (H.app
                          uniformOf_strict
                          E)
                        State)
                      op)
                    H.zero;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInr";
            };
          };
        };

        uniformOf_collectingTy = api.leaf {
          value = uniformOf_collectingTy;
          description = "Π-type of `uniformOf_collecting`: UniRet at S := List E, with A as a phantom parameter (collecting never aborts).";
          tests = {
            "uniformOf_collectingTy-well-formed" = {
              expr = !((H.inferHoas uniformOf_collectingTy) ? error);
              expected = true;
            };
          };
        };

        uniformOf_collecting = api.leaf {
          value = uniformOf_collecting;
          description = "`uniformOf_collecting E A`: UniRet-shaped adapter for `handle_collecting`. Dispatches via EffError.elim so the resume payload `tt : Unit ≡ Resp_collecting E (error E payload)` types in each branch.";
          tests = {
            "uniformOf_collecting-checks-against-uniformOf_collectingTy" = {
              expr = !((H.checkHoas uniformOf_collectingTy uniformOf_collecting) ? error);
              expected = true;
            };
            "uniformOf_collecting-produces-bootInl" = {
              expr =
                let
                  E = H.string;
                  op = H.app (H.app EffError.error E) (H.stringLit "boom");
                  t = H.app
                    (H.app
                      (H.app
                        (H.app
                          uniformOf_collecting
                          E)
                        H.nat)
                      op)
                    (HI.nilAtExplicit E);
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInl";
            };
          };
        };

        uniformOf_resultTy = api.leaf {
          value = uniformOf_resultTy;
          description = "Π-type of `uniformOf_result`: UniRet at A := Sum E A_inner (handle_result's typed result channel becomes the abort value).";
          tests = {
            "uniformOf_resultTy-well-formed" = {
              expr = !((H.inferHoas uniformOf_resultTy) ? error);
              expected = true;
            };
          };
        };

        uniformOf_result = api.leaf {
          value = uniformOf_result;
          description = "`uniformOf_result E State A_inner`: UniRet-shaped adapter for `handle_result`. Projects `Σ State (Sum E A_inner)` into `mkAbort … sumPayload state`.";
          tests = {
            "uniformOf_result-checks-against-uniformOf_resultTy" = {
              expr = !((H.checkHoas uniformOf_resultTy uniformOf_result) ? error);
              expected = true;
            };
            "uniformOf_result-produces-bootInr" = {
              expr =
                let
                  E = H.string;
                  State = H.nat;
                  A_inner = H.nat;
                  op = H.app (H.app EffError.error E) (H.stringLit "boom");
                  t = H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            uniformOf_result
                            E)
                          State)
                        A_inner)
                      op)
                    H.zero;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInr";
            };
          };
        };
      };
    };
  };
}
