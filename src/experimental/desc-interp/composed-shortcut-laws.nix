# H.refl-discharged lemmas certifying `composeHandlers` at each canonical
# `(sub-handler, sub-canonical-op)` reduces to the composed `mkResumeAt`/
# `mkAbortAt` shape the shortcut emits.
#
# Discharge chain (all conv-decidable, fires entirely under kernel ι+β):
# `composeHandlersInl/InrLemma` (outer reduction) → per-effect uniform-
# shortcut lemma (sub-handler reduction at the canonical op) → inner
# `sumElim` ι (re-injection with repacked state). The off-side handler is
# left Π-bound because the dispatched side is fixed by the composedOp's
# inl/inr tag.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  C = fx.experimental.desc-interp.compose;
  St = fx.experimental.desc-interp.effects.state;
  Er = fx.experimental.desc-interp.effects.error;

  composedHandlerAt = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    H.app
      (H.app
        (H.app
          (H.app
            (H.app
              (H.app
                (H.app
                  (H.app (H.app C.composeHandlers S_A) S_B)
                  Op_A)
                Op_B)
              Resp_A)
            Resp_B)
          A)
        H_A)
      H_B;

  # Π-type of an off-side handler at fixed (S, Op, Resp, A).
  subHandlerTy = S: Op: Resp: A:
    H.forall "op" Op (op:
      H.forall "_s" S (_s:
        C.uniRetAt S Op Resp op A));

  # State-side lemmas — `H_A := handle_State`, off-side `H_B` Π-bound at
  # the collecting typing (concrete Op_B/Resp_B/S_B keeps `H_B`'s type
  # closed; the body never invokes it on inl-dispatch).

  stateInlPrefixTy = body:
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_B = H.app Er.Resp_collecting E;
          in
          H.forall "H_B" (subHandlerTy S_B Op_B Resp_B A) (H_B:
            body { inherit E S_A A S_B Op_A Op_B Resp_B H_B; }))));

  stateInlPrefixLam = body:
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_B = H.app Er.Resp_collecting E;
          in
          H.lam "H_B" (subHandlerTy S_B Op_B Resp_B A) (H_B:
            body { inherit E S_A A S_B Op_A Op_B Resp_B H_B; }))));

  # `composedHandler ≡ mkResumeAt … r (pair sNew s_B)` for canonical
  # inl-state op + per-op `(r, sNew)`. No-extra-parameter ops only;
  # `put`/`modify` inline the prefix to bind their extra Π.
  stateInlBody = { canonicalOp, rOf, sNewOf }:
    { E, S_A, A, S_B, Op_A, Op_B, Resp_B, H_B }:
    let
      Resp_A = H.app St.Resp_State S_A;
      H_A = H.app (H.app St.handle_State S_A) A;
      SigmaS = H.sigma "_sA" S_A (_: S_B);
      SumOp = H.sum Op_A Op_B;
      RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
      cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
    in
    H.forall "s_A" S_A (s_A:
      H.forall "s_B" S_B (s_B:
        let
          op = canonicalOp { inherit S_A; };
          composedOp = HI.inlAtExplicit H.levelZero Op_A Op_B op;
          composedState = H.pair s_A s_B;
          lhs = H.app (H.app cHand composedOp) composedState;
          r = rOf { inherit s_A; };
          newSubState = sNewOf { inherit s_A; };
          rhs = C.mkResumeAt SigmaS SumOp RespC composedOp A
            r
            (H.pair newSubState s_B);
        in
        H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs));

  stateInlReflBody = { S_A, S_B, ... }:
    H.lam "s_A" S_A (_:
      H.lam "s_B" S_B (_: H.refl));

  # state-get-inl
  stateGetInlLemmaTy = stateInlPrefixTy
    (stateInlBody {
      canonicalOp = { S_A, ... }: St.getAt S_A;
      rOf = { s_A, ... }: s_A;
      sNewOf = { s_A, ... }: s_A;
    });
  stateGetInlLemma = stateInlPrefixLam stateInlReflBody;

  # state-put-inl: `Resp_State (put _) ≡ Unit` by ι; resume payload `tt`,
  # new sub-state `param`. Prefix inlined to bind `param:S_A` in the Π.
  statePutInlLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_B = H.app Er.EffError.T E;
            Resp_B = H.app Er.Resp_collecting E;
          in
          H.lam "H_B" (subHandlerTy S_B Op_B Resp_B A) (_H_B:
            H.lam "param" S_A (_:
              H.lam "s_A" S_A (_:
                H.lam "s_B" S_B (_: H.refl)))))));

  statePutInlLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_A = H.app St.Resp_State S_A;
            Resp_B = H.app Er.Resp_collecting E;
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            H_A = H.app (H.app St.handle_State S_A) A;
          in
          H.forall "H_B" (subHandlerTy S_B Op_B Resp_B A) (H_B:
            H.forall "param" S_A (param:
              H.forall "s_A" S_A (s_A:
                H.forall "s_B" S_B (s_B:
                  let
                    op = St.putAt S_A param;
                    composedOp = HI.inlAtExplicit H.levelZero Op_A Op_B op;
                    composedState = H.pair s_A s_B;
                    cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                    lhs = H.app (H.app cHand composedOp) composedState;
                    rhs = C.mkResumeAt SigmaS SumOp RespC composedOp A
                      H.tt
                      (H.pair param s_B);
                  in
                  H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs)))))));

  # state-modify-inl: resume payload `tt`, new sub-state `fn s_A`.
  stateModifyInlLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_A = H.app St.Resp_State S_A;
            Resp_B = H.app Er.Resp_collecting E;
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            H_A = H.app (H.app St.handle_State S_A) A;
            fnTy = H.forall "_" S_A (_: S_A);
          in
          H.forall "H_B" (subHandlerTy S_B Op_B Resp_B A) (H_B:
            H.forall "fn" fnTy (fn:
              H.forall "s_A" S_A (s_A:
                H.forall "s_B" S_B (s_B:
                  let
                    op = St.modifyAt S_A fn;
                    composedOp = HI.inlAtExplicit H.levelZero Op_A Op_B op;
                    composedState = H.pair s_A s_B;
                    cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                    lhs = H.app (H.app cHand composedOp) composedState;
                    rhs = C.mkResumeAt SigmaS SumOp RespC composedOp A
                      H.tt
                      (H.pair (H.app fn s_A) s_B);
                  in
                  H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs)))))));

  stateModifyInlLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_B = H.app Er.EffError.T E;
            Resp_B = H.app Er.Resp_collecting E;
            fnTy = H.forall "_" S_A (_: S_A);
          in
          H.lam "H_B" (subHandlerTy S_B Op_B Resp_B A) (_H_B:
            H.lam "fn" fnTy (_:
              H.lam "s_A" S_A (_:
                H.lam "s_B" S_B (_: H.refl)))))));

  # Error-side lemmas — `H_B := uniformOf_X`, `H_A` Π-bound over the
  # state typing (never invoked on inr-dispatch).
  #
  #   collecting  S_B := List E,  A free            → composed Resume
  #   strict      S_B free,       A := E            → composed Abort
  #   result      S_B free,       A := Sum E A_i    → composed Abort

  errorCollectingInrLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_A = H.app St.Resp_State S_A;
            Resp_B = H.app Er.Resp_collecting E;
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            H_B = H.app (H.app Er.uniformOf_collecting E) A;
          in
          H.forall "H_A" (subHandlerTy S_A Op_A Resp_A A) (H_A:
            H.forall "payload" E (payload:
              H.forall "s_A" S_A (s_A:
                H.forall "s_B" S_B (s_B:
                  let
                    op = H.app (H.app Er.EffError.error E) payload;
                    composedOp = HI.inrAtExplicit H.levelZero Op_A Op_B op;
                    composedState = H.pair s_A s_B;
                    cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                    lhs = H.app (H.app cHand composedOp) composedState;
                    rhs = C.mkResumeAt SigmaS SumOp RespC composedOp A
                      H.tt
                      (H.pair s_A (HI.consAtExplicit H.levelZero E payload s_B));
                  in
                  H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs)))))));

  errorCollectingInrLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "A" (H.u 0) (A:
          let
            S_B = H.listOf E;
            Op_A = H.app St.EffState.T S_A;
            Resp_A = H.app St.Resp_State S_A;
          in
          H.lam "H_A" (subHandlerTy S_A Op_A Resp_A A) (_H_A:
            H.lam "payload" E (_:
              H.lam "s_A" S_A (_:
                H.lam "s_B" S_B (_: H.refl)))))));

  errorStrictInrLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "S_B" (H.u 0) (S_B:
          let
            Op_A = H.app St.EffState.T S_A;
            Op_B = H.app Er.EffError.T E;
            Resp_A = H.app St.Resp_State S_A;
            Resp_B = H.app Er.Resp_strict E;
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            A = E;
            H_B = H.app (H.app Er.uniformOf_strict E) S_B;
          in
          H.forall "H_A" (subHandlerTy S_A Op_A Resp_A A) (H_A:
            H.forall "payload" E (payload:
              H.forall "s_A" S_A (s_A:
                H.forall "s_B" S_B (s_B:
                  let
                    op = H.app (H.app Er.EffError.error E) payload;
                    composedOp = HI.inrAtExplicit H.levelZero Op_A Op_B op;
                    composedState = H.pair s_A s_B;
                    cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                    lhs = H.app (H.app cHand composedOp) composedState;
                    rhs = C.mkAbortAt SigmaS SumOp RespC composedOp A
                      payload
                      (H.pair s_A s_B);
                  in
                  H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs)))))));

  errorStrictInrLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "S_B" (H.u 0) (S_B:
          let
            Op_A = H.app St.EffState.T S_A;
            Resp_A = H.app St.Resp_State S_A;
            A = E;
          in
          H.lam "H_A" (subHandlerTy S_A Op_A Resp_A A) (_H_A:
            H.lam "payload" E (_:
              H.lam "s_A" S_A (_:
                H.lam "s_B" S_B (_: H.refl)))))));

  errorResultInrLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "S_A" (H.u 0) (S_A:
        H.forall "S_B" (H.u 0) (S_B:
          H.forall "A_inner" (H.u 0) (A_inner:
            let
              Op_A = H.app St.EffState.T S_A;
              Op_B = H.app Er.EffError.T E;
              Resp_A = H.app St.Resp_State S_A;
              Resp_B = H.app Er.Resp_result E;
              SigmaS = H.sigma "_sA" S_A (_: S_B);
              SumOp = H.sum Op_A Op_B;
              RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
              A = H.sum E A_inner;
              H_B = H.app (H.app (H.app Er.uniformOf_result E) S_B) A_inner;
            in
            H.forall "H_A" (subHandlerTy S_A Op_A Resp_A A) (H_A:
              H.forall "payload" E (payload:
                H.forall "s_A" S_A (s_A:
                  H.forall "s_B" S_B (s_B:
                    let
                      op = H.app (H.app Er.EffError.error E) payload;
                      composedOp = HI.inrAtExplicit H.levelZero Op_A Op_B op;
                      composedState = H.pair s_A s_B;
                      cHand = composedHandlerAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                      lhs = H.app (H.app cHand composedOp) composedState;
                      rhs = C.mkAbortAt SigmaS SumOp RespC composedOp A
                        (HI.inlAtExplicit H.levelZero E A_inner payload)
                        (H.pair s_A s_B);
                    in
                    H.eq (C.uniRetAt SigmaS SumOp RespC composedOp A) lhs rhs))))))));

  errorResultInrLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "S_A" (H.u 0) (S_A:
        H.lam "S_B" (H.u 0) (S_B:
          H.lam "A_inner" (H.u 0) (A_inner:
            let
              Op_A = H.app St.EffState.T S_A;
              Resp_A = H.app St.Resp_State S_A;
              A = H.sum E A_inner;
            in
            H.lam "H_A" (subHandlerTy S_A Op_A Resp_A A) (_H_A:
              H.lam "payload" E (_:
                H.lam "s_A" S_A (_:
                  H.lam "s_B" S_B (_: H.refl))))))));

in
{
  scope = {
    "composed-shortcut-laws" = api.namespace {
      description = "fx.experimental.desc-interp.composed-shortcut-laws: six H.refl lemmas — state's three canonical ops on inl and error's three strategies on inr — anchoring `composedHandlerShortcut` soundness. Each chains `composeHandlersInl/InrLemma`, the per-effect uniform-shortcut lemma, and inner `sumElim` ι; all three reductions are conv-decidable.";

      value = {
        stateGetInlLemmaTy = api.leaf {
          value = stateGetInlLemmaTy;
          description = "`Π E S_A A. Π H_B. Π s_A:S_A. Π s_B:List E. composeHandlers … handle_State H_B (inl (get S_A)) (pair s_A s_B) ≡ mkResumeAt … (inl (get S_A)) A s_A (pair s_A s_B)`.";
          tests = {
            "stateGetInlLemmaTy-well-formed" = {
              expr = !((H.inferHoas stateGetInlLemmaTy) ? error);
              expected = true;
            };
          };
        };
        stateGetInlLemma = api.leaf {
          value = stateGetInlLemma;
          description = "H.refl proof of `stateGetInlLemmaTy`. `handle_State (get S) s_A ι→ inl(pair s_A s_A)`; inner sumElim ι folds to the composed mkResumeAt.";
          tests = {
            "stateGetInlLemma-checks-against-stateGetInlLemmaTy" = {
              expr = !((H.checkHoas stateGetInlLemmaTy stateGetInlLemma) ? error);
              expected = true;
            };
          };
        };
        statePutInlLemmaTy = api.leaf {
          value = statePutInlLemmaTy;
          description = "`Π E S_A A. Π H_B. Π param s_A:S_A. Π s_B:List E. composeHandlers … handle_State H_B (inl (put S_A param)) (pair s_A s_B) ≡ mkResumeAt … tt (pair param s_B)`.";
          tests = {
            "statePutInlLemmaTy-well-formed" = {
              expr = !((H.inferHoas statePutInlLemmaTy) ? error);
              expected = true;
            };
          };
        };
        statePutInlLemma = api.leaf {
          value = statePutInlLemma;
          description = "H.refl proof of `statePutInlLemmaTy`. New sub-state := `param`; resume payload := `tt`.";
          tests = {
            "statePutInlLemma-checks-against-statePutInlLemmaTy" = {
              expr = !((H.checkHoas statePutInlLemmaTy statePutInlLemma) ? error);
              expected = true;
            };
          };
        };
        stateModifyInlLemmaTy = api.leaf {
          value = stateModifyInlLemmaTy;
          description = "`Π E S_A A. Π H_B. Π fn:S_A→S_A. Π s_A:S_A. Π s_B:List E. composeHandlers … handle_State H_B (inl (modify S_A fn)) (pair s_A s_B) ≡ mkResumeAt … tt (pair (fn s_A) s_B)`.";
          tests = {
            "stateModifyInlLemmaTy-well-formed" = {
              expr = !((H.inferHoas stateModifyInlLemmaTy) ? error);
              expected = true;
            };
          };
        };
        stateModifyInlLemma = api.leaf {
          value = stateModifyInlLemma;
          description = "H.refl proof of `stateModifyInlLemmaTy`. New sub-state := `fn s_A`; resume payload := `tt`.";
          tests = {
            "stateModifyInlLemma-checks-against-stateModifyInlLemmaTy" = {
              expr = !((H.checkHoas stateModifyInlLemmaTy stateModifyInlLemma) ? error);
              expected = true;
            };
          };
        };
        errorCollectingInrLemmaTy = api.leaf {
          value = errorCollectingInrLemmaTy;
          description = "`Π E S_A A. Π H_A. Π payload:E. Π s_A:S_A. Π s_B:List E. composeHandlers … H_A uniformOf_collecting (inr (error E payload)) (pair s_A s_B) ≡ mkResumeAt … tt (pair s_A (cons E payload s_B))`.";
          tests = {
            "errorCollectingInrLemmaTy-well-formed" = {
              expr = !((H.inferHoas errorCollectingInrLemmaTy) ? error);
              expected = true;
            };
          };
        };
        errorCollectingInrLemma = api.leaf {
          value = errorCollectingInrLemma;
          description = "H.refl proof of `errorCollectingInrLemmaTy`. Resume payload := `tt`; new s_B := `cons E payload s_B`.";
          tests = {
            "errorCollectingInrLemma-checks-against-errorCollectingInrLemmaTy" = {
              expr = !((H.checkHoas errorCollectingInrLemmaTy errorCollectingInrLemma) ? error);
              expected = true;
            };
          };
        };
        errorStrictInrLemmaTy = api.leaf {
          value = errorStrictInrLemmaTy;
          description = "`Π E S_A S_B. Π H_A. Π payload:E. Π s_A:S_A. Π s_B:S_B. composeHandlers … H_A uniformOf_strict (inr (error E payload)) (pair s_A s_B) ≡ mkAbortAt … E payload (pair s_A s_B)`.";
          tests = {
            "errorStrictInrLemmaTy-well-formed" = {
              expr = !((H.inferHoas errorStrictInrLemmaTy) ? error);
              expected = true;
            };
          };
        };
        errorStrictInrLemma = api.leaf {
          value = errorStrictInrLemma;
          description = "H.refl proof of `errorStrictInrLemmaTy`. Strict always aborts; abort payload := `payload`.";
          tests = {
            "errorStrictInrLemma-checks-against-errorStrictInrLemmaTy" = {
              expr = !((H.checkHoas errorStrictInrLemmaTy errorStrictInrLemma) ? error);
              expected = true;
            };
          };
        };
        errorResultInrLemmaTy = api.leaf {
          value = errorResultInrLemmaTy;
          description = "`Π E S_A S_B A_inner. Π H_A. Π payload:E. Π s_A:S_A. Π s_B:S_B. composeHandlers … H_A uniformOf_result (inr (error E payload)) (pair s_A s_B) ≡ mkAbortAt … (Sum E A_inner) (inl E A_inner payload) (pair s_A s_B)`.";
          tests = {
            "errorResultInrLemmaTy-well-formed" = {
              expr = !((H.inferHoas errorResultInrLemmaTy) ? error);
              expected = true;
            };
          };
        };
        errorResultInrLemma = api.leaf {
          value = errorResultInrLemma;
          description = "H.refl proof of `errorResultInrLemmaTy`. Abort channel `Sum E A_inner` carries `inl payload`.";
          tests = {
            "errorResultInrLemma-checks-against-errorResultInrLemmaTy" = {
              expr = !((H.checkHoas errorResultInrLemmaTy errorResultInrLemma) ? error);
              expected = true;
            };
          };
        };
      };
    };
  };
}
