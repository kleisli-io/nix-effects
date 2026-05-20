# Kernel-checked one-shot meta-theorem for `composeHandlers`.
#
# `composeHandlers … H_A H_B (inl op_A) (pair s_A s_B)` reduces by conv
# to `sumElim (H_A op_A s_A) (mkResume_composed …) (mkAbort_composed …)`
# with `s_B` threaded; symmetric for `inr op_B`. Both discharge by
# `H.refl` — kernel conv decides the reduction universally over the
# handler/op/state binders.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  C = fx.experimental.desc-interp.compose;

  withPrefix = body:
    H.forall "S_A" (H.u 0) (S_A:
      H.forall "S_B" (H.u 0) (S_B:
        H.forall "Op_A" (H.u 0) (Op_A:
          H.forall "Op_B" (H.u 0) (Op_B:
            H.forall "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (Resp_A:
              H.forall "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (Resp_B:
                H.forall "A" (H.u 0) (A:
                  H.forall "H_A"
                    (H.forall "op" Op_A (op:
                      H.forall "_s" S_A (_s:
                        C.uniRetAt S_A Op_A Resp_A op A)))
                    (H_A:
                      H.forall "H_B"
                        (H.forall "op" Op_B (op:
                          H.forall "_s" S_B (_s:
                            C.uniRetAt S_B Op_B Resp_B op A)))
                        (H_B:
                          body S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B)))))))));

  lamPrefix = body:
    H.lam "S_A" (H.u 0) (S_A:
      H.lam "S_B" (H.u 0) (S_B:
        H.lam "Op_A" (H.u 0) (Op_A:
          H.lam "Op_B" (H.u 0) (Op_B:
            H.lam "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (Resp_A:
              H.lam "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (Resp_B:
                H.lam "A" (H.u 0) (A:
                  H.lam "H_A"
                    (H.forall "op" Op_A (op:
                      H.forall "_s" S_A (_s:
                        C.uniRetAt S_A Op_A Resp_A op A)))
                    (H_A:
                      H.lam "H_B"
                        (H.forall "op" Op_B (op:
                          H.forall "_s" S_B (_s:
                            C.uniRetAt S_B Op_B Resp_B op A)))
                        (H_B:
                          body S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B)))))))));

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

  inlBody = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    H.forall "op_A" Op_A (op_A:
      H.forall "s_A" S_A (s_A:
        H.forall "s_B" S_B (s_B:
          let
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            composedOp = HI.inlAtExplicit H.levelZero Op_A Op_B op_A;
            composedState = H.pair s_A s_B;
            composedHandler = composedHandlerAt
              S_A
              S_B
              Op_A
              Op_B
              Resp_A
              Resp_B
              A
              H_A
              H_B;
            lhs = H.app (H.app composedHandler composedOp) composedState;
            r = H.app (H.app H_A op_A) s_A;
            leftForInner = H.sigma "_r" (H.app Resp_A op_A) (_: S_A);
            rightForInner = H.sigma "_a" A (_: S_A);
            UniRetComposedTy = C.uniRetAt SigmaS SumOp RespC composedOp A;
            innerMotive = H.lam "_r" (H.sum leftForInner rightForInner) (_r:
              UniRetComposedTy);
            onInnerLeft = H.lam "pair_r_s" leftForInner (pair_rs:
              C.mkResumeAt SigmaS SumOp RespC composedOp A
                (H.fst_ pair_rs)
                (H.pair (H.snd_ pair_rs) s_B));
            onInnerRight = H.lam "pair_a_s" rightForInner (pair_as:
              C.mkAbortAt SigmaS SumOp RespC composedOp A
                (H.fst_ pair_as)
                (H.pair (H.snd_ pair_as) s_B));
            rhs = H.sumElim 0
              leftForInner
              rightForInner
              innerMotive
              onInnerLeft
              onInnerRight
              r;
          in
          H.eq UniRetComposedTy lhs rhs)));

  # Inr clause: handler runs on s_B; repack threads s_A unchanged.
  inrBody = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    H.forall "op_B" Op_B (op_B:
      H.forall "s_A" S_A (s_A:
        H.forall "s_B" S_B (s_B:
          let
            SigmaS = H.sigma "_sA" S_A (_: S_B);
            SumOp = H.sum Op_A Op_B;
            RespC = C.composedRespAt Op_A Op_B Resp_A Resp_B;
            composedOp = HI.inrAtExplicit H.levelZero Op_A Op_B op_B;
            composedState = H.pair s_A s_B;
            composedHandler = composedHandlerAt
              S_A
              S_B
              Op_A
              Op_B
              Resp_A
              Resp_B
              A
              H_A
              H_B;
            lhs = H.app (H.app composedHandler composedOp) composedState;
            r = H.app (H.app H_B op_B) s_B;
            leftForInner = H.sigma "_r" (H.app Resp_B op_B) (_: S_B);
            rightForInner = H.sigma "_a" A (_: S_B);
            UniRetComposedTy = C.uniRetAt SigmaS SumOp RespC composedOp A;
            innerMotive = H.lam "_r" (H.sum leftForInner rightForInner) (_r:
              UniRetComposedTy);
            onInnerLeft = H.lam "pair_r_s" leftForInner (pair_rs:
              C.mkResumeAt SigmaS SumOp RespC composedOp A
                (H.fst_ pair_rs)
                (H.pair s_A (H.snd_ pair_rs)));
            onInnerRight = H.lam "pair_a_s" rightForInner (pair_as:
              C.mkAbortAt SigmaS SumOp RespC composedOp A
                (H.fst_ pair_as)
                (H.pair s_A (H.snd_ pair_as)));
            rhs = H.sumElim 0
              leftForInner
              rightForInner
              innerMotive
              onInnerLeft
              onInnerRight
              r;
          in
          H.eq UniRetComposedTy lhs rhs)));

  reflBodyInl = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    H.lam "op_A" Op_A (op_A:
      H.lam "s_A" S_A (s_A:
        H.lam "s_B" S_B (s_B: H.refl)));

  reflBodyInr = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    H.lam "op_B" Op_B (op_B:
      H.lam "s_A" S_A (s_A:
        H.lam "s_B" S_B (s_B: H.refl)));

  composeHandlersInlLemmaTy = withPrefix inlBody;
  composeHandlersInlLemma = lamPrefix reflBodyInl;

  composeHandlersInrLemmaTy = withPrefix inrBody;
  composeHandlersInrLemma = lamPrefix reflBodyInr;

in
{
  scope = {
    "compose-laws" = api.namespace {
      description = "fx.experimental.desc-interp.compose-laws: kernel-checked one-shot meta-theorem for composeHandlers. Two clauses (inl/inr); both discharge by H.refl.";

      value = {
        composeHandlersInlLemmaTy = api.leaf {
          value = composeHandlersInlLemmaTy;
          description = "Inl clause Π-type: composeHandlers on (inl op_A, pair s_A s_B) ≡ sumElim … (H_A op_A s_A) (mkResume_composed …) (mkAbort_composed …) with s_B threaded.";
          tests = {
            "composeHandlersInlLemmaTy-well-formed" = {
              expr = !((H.inferHoas composeHandlersInlLemmaTy) ? error);
              expected = true;
            };
          };
        };

        composeHandlersInlLemma = api.leaf {
          value = composeHandlersInlLemma;
          description = "Inl clause proof: 12 lams + H.refl. checkHoas succeeds because kernel conv decides composeHandlers' iota universally.";
          tests = {
            "composeHandlersInlLemma-checks-against-inlLemmaTy" = {
              expr = !((H.checkHoas composeHandlersInlLemmaTy composeHandlersInlLemma) ? error);
              expected = true;
            };
          };
        };

        composeHandlersInrLemmaTy = api.leaf {
          value = composeHandlersInrLemmaTy;
          description = "Inr clause Π-type: mirror of the inl clause with the state-slot roles swapped.";
          tests = {
            "composeHandlersInrLemmaTy-well-formed" = {
              expr = !((H.inferHoas composeHandlersInrLemmaTy) ? error);
              expected = true;
            };
          };
        };

        composeHandlersInrLemma = api.leaf {
          value = composeHandlersInrLemma;
          description = "Inr clause proof: 12 lams + H.refl.";
          tests = {
            "composeHandlersInrLemma-checks-against-inrLemmaTy" = {
              expr = !((H.checkHoas composeHandlersInrLemmaTy composeHandlersInrLemma) ? error);
              expected = true;
            };
          };
        };
      };
    };
  };
}
