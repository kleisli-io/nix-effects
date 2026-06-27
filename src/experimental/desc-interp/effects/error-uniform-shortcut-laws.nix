# Kernel-checked H.refl lemmas certifying that each `uniformOf_*` on the
# canonical EffError constructor (`error E payload`) reduces to the
# `mkResumeAt`/`mkAbortAt` UniRet form expected by the composed-shortcut
# emitter.
#
# All three `uniformOf_X` are defined as direct `EffError.elim 0`
# dispatches (the universal-property presentation: the eliminator is
# the unique map specified by its per-constructor behavior). At each
# canonical op `error E payload`, ι on the elim fires (single
# constructor → onError branch) and β on the onError λs delivers the
# RHS in one normal-form step. So all three lemmas discharge by a
# single `H.refl`.
#
# The categorical factorization `uniformOf_X = mkAbort ∘ ⟨snd, fst⟩ ∘
# handle_X` (for strict and result; collecting can't factor — its
# typing requires `Resp_collecting E op ≡_ι Unit`, only firing at the
# canonical-constructor branch) holds as a downstream theorem about
# these maps, not as their definition.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  C = fx.experimental.desc-interp.compose;
  Er = fx.experimental.desc-interp.effects.error;

  errorAt = E: payload:
    H.app (H.app Er.EffError.error E) payload;

  EeAt = E: H.app Er.EffError.T E;
  RespSt = E: H.app Er.Resp_strict E;
  RespCo = E: H.app Er.Resp_collecting E;
  RespRe = E: H.app Er.Resp_result E;

  # ---- strict ---------------------------------------------------------

  strictBody = E: State:
    H.forall "payload" E (payload:
      H.forall "s" State (s:
        let
          op = errorAt E payload;
          Ee = EeAt E;
          Resp = RespSt E;
          lhs = H.app (H.app (H.app (H.app Er.uniformOf_strict E) State) op) s;
          rhs = C.mkAbortAt State Ee Resp op E payload s;
        in
        H.eq (C.uniRetAt State Ee Resp op E) lhs rhs));

  strictReflBody = E: State:
    H.lam "payload" E (_:
      H.lam "s" State (_: H.refl));

  strictUniformLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        strictBody E State));

  strictUniformLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        strictReflBody E State));

  # ---- collecting -----------------------------------------------------

  collectingBody = E: A:
    H.forall "payload" E (payload:
      H.forall "s" (H.listOf E) (s:
        let
          op = errorAt E payload;
          Ee = EeAt E;
          State = H.listOf E;
          Resp = RespCo E;
          lhs = H.app (H.app (H.app (H.app Er.uniformOf_collecting E) A) op) s;
          rhs = C.mkResumeAt State Ee Resp op A H.tt (HI.consAtExplicit H.levelZero E payload s);
        in
        H.eq (C.uniRetAt State Ee Resp op A) lhs rhs));

  collectingReflBody = E: A:
    H.lam "payload" E (_:
      H.lam "s" (H.listOf E) (_: H.refl));

  collectingUniformLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "A" (H.u 0) (A:
        collectingBody E A));

  collectingUniformLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "A" (H.u 0) (A:
        collectingReflBody E A));

  # ---- result ---------------------------------------------------------

  resultBody = E: State: A_inner:
    H.forall "payload" E (payload:
      H.forall "s" State (s:
        let
          op = errorAt E payload;
          Ee = EeAt E;
          Resp = RespRe E;
          A = H.sum E A_inner;
          lhs = H.app
            (H.app
              (H.app
                (H.app
                  (H.app
                    Er.uniformOf_result
                    E)
                  State)
                A_inner)
              op)
            s;
          rhs = C.mkAbortAt State Ee Resp op A
            (HI.inlAtExplicit H.levelZero E A_inner payload)
            s;
        in
        H.eq (C.uniRetAt State Ee Resp op A) lhs rhs));

  resultReflBody = E: State: A_inner:
    H.lam "payload" E (_:
      H.lam "s" State (_: H.refl));

  resultUniformLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "A_inner" (H.u 0) (A_inner:
          resultBody E State A_inner)));

  resultUniformLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        H.lam "A_inner" (H.u 0) (A_inner:
          resultReflBody E State A_inner)));

in
{
  scope = {
    "error-uniform-shortcut-laws" = api.namespace {
      description = "fx.experimental.desc-interp.effects.error-uniform-shortcut-laws: kernel-checked H.refl lemmas certifying that each `uniformOf_*` on the canonical EffError raise reduces to the appropriate `mkResumeAt`/`mkAbortAt` UniRet form. All three `uniformOf_X` are defined as direct `EffError.elim 0`-dispatches; at the canonical `error E payload` op, ι on the elim fires (single constructor → onError branch) and β on the onError λs delivers the RHS in one normal-form step. So all three lemmas discharge by H.refl uniformly.";

      value = {
        strictUniformLemmaTy = api.leaf {
          value = strictUniformLemmaTy;
          description = "Π-type of strict-uniform lemma: `Π E State. Π payload:E. Π s:State. uniformOf_strict E State (error E payload) s ≡ mkAbortAt State Ee Resp_strict_E op E payload s : UniRet State Ee Resp_strict_E op E`.";
          tests = {
            "strictUniformLemmaTy-well-formed" = {
              expr = !((H.inferHoas strictUniformLemmaTy) ? error);
              expected = true;
            };
          };
        };

        strictUniformLemma = api.leaf {
          value = strictUniformLemma;
          description = "Proof of strict-uniform lemma: single H.refl over `uniformOf_strict`'s direct `EffError.elim 0` dispatch at the canonical `error` constructor. ι + two β.";
          tests = {
            "strictUniformLemma-checks-against-strictUniformLemmaTy" = {
              expr = !((H.checkHoas strictUniformLemmaTy strictUniformLemma) ? error);
              expected = true;
            };
          };
        };

        collectingUniformLemmaTy = api.leaf {
          value = collectingUniformLemmaTy;
          description = "Π-type of collecting-uniform lemma: `Π E A. Π payload:E. Π s:List E. uniformOf_collecting E A (error E payload) s ≡ mkResumeAt (List E) Ee Resp_collecting_E op A tt (cons E payload s) : UniRet (List E) Ee Resp_collecting_E op A`.";
          tests = {
            "collectingUniformLemmaTy-well-formed" = {
              expr = !((H.inferHoas collectingUniformLemmaTy) ? error);
              expected = true;
            };
          };
        };

        collectingUniformLemma = api.leaf {
          value = collectingUniformLemma;
          description = "Proof of collecting-uniform lemma: single H.refl over `uniformOf_collecting`'s direct `EffError.elim 0` dispatch at the canonical `error` constructor. ι + two β. Kernel typing of mkResume's r-slot additionally requires `Resp_collecting E op ≡_ι Unit`, which the same ι firing delivers.";
          tests = {
            "collectingUniformLemma-checks-against-collectingUniformLemmaTy" = {
              expr = !((H.checkHoas collectingUniformLemmaTy collectingUniformLemma) ? error);
              expected = true;
            };
          };
        };

        resultUniformLemmaTy = api.leaf {
          value = resultUniformLemmaTy;
          description = "Π-type of result-uniform lemma: `Π E State A_inner. Π payload:E. Π s:State. uniformOf_result E State A_inner (error E payload) s ≡ mkAbortAt State Ee Resp_result_E op (Sum E A_inner) (inl E A_inner payload) s : UniRet State Ee Resp_result_E op (Sum E A_inner)`.";
          tests = {
            "resultUniformLemmaTy-well-formed" = {
              expr = !((H.inferHoas resultUniformLemmaTy) ? error);
              expected = true;
            };
          };
        };

        resultUniformLemma = api.leaf {
          value = resultUniformLemma;
          description = "Proof of result-uniform lemma: single H.refl over `uniformOf_result`'s direct `EffError.elim 0` dispatch at the canonical `error` constructor. ι + two β; the onError branch's body emits `mkAbort … (inl E A_inner payload) _s` directly.";
          tests = {
            "resultUniformLemma-checks-against-resultUniformLemmaTy" = {
              expr = !((H.checkHoas resultUniformLemmaTy resultUniformLemma) ? error);
              expected = true;
            };
          };
        };
      };
    };
  };
}
