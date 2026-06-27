# Kernel-checked one-shot lemmas certifying that each `handle_*` on the
# canonical EffError constructor (`error E payload`) reduces to a bare
# `H.pair` shape — the residual the shortcut emitter targets via
# `extract.PairRaw`. All three discharge by `H.refl` — kernel conv
# decides the reduction universally:
#
#   ι on `EffError.elim` selects the (single) `error` constructor branch
#   β on the branch's λs eliminates the bound payload + state
#
# Strategies and their reduced RHS shapes:
#
#   strict     : handle_strict E State (error E p) s
#                  ≡ H.pair s p                       : Σ State E
#   collecting : handle_collecting E (error E p) s
#                  ≡ H.pair (H.cons E p s) H.tt       : Σ (List E) Unit
#   result     : handle_result E State A_i (error E p) s
#                  ≡ H.pair s (H.inl E A_i p)         : Σ State (Sum E A_i)
#
# Each per-strategy `atType_*` factory's `handlerShortcut` builds the
# RHS Val via `extract.PairRaw` + precomputed inner-injector Val
# closures (`inl`-closure for result, `cons`-closure for collecting),
# so emitter conv + this file's H.refl lemmas chain into:
#
#   vApp (vApp handlerCore opVal) stateVal ≡_Val extract (PairRaw …)
#
# at every canonical raise.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  Er = fx.experimental.desc-interp.effects.error;

  errorAt = E: payload:
    H.app (H.app Er.EffError.error E) payload;

  # ---- strict ---------------------------------------------------------
  #
  # `handle_strict E State (error E payload) s ≡ H.pair s payload`.
  # `_s : State` is discarded by name in the handler body — the onError
  # branch returns `H.pair _s payload` with `_s := s` by β.

  strictBody = E: State:
    H.forall "payload" E (payload:
      H.forall "s" State (s:
        let
          op = errorAt E payload;
          lhs = H.app (H.app (H.app (H.app Er.handle_strict E) State) op) s;
          rhs = H.pair s payload;
        in
        H.eq (H.sigma "_state" State (_st: E)) lhs rhs));

  strictReflBody = E: State:
    H.lam "payload" E (_:
      H.lam "s" State (_: H.refl));

  strictRaiseLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        strictBody E State));

  strictRaiseLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        strictReflBody E State));

  # ---- collecting -----------------------------------------------------
  #
  # `handle_collecting E (error E payload) s ≡ H.pair (H.cons E payload s) H.tt`.
  # State is fixed at `List E`; the onError branch cons-es payload onto
  # the prior list and signals resume via `tt : Unit`.

  collectingBody = E:
    H.forall "payload" E (payload:
      H.forall "s" (H.listOf E) (s:
        let
          op = errorAt E payload;
          lhs = H.app (H.app (H.app Er.handle_collecting E) op) s;
          rhs = H.pair (HI.consAtExplicit H.levelZero E payload s) H.tt;
        in
        H.eq (H.sigma "_state" (H.listOf E) (_st: H.unit)) lhs rhs));

  collectingReflBody = E:
    H.lam "payload" E (_:
      H.lam "s" (H.listOf E) (_: H.refl));

  collectingRaiseLemmaTy =
    H.forall "E" (H.u 0) (E:
      collectingBody E);

  collectingRaiseLemma =
    H.lam "E" (H.u 0) (E:
      collectingReflBody E);

  # ---- result ---------------------------------------------------------
  #
  # `handle_result E State A_inner (error E payload) s
  #     ≡ H.pair s (H.inl E A_inner payload)`.
  # `A_inner` is the program's typed result channel; the handler always
  # injects on the left (the error side of the Sum).

  resultBody = E: State: A_inner:
    H.forall "payload" E (payload:
      H.forall "s" State (s:
        let
          op = errorAt E payload;
          lhs = H.app
            (H.app
              (H.app
                (H.app
                  (H.app
                    Er.handle_result
                    E)
                  State)
                A_inner)
              op)
            s;
          rhs = H.pair s (HI.inlAtExplicit H.levelZero E A_inner payload);
        in
        H.eq (H.sigma "_state" State (_st: H.sum E A_inner)) lhs rhs));

  resultReflBody = E: State: A_inner:
    H.lam "payload" E (_:
      H.lam "s" State (_: H.refl));

  resultRaiseLemmaTy =
    H.forall "E" (H.u 0) (E:
      H.forall "State" (H.u 0) (State:
        H.forall "A_inner" (H.u 0) (A_inner:
          resultBody E State A_inner)));

  resultRaiseLemma =
    H.lam "E" (H.u 0) (E:
      H.lam "State" (H.u 0) (State:
        H.lam "A_inner" (H.u 0) (A_inner:
          resultReflBody E State A_inner)));

in
{
  scope = {
    "error-shortcut-laws" = api.namespace {
      description = "fx.experimental.desc-interp.effects.error-shortcut-laws: kernel-checked one-shot lemmas for each `handle_*` on the canonical EffError raise. Each lemma discharges by `H.refl` — ι on EffError.elim fires at the single `error` constructor, then β reduces the onError branch to a bare `H.pair _ _`. RHSes match `extract.PairRaw` emitter output, anchoring per-strategy shortcut soundness at the kernel layer.";

      value = {
        strictRaiseLemmaTy = api.leaf {
          value = strictRaiseLemmaTy;
          description = "Π-type of strict-raise lemma: `Π E State. Π payload:E. Π s:State. handle_strict E State (error E payload) s ≡ H.pair s payload : Σ State E`.";
          tests = {
            "strictRaiseLemmaTy-well-formed" = {
              expr = !((H.inferHoas strictRaiseLemmaTy) ? error);
              expected = true;
            };
          };
        };

        strictRaiseLemma = api.leaf {
          value = strictRaiseLemma;
          description = "Proof of strict-raise lemma: 4 lams + H.refl. EffError has one constructor, so ι on `EffError.elim 0` fires immediately at `error`; β on the onError λs (`H.lam payload. H.lam _s. H.pair _s payload`) yields `H.pair s payload`.";
          tests = {
            "strictRaiseLemma-checks-against-strictRaiseLemmaTy" = {
              expr = !((H.checkHoas strictRaiseLemmaTy strictRaiseLemma) ? error);
              expected = true;
            };
          };
        };

        collectingRaiseLemmaTy = api.leaf {
          value = collectingRaiseLemmaTy;
          description = "Π-type of collecting-raise lemma: `Π E. Π payload:E. Π s:List E. handle_collecting E (error E payload) s ≡ H.pair (H.cons E payload s) H.tt : Σ (List E) Unit`.";
          tests = {
            "collectingRaiseLemmaTy-well-formed" = {
              expr = !((H.inferHoas collectingRaiseLemmaTy) ? error);
              expected = true;
            };
          };
        };

        collectingRaiseLemma = api.leaf {
          value = collectingRaiseLemma;
          description = "Proof of collecting-raise lemma: 3 lams + H.refl. State specialised to `List E`; onError cons-es payload onto the prior list and signals resume via `tt`.";
          tests = {
            "collectingRaiseLemma-checks-against-collectingRaiseLemmaTy" = {
              expr = !((H.checkHoas collectingRaiseLemmaTy collectingRaiseLemma) ? error);
              expected = true;
            };
          };
        };

        resultRaiseLemmaTy = api.leaf {
          value = resultRaiseLemmaTy;
          description = "Π-type of result-raise lemma: `Π E State A_inner. Π payload:E. Π s:State. handle_result E State A_inner (error E payload) s ≡ H.pair s (H.inl E A_inner payload) : Σ State (Sum E A_inner)`.";
          tests = {
            "resultRaiseLemmaTy-well-formed" = {
              expr = !((H.inferHoas resultRaiseLemmaTy) ? error);
              expected = true;
            };
          };
        };

        resultRaiseLemma = api.leaf {
          value = resultRaiseLemma;
          description = "Proof of result-raise lemma: 5 lams + H.refl. Always aborts; the Sum E A_inner result channel always carries the inl-injected payload (handler never produces inr).";
          tests = {
            "resultRaiseLemma-checks-against-resultRaiseLemmaTy" = {
              expr = !((H.checkHoas resultRaiseLemmaTy resultRaiseLemma) ? error);
              expected = true;
            };
          };
        };
      };
    };
  };
}
