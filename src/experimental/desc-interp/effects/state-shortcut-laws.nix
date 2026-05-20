# Kernel-checked one-shot lemmas certifying that `handle_State` on each
# canonical EffState constructor (`get`, `put param`, `modify fn`)
# reduces to the UniRet `mkResumeAt` form expected by the shortcut
# emitter. All three discharge by `H.refl` — kernel conv decides the
# reduction universally:
#
#   ι on `EffState.elim` selects the per-constructor branch
#   β on the branch's λs eliminates the bound payload + state
#   ι on `Resp_State S op` reduces the response type at each op
#
# The lemma RHSes are exactly what `extract.Resume` is told to emit
# at runtime (with `r` and `s` instantiated to the runtime Vals), so
# the kernel-checked equality + the emitter's Val-conv soundness
# (`extract.nix:_self.tests`) chain into:
#
#   vApp (vApp handlerCore opVal) stateVal ≡_Val extract (Resume {…})
#
# at every canonical EffState op.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  C = fx.experimental.desc-interp.compose;
  St = fx.experimental.desc-interp.effects.state;

  withPrefix = body:
    H.forall "S" (H.u 0) (S:
      H.forall "A" (H.u 0) (A:
        body S A));

  lamPrefix = body:
    H.lam "S" (H.u 0) (S:
      H.lam "A" (H.u 0) (A:
        body S A));

  # Shared spine helpers — `Op`/`Resp` are constant across all three
  # canonical ops at fixed `S`.
  Op = S: H.app St.EffState.T S;
  Resp = S: H.app St.Resp_State S;

  handle_StateAt = S: A: op: s:
    H.app (H.app (H.app (H.app St.handle_State S) A) op) s;

  uniRetAt = S: A: op:
    C.uniRetAt S (Op S) (Resp S) op A;

  # ---- get ------------------------------------------------------------
  #
  # `handle_State S A (get S) s ≡ mkResumeAt S Op Resp (get S) A s s`.
  # `Resp_State S (get S) ≡ S` by ι, so the resume payload `s : S` is
  # well-typed in the `Σ _r:(Resp (get S)). S` left summand.

  getBody = S: A:
    H.forall "s" S (s:
      let
        op = St.getAt S;
        lhs = handle_StateAt S A op s;
        rhs = C.mkResumeAt S (Op S) (Resp S) op A s s;
      in
      H.eq (uniRetAt S A op) lhs rhs);

  getReflBody = S: A:
    H.lam "s" S (_: H.refl);

  getLemmaTy = withPrefix getBody;
  getLemma = lamPrefix getReflBody;

  # ---- put ------------------------------------------------------------
  #
  # `handle_State S A (put S param) s ≡ mkResumeAt S Op Resp (put S param) A tt param`.
  # `Resp_State S (put S param) ≡ Unit` by ι, so `tt : Unit` inhabits
  # the response slot. The handler discards the prior state and resumes
  # with the new state set to `param`.

  putBody = S: A:
    H.forall "param" S (param:
      H.forall "s" S (s:
        let
          op = St.putAt S param;
          lhs = handle_StateAt S A op s;
          rhs = C.mkResumeAt S (Op S) (Resp S) op A H.tt param;
        in
        H.eq (uniRetAt S A op) lhs rhs));

  putReflBody = S: A:
    H.lam "param" S (_:
      H.lam "s" S (_: H.refl));

  putLemmaTy = withPrefix putBody;
  putLemma = lamPrefix putReflBody;

  # ---- modify ---------------------------------------------------------
  #
  # `handle_State S A (modify S fn) s ≡ mkResumeAt S Op Resp (modify S fn) A tt (fn s)`.
  # `Resp_State S (modify S fn) ≡ Unit`; new state := `fn s`.

  modifyBody = S: A:
    H.forall "fn" (H.forall "_" S (_: S)) (fn:
      H.forall "s" S (s:
        let
          op = St.modifyAt S fn;
          lhs = handle_StateAt S A op s;
          rhs = C.mkResumeAt S (Op S) (Resp S) op A H.tt (H.app fn s);
        in
        H.eq (uniRetAt S A op) lhs rhs));

  modifyReflBody = S: A:
    H.lam "fn" (H.forall "_" S (_: S)) (_:
      H.lam "s" S (_: H.refl));

  modifyLemmaTy = withPrefix modifyBody;
  modifyLemma = lamPrefix modifyReflBody;

in
{
  scope = {
    "state-shortcut-laws" = api.namespace {
      description = "fx.experimental.desc-interp.effects.state-shortcut-laws: kernel-checked one-shot lemmas for handle_State on each canonical EffState op (get/put/modify). Each lemma discharges by `H.refl` — kernel conv decides reduction universally via ι on EffState.elim + Resp_State. Lemma RHSes match the `extract.Resume` emitter output, anchoring the shortcut path's soundness at the kernel layer.";

      value = {
        getLemmaTy = api.leaf {
          value = getLemmaTy;
          description = "Π-type of get-lemma: `Π S A. Π s:S. handle_State S A (get S) s ≡ mkResumeAt S Op Resp (get S) A s s`.";
          tests = {
            "getLemmaTy-well-formed" = {
              expr = !((H.inferHoas getLemmaTy) ? error);
              expected = true;
            };
          };
        };

        getLemma = api.leaf {
          value = getLemma;
          description = "Proof of get-lemma: 3 lams + H.refl. Reduction at canonical `get` is by ι on `EffState.elim` plus β on the onGet branch; `Resp_State S (get S) ≡ S` by ι makes the resume payload `s` well-typed.";
          tests = {
            "getLemma-checks-against-getLemmaTy" = {
              expr = !((H.checkHoas getLemmaTy getLemma) ? error);
              expected = true;
            };
          };
        };

        putLemmaTy = api.leaf {
          value = putLemmaTy;
          description = "Π-type of put-lemma: `Π S A. Π param s:S. handle_State S A (put S param) s ≡ mkResumeAt S Op Resp (put S param) A tt param`.";
          tests = {
            "putLemmaTy-well-formed" = {
              expr = !((H.inferHoas putLemmaTy) ? error);
              expected = true;
            };
          };
        };

        putLemma = api.leaf {
          value = putLemma;
          description = "Proof of put-lemma: 4 lams + H.refl. `Resp_State S (put S param) ≡ Unit` by ι; the prior state `s` is discarded and resume carries new state `param`.";
          tests = {
            "putLemma-checks-against-putLemmaTy" = {
              expr = !((H.checkHoas putLemmaTy putLemma) ? error);
              expected = true;
            };
          };
        };

        modifyLemmaTy = api.leaf {
          value = modifyLemmaTy;
          description = "Π-type of modify-lemma: `Π S A. Π fn:S→S. Π s:S. handle_State S A (modify S fn) s ≡ mkResumeAt S Op Resp (modify S fn) A tt (fn s)`.";
          tests = {
            "modifyLemmaTy-well-formed" = {
              expr = !((H.inferHoas modifyLemmaTy) ? error);
              expected = true;
            };
          };
        };

        modifyLemma = api.leaf {
          value = modifyLemma;
          description = "Proof of modify-lemma: 4 lams + H.refl. `Resp_State S (modify S fn) ≡ Unit` by ι; new state := `fn s`.";
          tests = {
            "modifyLemma-checks-against-modifyLemmaTy" = {
              expr = !((H.checkHoas modifyLemmaTy modifyLemma) ? error);
              expected = true;
            };
          };
        };
      };
    };
  };
}
