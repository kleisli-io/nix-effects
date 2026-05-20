# Synthesis wrapper for the meta-aware elaborator.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;
  V = fx.tc.value;
  T = fx.tc.term;

  Eff = self.metaEff;
  Resp = self.metaResp;
  E = fx.tc.eval;

  pure_ = K.pure Eff Resp H.unit;
  bind_ = K.bind Eff Resp H.unit H.unit;

  isMetaTm = tm:
    builtins.isAttrs tm && (tm.tag or null) == "meta";

  isAppTm = tm:
    builtins.isAttrs tm && (tm.tag or null) == "app";

  missingMetaType = tm: {
    error = {
      msg = "meta term requires a type annotation for synthesis";
      term = tm;
    };
    msg = "meta term requires a type annotation for synthesis";
    expected = "type";
    got = null;
  };

  elabInferApp = ctx: tm:
    bind_ (elabInfer ctx tm.fn) (fResult:
      if builtins.isAttrs fResult && fResult ? error then pure_ fResult
      else
        let userExplicit = (tm._plicity or "explicit") == "explicit"; in
        bind_
          (if userExplicit
          then self.insertImplicits ctx fResult.term fResult.type
          else pure_ { term = fResult.term; type = fResult.type; })
          (ins:
            let fTy = ins.type; in
            if (fTy.tag or null) != "VPi"
            then
              pure_
                {
                  error = {
                    msg = "expected function type";
                    expected = { tag = "pi"; };
                    got = fTy;
                    term = { tag = tm.tag; };
                  };
                  msg = "expected function type";
                  expected = { tag = "pi"; };
                  got = fTy;
                }
            else
              bind_ (self.elabCheck ctx tm.arg fTy.domain) (uTm:
                if builtins.isAttrs uTm && uTm ? error
                then pure_ uTm
                else
                  # Meta-aware: `elabCheck` may emit a Tm whose evaluation
                  # contains a VMeta (unsolved arg), and `fTy.closure`'s
                  # body may apply that VMeta as a function head. Both the
                  # eval and the instantiate must route through the
                  # VMeta-aware overlay so `vAppF` doesn't read `.tag` on
                  # a VMeta. Matches insertion.nix and meta/unify.nix.
                  let retTy = self.instantiateOverlay fTy.closure (self.evalOverlay (ctx.env or [ ]) uTm); in
                  pure_ { term = T.mkApp ins.term uTm; type = retTy; })));

  elabInfer = ctx: tm:
    if isMetaTm tm then
      if tm ? type && builtins.isAttrs tm.type && tm.type ? ty
      then pure_ { term = tm; type = tm.type.ty; }
      else pure_ (missingMetaType tm)
    else if isAppTm tm then elabInferApp ctx tm
    else pure_ (fx.tc.check.inferTm ctx tm);

  elabInferTm = ctx: tm:
    (self.runElab H.unit (elabInfer ctx tm)).value;

  metaType = self.mkVMeta 0 [ ] {
    ctx = fx.tc.check.emptyCtx;
    ty = V.vU V.vLevelZero;
  };
in
{
  scope = {
    elabInfer = api.leaf {
      value = elabInfer;
      description = "elabInfer ctx tm: elaborator synthesis wrapper. Rigid terms delegate to the rigid checker; overlay meta terms carrying a type annotation synthesize that annotation without entering the rigid checker.";
      signature = "elabInfer : Ctx -> ElabTm -> ElabComp { term : ElabTm; type : ElabVal }";
      tests = {
        "elabInfer-rigid-string-lit" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              tm = T.mkStringLit "x";
              rigid = fx.tc.check.inferTm ctx tm;
              got = elabInferTm ctx tm;
            in
            got == rigid;
          expected = true;
        };
        "elabInfer-meta-term-with-type" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              tm = (self.mkMeta 0 [ ]) // {
                type = { ctx = fx.tc.check.emptyCtx; ty = metaType; };
              };
              got = elabInferTm ctx tm;
            in
            {
              termTag = got.term.tag;
              typeTag = got.type._vTag;
              typeId = got.type.id;
            };
          expected = { termTag = "meta"; typeTag = "VMeta"; typeId = 0; };
        };
      };
    };
    elabInferTm = api.leaf {
      value = elabInferTm;
      description = "elabInferTm ctx tm: run `elabInfer` under `runElab` and return the value branch.";
      signature = "elabInferTm : Ctx -> ElabTm -> { term; type } | Error";
    };
    elabInferApp = api.leaf {
      value = elabInferApp;
      description = "elabInferApp ctx tm: App-mode synthesis. Infers fn type, peels leading implicit Pis via `insertImplicits` when the call site is explicit, then checks the argument against the resulting explicit domain.";
      signature = "elabInferApp : Ctx -> ElabTm -> Comp ({ term; type } | Error)";
    };
  };

}
