# Checking wrapper for the meta-aware elaborator.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;
  V = fx.tc.value;
  T = fx.tc.term;

  Eff = self.metaEff;
  Resp = self.metaResp;

  pure_ = K.pure Eff Resp H.unit;
  bind_ = K.bind Eff Resp H.unit H.unit;

  isMetaTm = tm:
    builtins.isAttrs tm && (tm.tag or null) == "meta";

  isImplicitLamTm = tm:
    builtins.isAttrs tm
    && (tm.tag or null) == "lam"
    && (tm._plicity or "explicit") == "implicit";

  isAppTm = tm:
    builtins.isAttrs tm && (tm.tag or null) == "app";

  isAnnTm = tm:
    builtins.isAttrs tm && (tm.tag or null) == "ann";

  # Checking-only kernel primitives: `inferTm` has no rule for these,
  # so the Sub-rule's infer-then-convert path throws. They go through
  # `elabCheckIntro` instead.
  isIntroForm = tm:
    let t = tm.tag or null;
    in t == "tt";

  kernelIntroCanonTy = tm:
    let t = tm.tag or null;
    in if t == "tt" then V.vUnit
    else null;

  containsMetaVal = v:
    if self.isVMeta v then true
    else if !(builtins.isAttrs v) then false
    else if v.tag or null == "VPi" then containsMetaVal v.domain
    else if v.tag or null == "VLam" then containsMetaVal v.domain
    else if v.tag or null == "VSigma" then containsMetaVal v.fst
    else if v.tag or null == "VPair" then containsMetaVal v.fst || containsMetaVal v.snd
    else false;

  ctxHasMeta = ctx:
    builtins.any containsMetaVal (V.envToList (ctx.types or V.envNil));

  comparisonType = lhs: rhs:
    if self.isVMeta lhs && lhs.type ? ty then lhs.type.ty
    else if self.isVMeta rhs && rhs.type ? ty then rhs.type.ty
    else V.vU V.vLevelZero;

  mismatchError = ctx: tm: expected: got: {
    error = {
      msg = "type mismatch";
      inherit expected got;
      term = { tag = tm.tag; };
      frame = fx.diag.error.captureFrame ctx;
      children = [ ];
    };
    msg = "type mismatch";
    inherit expected got;
  };

  elabSub = ctx: tm: ty:
    bind_ (self.elabInfer ctx tm) (result:
      if result ? error then pure_ result
      else
        bind_ (self.force ty) (forcedTy:
          bind_
            (if self.isImplicitPi forcedTy
             then pure_ result
             else self.insertImplicits ctx result.term result.type)
            (inserted:
              bind_ (self.elabConv ctx.depth (comparisonType inserted.type ty) inserted.type ty) (ok:
                if ok then pure_ inserted.term
                else pure_ (mismatchError ctx tm ty inserted.type)))));

  # Route App through the meta-aware Sub-rule unconditionally so
  # `elabInferApp` can peel implicit binders (insertImplicits). The rigid
  # checker's App rule would otherwise feed the argument directly into the
  # head's domain and report a spurious type mismatch when the head is an
  # implicit-Pi. Conv on the inferred result type is safe under the
  # canonical-form short-circuit in metaIdsVal (conv.nix:79-93).
  rigidOrSub = ctx: tm: ty:
    if containsMetaVal ty || ctxHasMeta ctx || isMetaTm tm || isAppTm tm || isAnnTm tm
    then elabSub ctx tm ty
    else pure_ (fx.tc.check.checkTm ctx tm ty);

  # Unify the constructor's principal codomain with the expected
  # type. Solves the expected meta when forcedTy is `VMeta`.
  elabCheckIntro = ctx: tm: forcedTy:
    let
      canonTy = kernelIntroCanonTy tm;
    in
      if canonTy == null
      then rigidOrSub ctx tm forcedTy
      else
        bind_ (self.elabConv ctx.depth
                 (comparisonType canonTy forcedTy)
                 canonTy forcedTy) (ok:
          if ok then pure_ tm
          else pure_ (mismatchError ctx tm forcedTy canonTy));

  elabCheck = ctx: tm: ty:
    bind_ (self.force ty) (forced:
      if self.isImplicitPi forced && !(isImplicitLamTm tm)
      then
        self.descendImplicitPi ctx forced
          (innerCtx: innerTy: elabCheck innerCtx tm innerTy)
      else if isIntroForm tm
      then elabCheckIntro ctx tm forced
      else if self.isVMetaTy forced
      then
        bind_ (self.plicityAwait ctx forced.id forced ty)
          (_:
            rigidOrSub ctx tm ty)
      else rigidOrSub ctx tm ty);

  elabCheckTm = ctx: tm: ty:
    (self.runElab H.unit (elabCheck ctx tm ty)).value;

  metaType = self.mkVMeta 0 [ ] {
    ctx = fx.tc.check.emptyCtx;
    ty = V.vU V.vLevelZero;
  };
  ctxWithMetaType = {
    env = [ (V.freshVar 0) ];
    types = [ metaType ];
    names = [ "x" ];
    depth = 1;
  };
in
{
  scope = {
    elabCheck = api.leaf {
      value = elabCheck;
      description = "elabCheck ctx tm ty: elaborator checking wrapper. Rigid cases delegate to the rigid checker; meta-involving Sub-rule cases synthesize then call `elabConv`, emitting postponed constraints instead of rigid type errors.";
      signature = "elabCheck : Ctx -> ElabTm -> ElabVal -> ElabComp ElabTm";
      tests = {
        "elabCheck-rigid-tt" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              rigid = fx.tc.check.checkTm ctx T.mkTt V.vUnit;
              got = elabCheckTm ctx T.mkTt V.vUnit;
            in
            got == rigid;
          expected = true;
        };
        "elabCheck-rigid-mismatch-preserves-error" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              got = elabCheckTm ctx (T.mkStringLit "x") V.vUnit;
            in
            {
              hasError = got ? error;
              msg = got.msg or null;
            };
          expected = { hasError = true; msg = "type mismatch"; };
        };
        "elabCheck-meta-sub-emits-constraint" = {
          expr =
            let r = self.runElab H.unit (elabCheck ctxWithMetaType (T.mkVar 0) V.vUnit);
            in {
              termTag = r.value.tag;
              nConstraints = builtins.length r.state.constraints;
            };
          expected = { termTag = "var"; nConstraints = 1; };
        };
        "elabCheck-meta-sub-constraint-shape" = {
          expr =
            let
              r = self.runElab H.unit (elabCheck ctxWithMetaType (T.mkVar 0) V.vUnit);
              c = builtins.head r.state.constraints;
            in
            {
              inherit (c) tag status mentions;
              lhsTag = c.lhs._vTag;
              rhsTag = c.rhs.tag;
              typeTag = c.type.tag;
            };
          expected = {
            tag = "conv";
            status = "solved";
            mentions = [ 0 ];
            lhsTag = "VMeta";
            rhsTag = "VUnit";
            typeTag = "VU";
          };
        };
        # Sub-rule must peel `{A:U}` on the inferred type before conv,
        # so the implicit-Pi `H.nil` aligns with the explicit `List Nat`.
        "elabCheck-hoas-nil-against-listNat-succeeds" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              listNatTm = H.elab (H.listOf H.nat);
              listNatVal = fx.tc.eval.eval [ ] listNatTm;
              nilTm = H.elab H.nil;
              got = elabCheckTm ctx nilTm listNatVal;
            in
            got ? error;
          expected = false;
        };
        # Outer app peels `{A}` via `insertImplicits` (app-mode); the bare
        # `H.nil` argument peels on the Sub-rule's inferred side against
        # the resulting `List ?A`. `?A` solves to `Nat` via conv.
        #
        # Uses raw `H.lower 0` rather than `H.elab` because `H.elab`
        # throws on unsolved metas at the boundary; here the test's job
        # is precisely to feed a meta-bearing Tm to `elabCheckTm` so the
        # Sub-rule peel + conv path can resolve `?A := Nat`.
        "elabCheck-hoas-cons-zero-nil-against-listNat-succeeds" = {
          expr =
            let
              ctx = fx.tc.check.emptyCtx;
              listNatTm = H.elab (H.listOf H.nat);
              listNatVal = fx.tc.eval.eval [ ] listNatTm;
              consTm = H.lower 0 (H.cons H.zero H.nil);
              got = elabCheckTm ctx consTm listNatVal;
            in
            got ? error;
          expected = false;
        };
      };
    };
    elabCheckTm = api.leaf {
      value = elabCheckTm;
      description = "elabCheckTm ctx tm ty: run `elabCheck` under `runElab` and return the value branch.";
      signature = "elabCheckTm : Ctx -> ElabTm -> ElabVal -> ElabTm | Error";
    };
  };

}
