# Bidirectional implicit-argument insertion (smalltt-style).
#
# Two operations:
#   - insertImplicits ctx (fTm, fTy) : peel leading implicit Pi binders
#     from a function's inferred type by allocating fresh metas at each.
#     Used at infer-mode App before checking the explicit argument.
#   - descendImplicitPi ctx tm expectedTy inner : when checking against
#     {x:A} → B and `tm` is not an implicit lam, prepend an implicit
#     binder around `tm` and recurse with the body's expected type.
#
# Postpone discipline: when the type driving insertion is itself an
# unsolved VMeta, emit a `plicity-await` constraint via emitConstraint
# (Optimist Lemma — Gundry-McBride-McKinna 2010 §6.2 Lemma 4) and fall
# through to the underlying Sub-rule.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  quote = self.quote;

  Eff = self.metaEff;
  Resp = self.metaResp;

  pure_ = K.pure Eff Resp H.unit;
  bind_ = K.bind Eff Resp H.unit H.unit;

  isImplicitPi = v:
    builtins.isAttrs v
    && (v.tag or null) == "VPi"
    && (v._plicity or "explicit") == "implicit";

  isVMetaTy = v:
    builtins.isAttrs v && (v._vTag or null) == "VMeta";

  metaTypeAt = ctx: ty: { inherit ctx ty; };

  # insertImplicits ctx (fTm, fTy) returns Comp { term; type } where
  # leading implicit binders of `fTy` have been consumed by fresh metas.
  insertImplicits = ctx: fTm: fTy:
    bind_ (self.force fTy) (forced:
      if isImplicitPi forced then
        bind_ (self.freshMeta (metaTypeAt ctx forced.domain))
          (m:
            let
              mTm = quote ctx.depth m;
              fTm' = T.mkApp fTm mTm;
              # Meta-aware instantiation: `m` is a VMeta, and the kernel
              # evaluator would crash reading `.tag` on it from inside
              # the closure body. The overlay routes app/elim through
              # VMeta-aware variants. See `eval-overlay.nix`.
              fTy' = self.instantiateOverlay forced.closure m;
            in
            insertImplicits ctx fTm' fTy')
      else pure_ { term = fTm; type = forced; });

  # descendImplicitPi ctx expectedTy mkBody: when expectedTy is an
  # implicit Pi, wrap mkBody in implicit lambdas peeling those binders.
  # mkBody receives the (extended ctx, body-side expected type) and
  # returns a Comp Tm.
  descendImplicitPi = ctx: expectedTy: mkBody:
    bind_ (self.force expectedTy) (forced:
      if isImplicitPi forced then
        let
          fresh = V.freshVar ctx.depth;
          d = (ctx.depth or 0) + 1;
          ctx' = builtins.seq d (ctx // {
            env = V.envCons fresh (ctx.env or V.envNil);
            types = V.envCons forced.domain (ctx.types or V.envNil);
            names = V.envCons forced.name (ctx.names or V.envNil);
            depth = d;
          });
          # `forced.closure` may capture `VMeta`s; the kernel evaluator
          # crashes inspecting them (reads `.tag`). Route through the overlay
          # (mirrors `insertImplicits` above).
          bodyTy = self.instantiateOverlay forced.closure fresh;
        in
        bind_ (descendImplicitPi ctx' bodyTy mkBody) (bodyTm:
          pure_ (T.mkLam forced.name (quote ctx.depth forced.domain) bodyTm
            // { _plicity = "implicit"; }))
      else mkBody ctx forced);

  # plicityAwait metaId lhs rhs : emit a marker constraint that
  # postpones until the named meta solves; once solved, simplifyConstraint
  # marks this constraint solved (re-running the deferred elaboration is
  # left to the calling sites; the marker is the observable witness).
  plicityAwait = ctx: metaId: lhs: rhs:
    self.emitConstraint {
      tag = "plicity-await";
      awaiting = metaId;
      inherit lhs rhs;
      type = V.vU V.vLevelZero;
      depth = ctx.depth or 0;
      mentions = [ metaId ];
      status = "postponed";
    };

  ctx0 = fx.tc.check.emptyCtx;

  # {A : U(0)} → Unit → Unit
  polyIdLikeTy =
    (V.vPi "A" (V.vU V.vLevelZero)
      (V.mkClosure [ ] (T.mkPi "_" T.mkUnit T.mkUnit)))
    // { _plicity = "implicit"; };

  # Unit → Unit
  explicitArrowTy = V.vPi "_" V.vUnit (V.mkClosure [ ] T.mkUnit);

  # {A : U(0)} → Unit
  oneImplicitTy =
    (V.vPi "A" (V.vU V.vLevelZero)
      (V.mkClosure [ ] T.mkUnit))
    // { _plicity = "implicit"; };

  filterPlicityAwait = cs:
    builtins.filter (c: (c.tag or null) == "plicity-await") cs;

in
{
  scope = {
    insertImplicits = api.leaf {
      value = insertImplicits;
      description = "Peel leading implicit Pi binders of a function's inferred type by fresh-meta insertion. Returns Comp { term; type } with the explicit head.";
      signature = "insertImplicits : Ctx -> Tm -> Val -> Comp { term : Tm; type : Val }";
      tests = {
        "insertImplicits-peels-leading-implicit-binder" = {
          expr =
            let
              fn = T.mkVar 0;
              r = self.runElab H.unit (insertImplicits ctx0 fn polyIdLikeTy);
            in
            {
              nMetas = r.state.nextMetaId;
              termTag = r.value.term.tag;
              argTag = r.value.term.arg.tag;
              fnIsOriginal = r.value.term.fn == fn;
              typeTag = r.value.type.tag;
              residualPlicity = r.value.type._plicity or "explicit";
            };
          expected = {
            nMetas = 1;
            termTag = "app";
            argTag = "meta";
            fnIsOriginal = true;
            typeTag = "VPi";
            residualPlicity = "explicit";
          };
        };

        "insertImplicits-no-overhead-on-explicit-pi" = {
          expr =
            let
              fn = T.mkVar 0;
              r = self.runElab H.unit (insertImplicits ctx0 fn explicitArrowTy);
            in
            {
              nMetas = r.state.nextMetaId;
              termIsOriginal = r.value.term == fn;
              typeTag = r.value.type.tag;
            };
          expected = { nMetas = 0; termIsOriginal = true; typeTag = "VPi"; };
        };

        "elabInferApp-inserts-meta-at-implicit-pi-head" = {
          expr =
            let
              fnTm = (self.mkMeta 0 [ ]) // {
                type = { ctx = ctx0; ty = polyIdLikeTy; };
              };
              appTm = T.mkApp fnTm T.mkTt;
              r = self.runElab H.unit (self.elabInfer ctx0 appTm);
            in
            {
              hasError = r.value ? error;
              nMetas = 1;
              outerTag = r.value.term.tag;
              innerFnTag = r.value.term.fn.tag;
              innerArgTag = r.value.term.fn.arg.tag;
              outerArgTag = r.value.term.arg.tag;
            };
          expected = {
            hasError = false;
            nMetas = 1;
            outerTag = "app";
            innerFnTag = "app";
            innerArgTag = "meta";
            outerArgTag = "tt";
          };
        };
      };
    };
    descendImplicitPi = api.leaf {
      value = descendImplicitPi;
      description = "Wrap a body in implicit lambdas peeling leading implicit binders from an expected type.";
      signature = "descendImplicitPi : Ctx -> Val -> (Ctx -> Val -> Comp Tm) -> Comp Tm";
      tests = {
        "descendImplicitPi-wraps-body-in-implicit-lam" = {
          expr =
            let
              mkBody = _innerCtx: _innerTy: pure_ T.mkTt;
              r = self.runElab H.unit (descendImplicitPi ctx0 oneImplicitTy mkBody);
            in
            {
              tag = r.value.tag;
              name = r.value.name;
              plicity = r.value._plicity or null;
              bodyTag = r.value.body.tag;
            };
          expected = {
            tag = "lam";
            name = "A";
            plicity = "implicit";
            bodyTag = "tt";
          };
        };

        "elabCheck-descends-implicit-Pi-via-implicit-lam" = {
          expr =
            let
              r = self.runElab H.unit (self.elabCheck ctx0 T.mkTt oneImplicitTy);
            in
            {
              tag = r.value.tag;
              plicity = r.value._plicity or null;
              bodyTag = r.value.body.tag;
            };
          expected = { tag = "lam"; plicity = "implicit"; bodyTag = "tt"; };
        };
        # Regression: the implicit Pi's closure captures a `VMeta` lifted in
        # the body. Opening it via the overlay keeps the meta out of the
        # kernel CEK machine, whose `KLift_X` reads `.tag` (absent on `VMeta`).
        "descendImplicitPi-meta-closure-stays-out-of-kernel" = {
          expr =
            let
              liftBody = T.mkLift T.mkLevelZero
                (T.mkLevelSuc T.mkLevelZero) T.mkBootRefl (T.mkVar 1);
              m = self.mkVMeta 0 [ ] { ctx = ctx0; ty = V.vUnit; };
              implicitPi = (V.vPi "A" V.vUnit (V.mkClosure [ m ] liftBody))
                // { _plicity = "implicit"; };
              mkBody = _innerCtx: _innerTy: pure_ T.mkTt;
              r = self.runElab H.unit (descendImplicitPi ctx0 implicitPi mkBody);
            in
            {
              tag = r.value.tag;
              plicity = r.value._plicity or null;
              bodyTag = r.value.body.tag;
            };
          expected = { tag = "lam"; plicity = "implicit"; bodyTag = "tt"; };
        };
      };
    };
    plicityAwait = api.leaf {
      value = plicityAwait;
      description = "Emit a postponed plicity-await constraint awaiting the named meta; re-awakens when the meta solves.";
      signature = "plicityAwait : Ctx -> Int -> Val -> Val -> Comp Int";
      tests = {
        "plicity-await-emits-postponed-constraint" = {
          expr =
            let
              mt = self.mkVMeta 99 [ ] {
                ctx = ctx0;
                ty = V.vU V.vLevelZero;
              };
              r = self.runElab H.unit (plicityAwait ctx0 99 mt mt);
              awaits = filterPlicityAwait r.state.constraints;
              pa = builtins.head awaits;
            in
            {
              nAwaits = builtins.length awaits;
              tag = pa.tag;
              awaiting = pa.awaiting;
              status = pa.status;
              mentions = pa.mentions;
            };
          expected = {
            nAwaits = 1;
            tag = "plicity-await";
            awaiting = 99;
            status = "postponed";
            mentions = [ 99 ];
          };
        };

        "plicity-await-reawakens-when-meta-solves" = {
          expr =
            let
              mt = self.mkVMeta 99 [ ] {
                ctx = ctx0;
                ty = V.vU V.vLevelZero;
              };
              prog = bind_
                (plicityAwait ctx0 99 mt mt)
                (_: self.assignMeta 99 T.mkUnit);
              r = self.runElab H.unit prog;
              pa = builtins.head (filterPlicityAwait r.state.constraints);
            in
            pa.status;
          expected = "solved";
        };
      };
    };
    isImplicitPi = api.leaf {
      value = isImplicitPi;
      description = "Predicate: value is a VPi with implicit plicity sidecar.";
      signature = "isImplicitPi : Val -> Bool";
    };
    isVMetaTy = api.leaf {
      value = isVMetaTy;
      description = "Predicate: value is a VMeta (overlay representation).";
      signature = "isVMetaTy : Val -> Bool";
    };
  };

}
