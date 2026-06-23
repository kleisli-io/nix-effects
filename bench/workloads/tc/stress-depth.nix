# Stack-safety stress probes for the native structural walks that are not
# yet defunctionalized into heap machines.
#
# Each probe builds a depth-N term that drives one such walk and forces it.
# Above a measured crossover depth the walk exhausts the host call stack;
# below it the walk completes. These are TOTALITY probes, not alloc/cpu
# workloads: a probe is RED (host stack overflow) until its walk becomes
# heap-driven, then GREEN (bounded only by memory). They are deliberately
# absent from `meta.nix`, so the alloc/cpu runner never enumerates them;
# the stack-safety runner (`runner/stress.nix`) addresses them by path and
# classifies the subprocess exit.
#
# Each probe exposes two leaves:
#   control — a depth below the crossover; completes today (construction
#             integrity check — must stay GREEN).
#   witness — a depth past the crossover; overflows today, must go GREEN
#             once the walk is heap-driven.
#
# Crossover depths — first host stack overflow under the pinned evaluator
# (nix 2.31.4, max-call-depth=10000):
#   conv-spine            1700   neutral-spine convElim recursion
#   derive-sigma          <2000  deriveGo walkSigma per-Σ-level re-entry
#   derive-tree           <1000  deriveGo walkDatatype recAt field descent
#   derive-maybe          ~6000  deriveGo walkMaybe inner re-entry (1 bind/lvl)
#   derive-sigma-elab     <2000  deriveElaborate hoasAlg onSigma spine
#   sigma-verify          <2000  types Sigma.verify recursive validateAt
#   desc-fold             3000-4000  generic.desc.fold pure catamorphism over
#                                    a deep plus-spine description
#   desc-foldm            1000-2000  foldDescM monadic bind-thread re-entry
#   desc-para             1000-2000  paraDM paramorphic monadic re-entry
#   desc-path             1000-2000  foldDescWithPath bindP-per-descent re-entry
#   orn-diag              8000-10000 ornament algShapeDiagnosticRecordsAt
#                                    desc-shape diagnostic walk — a `++`-collecting
#                                    recursion over description structure, ~1 host
#                                    frame per description level; type-depth-bounded
#   render-value          3500   renderValue native field/list recursion
#   extract-inner         none ≤16000   mu decoder per-level .l walk — rec
#                                       field threads tyVal unchanged, O(1)/
#                                       level; GREEN guard
#   extract-sigma         3500   sigma decoder per-level .snd walk — each
#                                       layer instantiates a fresh type value,
#                                       O(depth) closure-instantiation chain
#   lower-infer           5000   lower dispatch on an inferred app spine
#   hoas-whnf             5000   hoasWhnf neutral app-spine .fn peel
#   elaborate-for-check  10000   elaborateForCheck pi/lam descent
#   eqdt-telescope       12000   peelTmTelescope EqDT-witness descent
#   deep-sigma           none ≤16000   sigma/pair descent (latent guard)
#   scan-prefix          none ≤16000   scanPrefixOf Pi-prefix peel — lazy
#                                       {pre;open} keeps host depth O(1);
#                                       latent guard
#   quote-level          none ≤16000   quote level-suc read-back — every arm
#                                       is a lazy `T.mkLevelSuc (quote …)`
#                                       constructor, O(1) host depth per level;
#                                       latent guard
#   quote-machine        none ≤16000   quote machine (runQuoteF) value-pair
#                                       read-back — iterative driver emits a
#                                       lazy `mkPair (quote …) (quote …)` per
#                                       step, O(1) host depth per level; latent
#                                       guard
#   ctx-depth-counter    none ≤16000   extend depth/eb counter chain — a
#                                       C-stack-only cost (max-call-depth
#                                       untouched); its ambient crossover is
#                                       too deep to gate here. The small-
#                                       thread-stack gate is the nix-unit
#                                       `stress-extend-deep-depth-flat-10000`
#                                       case (overflows a worker below 4000
#                                       without the eager force) plus a
#                                       `ulimit -s 2048` probe. Latent guard.
{ fx }:
let
  H = fx.tc.hoas;
  Q = fx.tc.quote;
  E = fx.tc.eval;
  Ex = fx.tc.elaborate;
  CH = fx.tc.check;
  V = fx.tc.value;
  renderValue = fx.src.diag.pretty.renderValue;
  inherit (H)
    nat forall sigma lam app ann eq zero succ refl reflDT pair maybe
    checkHoas elab datatype con recField implicitApp u;

  G = fx.tc.generic;
  GP = G.path.empty;
  dc = G.check.deriveCheck;
  de = G.check.deriveElaborate;
  T = fx.types;
  K = fx.src.kernel;
  DG = G.desc;
  runCollecting = comp:
    (fx.src.trampoline.handle { handlers = fx.effects.typecheck.collecting; state = [ ]; } comp).state;
  runStrict = comp:
    (fx.src.trampoline.handle { handlers = fx.effects.typecheck.strict; state = null; } comp).value;

  rng = n: builtins.genList (x: x) n;

  # neutral-spine conv: refl : Eq Nat s s with s = f(f(…(0))), f a bound var.
  convSpine = n:
    let
      ty = forall "f" (forall "_" nat (_: nat)) (f:
        let s = builtins.foldl' (acc: _: app f acc) zero (rng n); in eq nat s s);
      tm = lam "f" (forall "_" nat (_: nat)) (_: refl);
    in (checkHoas ty tm).tag;

  # renderValue on a depth-n tagged record (a deep quoted type's shape).
  renderValueP = n:
    let deepRec = builtins.foldl' (acc: _: { tag = "node"; child = acc; }) { tag = "leaf"; } (rng n);
    in builtins.stringLength (renderValue deepRec);

  # Force a decoded value's spine one level per genericClosure step: the loop
  # is heap-driven, so the host depth seen is exactly one `extractInner` WHNF
  # per layer. `seq`/`deepSeq` cannot isolate this — `seq` stops at the WHNF
  # head, `deepSeq` recurses the whole result on the host stack (its own
  # artifact). `field` selects the recursive child (`l` for mu, `snd` for
  # sigma).
  walkSpine = field: cmp: root: builtins.length (builtins.genericClosure {
    startSet = [{ key = 0; node = root; }];
    operator = item:
      let m = item.node; in
      if builtins.isAttrs m && cmp m
      then [{ key = item.key + 1; node = m.${field}; }]
      else [ ];
  });

  # extractInner mu decoder: a branching datatype (two rec fields ⇒ off the
  # linearChain fast-path) with a deep left spine. The rec-field threads the
  # type value unchanged, so each decoded layer is an O(1) lazy WHNF — the
  # per-level `.l` walk completes at any depth.
  extractInner = n:
    let
      D = datatype "Tree" [ (con "leaf" [ ]) (con "node" [ (recField "l") (recField "r") ]) ];
      deepVal = builtins.foldl' (acc: _: app (app D.node acc) D.leaf) D.leaf (rng n);
    in walkSpine "l" (m: (m._con or null) == "node") (Ex.verifyAndExtract D.T deepVal);

  # extractInner sigma decoder: a deep right-nested Sigma value, decoded and
  # walked one `.snd` level per step. Each snd layer threads a freshly
  # instantiated type value (`instantiate tyVal.closure val.fst`), so the
  # native decode builds an O(depth) closure-instantiation chain that
  # overflows on force — until the snd-spine decode is heap-driven.
  extractSigma = n:
    let
      sigTy = builtins.foldl' (acc: _: sigma "_" nat (_: acc)) nat (rng n);
      sigTm = builtins.foldl' (acc: _: pair zero acc) zero (rng n);
    in walkSpine "snd" (m: m ? snd) (Ex.verifyAndExtract sigTy sigTm);

  # lower dispatch on a deep UN-annotated (inferred) application spine.
  lowerInfer = n:
    let
      idFn = ann (lam "x" nat (x: x)) (forall "_" nat (_: nat));
      s = builtins.foldl' (acc: _: app idFn acc) zero (rng n);
    in (elab s).tag;

  # elaborateForCheck pi/lam descent: deep Pi type vs matching deep Lam term.
  elaborateForCheck = n:
    let
      ty = builtins.foldl' (acc: _: forall "_" nat (_: acc)) nat (rng n);
      tm = builtins.foldl' (acc: _: lam "_" nat (_: acc)) zero (rng n);
    in (checkHoas ty tm).tag;

  # peelAppSpine on a deep LEFT-nested app spine. Implicit apps over an
  # open head keep the infer skeleton clean at any depth, so `elab`
  # returns the rigid Tm without running the meta elaborator; the spine
  # length alone drives `peelAppSpine`, which `lower`'s app case forces
  # eagerly through `tryFlattenCtorChain`.
  lowerPeel = n:
    let
      head = lam "x" nat (x: x);
      s = builtins.foldl' (acc: _: implicitApp acc zero) head (rng n);
    in (elab s).tag;

  # deep Sigma/pair descent — no crossover observed ≤16000; a regression
  # guard that the sigma/pair check path stays bounded.
  deepSigma = n:
    let
      ty = builtins.foldl' (acc: _: sigma "_" nat (_: acc)) nat (rng n);
      tm = builtins.foldl' (acc: _: pair zero acc) zero (rng n);
    in (checkHoas ty tm).tag;

  # peelTmTelescope on the EqDT-witness path: a deep Π-telescope ending in
  # a 3-arg Eq spine makes checkHoas derive the shared Eq witnesses
  # (checkedEqWitnesses -> peelTmTelescope), which descends the kernel-built
  # `mkPi` Tm spine one binder per host frame. A `nat`-terminal telescope
  # skips this path entirely, so only the Eq terminal drives the descent.
  eqdtTelescope = n:
    let
      ty = builtins.foldl' (acc: _: forall "_" nat (_: acc)) (eq nat zero zero) (rng n);
      tm = builtins.foldl' (acc: _: lam "_" nat (_: acc)) refl (rng n);
    in (checkHoas ty tm).tag;

  # extend's cached depth/eb counters: N chained extends build an N-deep
  # `+1`/`or` thunk chain in `depth`/`eb`; forcing it (here `lookupType`'s
  # `ctx.depth` bound check) recurses N-deep on the native C-stack. extend
  # forces the counters eagerly, so the chain never forms. No crossover on
  # the ambient stack ≤16000 (see header).
  ctxDepthCounter = n:
    let
      deepCtx = builtins.foldl' (acc: _: CH.extend acc "x" V.vUnit) CH.emptyCtx (rng n);
    in builtins.seq deepCtx.depth (CH.lookupType deepCtx 0).tag;

  # hoasWhnf on a deep neutral app-spine type: bind f : nat -> … -> nat ->
  # U(0), then check against the body `f zero … zero`, a neutral type at
  # U(0). checkHoas type-checks the Pi (so elaborateForCheck/hoasEqBody
  # run), then weak-head-reduces the body, peeling the app spine's `.fn`
  # one host frame per layer. The neutral body has no closed inhabitant,
  # so checkHoas returns an Error after the walk; `.tag or "ok"` forces
  # the walk and tolerates that. Witness depth is bounded by the O(n²)
  # kernel pre-check, not the (now heap-driven) walk.
  hoasWhnfP = n:
    let
      arrTy = builtins.foldl' (acc: _: forall "_" nat (_: acc)) (u 0) (rng n);
      ty = forall "f" arrTy (f: builtins.foldl' (acc: _: app acc zero) f (rng n));
      tm = lam "f" arrTy (_: zero);
    in (checkHoas ty tm).tag or "ok";

  # scanPrefixOf on a deep Pi-telescope annotation in app-head (infer)
  # position: `(ann (λx:nat.x) (nat→ⁿnat)) zero`. The infer pre-scan runs
  # scanSigOf(ann) → scanPrefixOf, peeling the annotation's Pi prefix one
  # binder per layer. The lazy `{ pre; open }` result is forced
  # sequentially through its fields, so host depth stays O(1) — no
  # crossover ≤16000. Latent guard against a regression to eager peeling.
  scanPrefixP = n:
    let
      deepPi = builtins.foldl' (acc: _: forall "_" nat (_: acc)) nat (rng n);
      f = ann (lam "x" nat (x: x)) deepPi;
    in (elab (app f zero)).tag;

  # quote (tc/quote.nix) read-back of a deep level-suc value. Every recursive
  # arm is a lazy constructor (`T.mkLevelSuc (quote d v.pred)` etc.), so the
  # term spine is forced one `quote` call per genericClosure step — O(1) host
  # depth per level. Walked heap-driven via `walkSpine`, never `deepSeq`:
  # `deepSeq` would overflow on its own traversal of the resulting deep term,
  # not on quote. Latent guard against a regression to eager sub-quoting.
  quoteLevel = n:
    let deepLevel = builtins.foldl' (acc: _: V.vLevelSuc acc) V.vLevelZero (rng n);
    in walkSpine "pred" (m: (m.tag or null) == "level-suc") (Q.quote 0 deepLevel);

  # quote of a deep VPair value routes through the quote machine (`runQ`):
  # its tag is dispatched by the fuel-driven `runQuoteF` driver rather than the
  # `quote` fallback. The driver emits a lazy `mkPair (quote d v.fst)
  # (quote d v.snd)` per node, so the `.snd` spine forces one machine step per
  # genericClosure step — O(1) host depth per level. Latent guard that the
  # quote machine stays iterative.
  quoteMachinePair = n:
    let deepPair = builtins.foldl' (acc: _: V.vPair V.vTt acc) V.vTt (rng n);
    in walkSpine "snd" (m: (m.tag or null) == "pair") (Q.quote 0 deepPair);

  # deriveGo (tc/generic/check.nix) — the polymorphic structural walker.
  # Each arm re-enters `deriveGo` inside a bind continuation; on the
  # well-typed path `bind (pure x) k = k x` collapses, so the visit is host
  # recursion one frame per value level. walkElems is the only flat arm.

  # walkSigma: deep right-nested kernel Σ over a native {fst;snd} value.
  deriveSigma = n:
    let
      ty = builtins.foldl' (acc: _: sigma "_" nat (_: acc)) nat (rng n);
      val = builtins.foldl' (acc: _: { fst = 0; snd = acc; }) 0 (rng n);
    in builtins.length (runCollecting (dc ty GP val));

  # walkDatatype recAt: deep left-spine Tree native value.
  deriveTree = n:
    let
      TreeD = datatype "Tree" [ (con "leaf" [ ]) (con "node" [ (recField "l") (recField "r") ]) ];
      val = builtins.foldl' (acc: _: { _con = "node"; l = acc; r = { _con = "leaf"; }; }) { _con = "leaf"; } (rng n);
    in builtins.length (runCollecting (dc TreeD.T GP val));

  # walkMaybe: deep nested Maybe type, one bind per level (higher crossover).
  deriveMaybe = n:
    let ty = builtins.foldl' (acc: _: maybe acc) nat (rng n);
    in builtins.length (runCollecting (dc ty GP 0));

  # deriveElaborate / hoasAlg on a deep Σ — the elaboration path also
  # re-enters per level, building the `onSigma` HOAS spine.
  deriveSigmaElab = n:
    let
      ty = builtins.foldl' (acc: _: sigma "_" nat (_: acc)) nat (rng n);
      val = builtins.foldl' (acc: _: { fst = 0; snd = acc; }) 0 (rng n);
    in (H.elab (runStrict (de ty GP val))).tag or "ok";

  # types-layer Sigma.verify (dependent.nix:452): recursive `validateAt`
  # per Σ level; surfaces at hoas/lower.nix per-level lowering.
  sigmaVerify = n:
    let
      ty = builtins.foldl' (acc: _: T.Sigma { fst = T.Int; snd = _: acc; universe = 0; }) T.Int (rng n);
      val = builtins.foldl' (acc: _: { fst = 0; snd = acc; }) 0 (rng n);
    in builtins.length (runCollecting (ty.validate val));

  # desc catamorphisms (tc/generic/desc.nix) — native-recursive folds over
  # description structure. Each non-leaf arm re-enters the fold on a child
  # before combining, growing the host stack one frame per description level.
  # `deepDesc` is a right-nested binary-sum description of depth n (each layer
  # `plus descRet <inner>`), so the `plus` arm's right re-entry drives the
  # depth. `fold` is pure; the three monadic variants thread results through
  # `K.bind` (foldDescWithPath additionally brackets each descent with `bindP`).
  deepDesc = n: builtins.foldl' (acc: _: H.plus H.descRet acc) H.descRet (rng n);

  # Discharge a monadic desc-fold: the bindP blame/yield discipline
  # (foldDescWithPath), the deriveBounce stack bounce, and a typeError
  # surfacer. The gate handlers are pure, so only the bounce is exercised.
  runDesc = comp:
    (fx.src.trampoline.handle {
      state = { blame = CH._blame.empty; };
      handlers = CH._blame.handlers // CH._yield.handlers // {
        deriveBounce = { param, state }: { resume = param.run null; inherit state; };
        typeError = { param, state }: { abort = { err = CH._blame.fold state.blame param.error; }; inherit state; };
      };
    } comp).value;

  descFold = n:
    DG.foldDesc {
      ret = _: 1;
      arg = x: 1 + x.sample;
      "rec" = x: 1 + x.sub;
      pi = x: 1 + x.sub;
      plus = x: 1 + x.left + x.right;
    } (deepDesc n);

  descFoldM = n:
    runDesc (DG.foldDescM {
      ret = _: K.pure 1;
      "rec" = x: K.pure (1 + x.sub);
      plus = x: K.pure (1 + x.left + x.right);
      default = _: K.pure 0;
    } (deepDesc n));

  descPara = n:
    runDesc (DG.paraDM {
      ret = _: K.pure 1;
      "rec" = x: K.pure (1 + x.sub);
      plus = x: K.pure (1 + x.left + x.right);
      default = _: K.pure 0;
    } (deepDesc n));

  descPath = n:
    runDesc (DG.foldDescWithPath [ ] {
      ret = _: K.pure 1;
      "rec" = x: K.pure (1 + x.sub);
      plus = x: K.pure (1 + x.left + x.right);
      default = _: K.pure 0;
    } (deepDesc n));

  # ornament algShapeDiagnosticRecordsAt (tc/hoas/ornament.nix): the
  # algebra/description shape-checker native-recurses over description
  # structure, concatenating diagnostic-record lists with `++`. A right-nested
  # descPlus spine (`deepDesc`) + a structurally-matching algPlus spine drives
  # the `desc-plus-enc` arm's two-child re-entry one host frame per level. On a
  # matching pair every arm yields `[]`, so the forced result is `0`.
  ornDiagAlg = n:
    builtins.foldl' (acc: _: H.algPlus (H.algRet H.zero) acc) (H.algRet H.zero) (rng n);
  ornDiag = n:
    builtins.length (H.algOrnDiagnosticRecords { D = deepDesc n; algebra = ornDiagAlg n; });

  pair2 = build: control: witness: { control = build control; witness = build witness; };
in
{
  conv-spine = pair2 convSpine 1000 4000;
  render-value = pair2 renderValueP 2000 8000;
  extract-inner = pair2 extractInner 2000 8000;
  extract-sigma = pair2 extractSigma 2000 8000;
  lower-infer = pair2 lowerInfer 3000 16000;
  hoas-whnf = pair2 hoasWhnfP 2000 8000;
  elaborate-for-check = pair2 elaborateForCheck 6000 16000;
  lower-peel = pair2 lowerPeel 2000 10500;
  eqdt-telescope = pair2 eqdtTelescope 6000 16000;
  deep-sigma = { latent = deepSigma 16000; };
  scan-prefix = { latent = scanPrefixP 16000; };
  quote-level = { latent = quoteLevel 16000; };
  quote-machine = { latent = quoteMachinePair 16000; };
  ctx-depth-counter = { latent = ctxDepthCounter 16000; };

  derive-sigma = pair2 deriveSigma 1000 4000;
  derive-tree = pair2 deriveTree 250 4000;
  derive-maybe = pair2 deriveMaybe 2000 8000;
  derive-sigma-elab = pair2 deriveSigmaElab 1000 4000;
  sigma-verify = pair2 sigmaVerify 1000 4000;

  desc-fold = pair2 descFold 2000 8000;
  desc-foldm = pair2 descFoldM 1000 4000;
  desc-para = pair2 descPara 1000 4000;
  desc-path = pair2 descPath 1000 4000;

  orn-diag = pair2 ornDiag 6000 16000;
}
