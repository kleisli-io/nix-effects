# Defunctionalized CBN abstract machine for the kernel evaluator.
#
# Introduction forms construct Vals directly via smart helpers,
# passing sub-evaluations as Nix thunks. Frames exist only at
# demand points: elimination dispatch, binder closure capture,
# sidecar plumbing.
#
# State:
#   { mode = "Eval";  env; tm;  kont; fuel; }
#   { mode = "Apply"; val;      kont; fuel; }
#   { mode = "Done";  val; }
#
# `kont` is a cons-cell `null | { head; tail; }`. Driver:
# `genericClosure` + `foldl'`; the operator throws
# `"normalization budget exceeded"` on fuel exhaustion.
{ self, fx, ... }:

let
  val = fx.tc.value;
  term = fx.tc.term;
  inherit (val) mkClosure freshVar
    envCons envNth envLen envFromList
    vTt vUnit vEmpty vNe vNeSnoc vLam vPi vSigma vPair
    vBootSum vBootInl vBootInr vBootEq vBootRefl vFunext
    vSquash vSquashIntro
    vDescAt vMu vDescCon vDescConChain vU vLazyDescIndAccLayer
    vLevel vLevelZero vLevelSuc vLevelMax vLiftIntro
    vString vInt vFloat vAttrs vPath vDerivation vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vDerivationLit vFnLit vAnyLit
    eApp eFst eSnd eBootSumElim eBootJ eInterpD eAllD eEverywhereD eDescInd;
  vUZero = vU vLevelZero;

  # Kont cells are `{ head = frame; tail = kont; }` literals at every push
  # site, and machine states are `{ mode; ...; kont; fuel }` literals at every
  # transition: a named constructor would cost one curried application (Env +
  # call) per argument per step, which at ~1M machine steps per heavy workload
  # is a measurable share of the evaluator's allocation floor.

  # Force-required frames: each resume needs `state.val` forced to dispatch
  # on `.tag`. All other sub-Tm propagation goes through Nix-lazy thunks via
  # the local `ev` handle, mirroring HEAD's `mkValueF` byte-for-byte.
  kApp1              = env: argTm: { tag = "KApp1";              inherit env argTm; };
  kAppVV             = arg:        { tag = "KApp_VV";            inherit arg; };
  kFst               =             { tag = "KFst"; };
  kSnd               =             { tag = "KSnd"; };
  kBootSumElim_Scrut = env: tm:    { tag = "KBootSumElim_Scrut"; inherit env tm; };
  kBootJ_Scrut       = env: tm:    { tag = "KBootJ_Scrut";       inherit env tm; };

  kDescInd                = D: motive: step: i:
    { tag = "KDescInd";                inherit D motive step i; };
  kDescIndLayer_GotEvResult = step: i: d:
    { tag = "KDescIndLayer_GotEvResult"; inherit step i d; };
  kDescIndLinear_LazyBuild = chainFn: n: step:
    { tag = "KDescIndLinear_LazyBuild"; inherit chainFn n step; };
  kEverywhereD                       = L: I: K: X: M: ih: i: d:
    { tag = "KEverywhereD";                       inherit L I K X M ih i d; };
  kEverywhereD_ArgGotSubD            = L: I: K: X: M: ih: i: sndD:
    { tag = "KEverywhereD_ArgGotSubD";            inherit L I K X M ih i sndD; };
  kEverywhereD_RecGotIhHere          = L: I: K: X: M: ih: i: sndD: sub:
    { tag = "KEverywhereD_RecGotIhHere";          inherit L I K X M ih i sndD sub; };
  kEverywhereD_RecCombine            = ihHere:
    { tag = "KEverywhereD_RecCombine";            inherit ihHere; };
  kEverywhereD_PiCombine             = piLam:
    { tag = "KEverywhereD_PiCombine";             inherit piLam; };
  kEverywhereD_PlusStuck_GotAInterp  = L: I: K: X: M: ih: i: d: viewA: viewB:
    { tag = "KEverywhereD_PlusStuck_GotAInterp";  inherit L I K X M ih i d viewA viewB; };
  kEverywhereD_PlusStuck_GotBInterp  = L: I: K: X: M: ih: i: d: viewA: viewB: AInterp:
    { tag = "KEverywhereD_PlusStuck_GotBInterp";  inherit L I K X M ih i d viewA viewB AInterp; };
  kAllD                       = L: I: K: X: M: i: d:
    { tag = "KAllD";                       inherit L I K X M i d; };
  kAllD_ArgGotSubD            = L: I: K: X: M: i: sndD:
    { tag = "KAllD_ArgGotSubD";            inherit L I K X M i sndD; };
  kAllD_RecCombine            = sndD: sub: L: I: K: X: M: i:
    { tag = "KAllD_RecCombine";            inherit sndD sub L I K X M i; };
  kAllD_PlusStuck_GotAInterp  = L: I: K: X: M: i: d: viewA: viewB:
    { tag = "KAllD_PlusStuck_GotAInterp";  inherit L I K X M i d viewA viewB; };
  kAllD_PlusStuck_GotBInterp  = L: I: K: X: M: i: d: viewA: viewB: AInterp:
    { tag = "KAllD_PlusStuck_GotBInterp";  inherit L I K X M i d viewA viewB AInterp; };
  kInterpD             = L: I: X: i:        { tag = "KInterpD";             inherit L I X i; };
  kInterpD_PlusGotA    = L: I: X: i: B:     { tag = "KInterpD_PlusGotA";    inherit L I X i B; };
  kInterpD_PlusCombine = AInterp:           { tag = "KInterpD_PlusCombine"; inherit AInterp; };
  kDescConPeel_Start      = env: tm:
    { tag = "KDescConPeel_Start";      inherit env tm; };
  kDescConPeel_BaseI      = state:
    { tag = "KDescConPeel_BaseI";      inherit state; };
  kDescConPeel_BaseD      = state: baseI:
    { tag = "KDescConPeel_BaseD";      inherit state baseI; };
  kLiftElim_X          = lV: mV: eqV: AV:                              { tag = "KLiftElim_X";          inherit lV mV eqV AV; };
  kLift_X              = lV: mV: eqV:                                  { tag = "KLift_X";              inherit lV mV eqV; };
  kLiftIntro_X         = lV: mV: eqV: AV:                              { tag = "KLiftIntro_X";         inherit lV mV eqV AV; };
  kSquashElim_X        = AV: BV: fV:                                   { tag = "KSquashElim_X";        inherit AV BV fV; };
  kAbsurd_Term         = tyV:                                          { tag = "KAbsurd_Term";         inherit tyV; };
  kBootSumElim_ScrutV  = left: right: motive: onLeft: onRight:
    { tag = "KBootSumElim_ScrutV"; inherit left right motive onLeft onRight; };

  # Force-and-resume frames. When a handler needs `.tag` of a stored sub-Val,
  # it pushes a `kResume_<H>_<field>` capturing every other field of its
  # context plus the originally-consumed val, then Apply-modes on the sub-Val.
  # the driver step's Apply-mode VThunkTm peek transitions to Eval inside the same
  # driver; on return the resume handler rebuilds H with the forced field
  # substituted and re-delivers the consumed val. No fresh `runMachineF`.
  # Q→Eval→Q transition: forced val lands as state.val; resume pops itself
  # and switches state back to Q-Eval at binder depth `d`.
  kqResumeQuote   = d:               { tag = "KQResumeQuote";        inherit d; };
  kResume_KAllD_d        = L: I: K: X: M: i: D:
    { tag = "KResume_KAllD_d";        inherit L I K X M i D; };
  kResume_KEverywhereD_d = L: I: K: X: M: ih: i: D:
    { tag = "KResume_KEverywhereD_d"; inherit L I K X M ih i D; };

  # Helper dispatchers. Each runs the corresponding `desc.nix` helper under
  # the unified driver and delivers the result to the paired `*_Got*` resume
  # frame structurally seated immediately above on the kont. The inspected
  # value flows through `state.val` (forced by the driver step's Apply-mode peek
  # if needed); only `kPeelLiftIntroVal` carries an accumulator field.
  kDescView         = { tag = "KDescView";         };
  kSumPayloadView   = { tag = "KSumPayloadView";   };
  kPeelLiftIntroVal = rb: { tag = "KPeelLiftIntroVal"; rebuildAcc = rb; };

  # Continuations paired with `kDescView`: forced view arrives as state.val
  # (sentinel-wrapped); the resume restores the original handler context.
  kResume_KInterpD_GotView     = L: I: X: i:
    { tag = "KResume_KInterpD_GotView";     inherit L I X i; };
  kResume_KInterpD_view2_GotXj = L: I: X: i: sub:
    { tag = "KResume_KInterpD_view2_GotXj"; inherit L I X i sub; };
  kResume_KAllD_GotView        = L: I: K: X: M: i: d:
    { tag = "KResume_KAllD_GotView";        inherit L I K X M i d; };
  kResume_KAllD_GotFstD        = L: I: K: X: M: i: d: view:
    { tag = "KResume_KAllD_GotFstD";        inherit L I K X M i d view; };
  kResume_KAllD_GotSndD        = L: I: K: X: M: i: fstD: view:
    { tag = "KResume_KAllD_GotSndD";        inherit L I K X M i fstD view; };
  kResume_KEverywhereD_GotView = L: I: K: X: M: ih: i: d:
    { tag = "KResume_KEverywhereD_GotView"; inherit L I K X M ih i d; };
  kResume_KEverywhereD_GotFstD = L: I: K: X: M: ih: i: d: view:
    { tag = "KResume_KEverywhereD_GotFstD"; inherit L I K X M ih i d view; };
  kResume_KEverywhereD_GotSndD = L: I: K: X: M: ih: i: fstD: view:
    { tag = "KResume_KEverywhereD_GotSndD"; inherit L I K X M ih i fstD view; };
  kResume_KDescConPeel_GotView = state:
    { tag = "KResume_KDescConPeel_GotView"; inherit state; };

  # Continuations paired with `kSumPayloadView` at the `view.idx == 4`
  # branches of KAllD / KEverywhereD.
  kResume_KAllD_view4_GotSV        = L: I: K: X: M: i: viewA: viewB: d:
    { tag = "KResume_KAllD_view4_GotSV";        inherit L I K X M i viewA viewB d; };
  kResume_KEverywhereD_view4_GotSV = L: I: K: X: M: ih: i: viewA: viewB: d:
    { tag = "KResume_KEverywhereD_view4_GotSV"; inherit L I K X M ih i viewA viewB d; };

  # Self-pushing walker over an inr/inl spine. Each VBootInr step pushes
  # `kDecodeWalk (depth+1)` and re-enters with `node.val`; VBootInl delivers
  # `{ idx = depth; payload }` in a `VRawDecode` sentinel, depth == 4 a
  # terminal-case payload. `KResume_KDescView_GotDecode` is structurally
  # seated immediately above on the kont to consume the result.
  kDecodeWalk = depth: { tag = "KDecodeWalk"; inherit depth; };

  # Paired with `kDecodeWalk`. `meta` carries the descViewF body constants
  # computed once from the forced `D` in KDescView's entry (D, hasDescDescRef,
  # iLev_val, I_val, k_val, dDescL_val, label_val, conLabel_val); the resume
  # dispatches on decoded idx into the per-arm peek chain.
  kResume_KDescView_GotDecode = meta:
    { tag = "KResume_KDescView_GotDecode"; inherit meta; };

  # Per-idx peek chains replicating `descViewF`'s body. Each step forces the
  # next sub-Val via an Apply state (the driver step's Apply-mode VThunkTm peek does the
  # actual force); successors read `.tag` / `.fst` / `.snd` of the forced
  # value. lowerMeta calls go through `kLiftElim_X` pushes per the
  # public-leaf forcing rule.
  kResume_KDescView_Idx0_GotPayload = meta:
    { tag = "KResume_KDescView_Idx0_GotPayload"; inherit meta; };
  kResume_KDescView_Idx0_GotJ = meta:
    { tag = "KResume_KDescView_Idx0_GotJ"; inherit meta; };
  kResume_KDescView_Idx1_GotPayload = meta:
    { tag = "KResume_KDescView_Idx1_GotPayload"; inherit meta; };
  kResume_KDescView_Idx1_GotSnd = meta: payload:
    { tag = "KResume_KDescView_Idx1_GotSnd"; inherit meta payload; };
  kResume_KDescView_Idx1_GotSMeta = meta: tPayload:
    { tag = "KResume_KDescView_Idx1_GotSMeta"; inherit meta tPayload; };
  kResume_KDescView_Idx2_GotPayload = meta:
    { tag = "KResume_KDescView_Idx2_GotPayload"; inherit meta; };
  kResume_KDescView_Idx2_GotSnd = meta: payload:
    { tag = "KResume_KDescView_Idx2_GotSnd"; inherit meta payload; };
  kResume_KDescView_Idx2_GotJ = meta: sub:
    { tag = "KResume_KDescView_Idx2_GotJ"; inherit meta sub; };
  kResume_KDescView_Idx3_GotPayload = meta:
    { tag = "KResume_KDescView_Idx3_GotPayload"; inherit meta; };
  kResume_KDescView_Idx3_GotSnd = meta: payload:
    { tag = "KResume_KDescView_Idx3_GotSnd"; inherit meta payload; };
  kResume_KDescView_Idx3_GotSndSnd = meta: payload: psnd:
    { tag = "KResume_KDescView_Idx3_GotSndSnd"; inherit meta payload psnd; };
  kResume_KDescView_Idx3_GotSMeta = meta: psndFst: sub:
    { tag = "KResume_KDescView_Idx3_GotSMeta"; inherit meta psndFst sub; };
  kResume_KDescView_Idx3_GotFn = meta: sMeta: sub:
    { tag = "KResume_KDescView_Idx3_GotFn"; inherit meta sMeta sub; };
  kResume_KDescView_Idx4_GotPayload = meta:
    { tag = "KResume_KDescView_Idx4_GotPayload"; inherit meta; };
  kResume_KDescView_Idx4_GotSnd = meta: payload:
    { tag = "KResume_KDescView_Idx4_GotSnd"; inherit meta payload; };

  # Sum-payload walker. `KSumPayloadView` forces `d`; each successor forces
  # the next sub-Val (d.D, d.d, d.d.val) before reading its tag. The
  # terminal `GotField` composes the rebuild closure from the existing
  # `KPeelLiftIntroVal` walker's `VRawPeel`.
  kResume_KSumPayloadView_GotDDesc = d:
    { tag = "KResume_KSumPayloadView_GotDDesc"; inherit d; };
  kResume_KSumPayloadView_GotDD = d:
    { tag = "KResume_KSumPayloadView_GotDD"; inherit d; };
  kResume_KSumPayloadView_GotDDVal = d: dD:
    { tag = "KResume_KSumPayloadView_GotDDVal"; inherit d dD; };
  kResume_KSumPayloadView_GotField = d: dD: pairSnd:
    { tag = "KResume_KSumPayloadView_GotField"; inherit d dD pairSnd; };

  # Force a `VLazyDescIndAccLayer` Val by expanding into three kAppVV frames
  # on top of the unchanged kont (the current dispatch frame stays at the
  # head). After the three force-apps consume — applying step to (layer.i,
  # layer.d, vPair prevAcc vTt) — the layer's accumulator value (a VLam, or
  # another VLazyDescIndAccLayer that this same helper re-fires) lands as
  # `state.val` on the original frame, which then re-dispatches with the
  # resolved value. The cascade lives entirely in the driver's kont stack;
  # libnix sees one frame regardless of chain depth.
  forceLazyLayer = state:
    let fn = state.val; in
    { mode = "Apply"; val = fn.step; kont = ({ head = (kAppVV fn.i); tail = ({ head = (kAppVV fn.d); tail = ({ head = (kAppVV (vPair fn.prevAcc vTt)); tail = state.kont; }); }); }); fuel = state.fuel - 1; };

  # Defunctionalised VDescViewFn dispatch from `KApp1` / `KApp_VV`.
  # The "vapp" kind — the only shape whose body re-enters `runMachineF`
  # via `vAppF → instantiateF` — is resolved by frame-pushing
  # `kAppVV liftedArg` on `tPayload` and transitioning to Apply mode,
  # keeping the cascade inside the same driver. Other kinds are pure
  # value-constructor composition; resolve them synchronously through
  # the shared `applyDescViewFnByKindF` helper.
  applyDescViewFnArm = state: fn: arg:
    if fn.kind == "vapp" then
      let liftedArg =
        if fn.noLift then arg
        else self.vLiftIntroF fn.liftK fn.liftDDescL vBootRefl fn.liftSTy arg;
      in { mode = "Apply"; val = fn.tPayload; kont = ({ head = (kAppVV liftedArg); tail = state.kont.tail; }); fuel = state.fuel - 1; }
    else { mode = "Apply"; val = (self.applyDescViewFnByKindF state.fuel fn arg); kont = state.kont.tail; fuel = state.fuel - 1; };

  # Sub-evaluator handle for lazy sub-Tm thunks at introduction-form
  # call sites. Three tiers:
  #
  #   1. Atomic tags (literals, singletons, var lookup, `U(0)`) — Val
  #      produced inline; no driver, no recursion.
  #   2. Tags whose evaluation recurses through `eval` (application, let,
  #      the eliminator and desc-ind families) — wrapped as a deferred
  #      `VThunkTm { env; tm }`. Forced lazily at the consumer (eval-side
  #      driver-step Apply peek, quote-side `mkQEvalStep` peek, or
  #      `forceVal` outside the machine). Top-level results are forced by
  #      the driver's `Done` arm in `stepIf`, so external callers see
  #      non-VThunkTm Vals. The single driver loop handles their
  #      recursion iteratively, so libnix stack depth stays independent
  #      of user-recursion depth.
  #   3. Every other tag holds a bounded type/description/constructor
  #      position: its Val is built directly by the shared `eval*V`
  #      builders (the exact expressions the evalDispatch arms emit), so
  #      the result is concrete — Nix thunk-memoization classifies each
  #      description once — without paying a 2-step machine entry
  #      (transient `deferTm` record, `envFromList`, state sets, driver
  #      prologue) per force. `ann`'s passthrough case and the
  #      WHNF-inspected positions of `lift`/`lift-intro` force explicitly
  #      to preserve this tier's forced-to-concrete contract. `desc-con`
  #      stays on the machine — its peel cascade and cert handling live
  #      on the single driver path (cf. the measured rejection of a
  #      direct peel in eval/direct.nix) — except for the statically
  #      recognizable subsets handled by `evalDescConFastV` /
  #      `evalDescConPlainV` below.
  evDeferTags = {
    "app" = true; "let" = true; "fst" = true; "snd" = true;
    "absurd" = true; "boot-sum-elim" = true; "boot-j" = true;
    "squash-elim" = true; "lift-elim" = true; "str-eq" = true;
    "desc-ind" = true; "interp-d" = true; "all-d" = true;
    "everywhere-d" = true;
  };
  # Deferred-Tm record with a memoized force: `forced` is a lazy field,
  # so every external read-site force of the SAME record (core.nix
  # `forceVal`) shares one machine run instead of re-evaluating per
  # touch. In-driver consumption (driver-step Apply/Done peeks) stays
  # frame-based for fuel accounting.
  deferTm = env: tm: {
    tag = "VThunkTm"; inherit env tm;
    forced = self.runMachineF self.defaultFuel env tm;
  };

  ev = env: tm:
    let t = tm.tag; in
         if t == "var"            then
           # inlined envNth i≤7 — frame-cut, see value.nix; do not re-wrap
           (if tm.idx == 0 then env.head
            else if tm.idx == 1 then env.tail.head
            else if tm.idx == 2 then env.tail.tail.head
            else if tm.idx == 3 then env.tail.tail.tail.head
            else if tm.idx == 4 then env.tail.tail.tail.tail.head
            else if tm.idx == 5 then env.tail.tail.tail.tail.tail.head
            else if tm.idx == 6 then env.tail.tail.tail.tail.tail.tail.head
            else if tm.idx == 7 then env.tail.tail.tail.tail.tail.tail.tail.head
            else envNth env tm.idx)
    else if t == "lit-val"        then tm.val
    else if t == "level-zero"     then vLevelZero
    # The level sub-language is evaluated strictly: a Level Val must never
    # carry a VThunkTm, because conv.nix's `flattenLevel` walks the whole
    # level tree (pred/lhs/rhs) reading `.tag` and throws on VThunkTm.
    # Levels are shallow (depth independent of user-recursion N), so eager
    # recursion here costs O(1) and reintroduces no stack-depth hazard.
    else if t == "level-suc"      then vLevelSuc (ev env tm.pred)
    else if t == "level-max"      then vLevelMax (ev env tm.lhs) (ev env tm.rhs)
    else if t == "tt"             then vTt
    else if t == "unit"           then vUnit
    else if t == "empty"          then vEmpty
    else if t == "boot-refl"      then vBootRefl
    else if t == "funext"         then vFunext
    else if t == "level"          then vLevel
    else if t == "string"         then vString
    else if t == "int"            then vInt
    else if t == "float"          then vFloat
    else if t == "attrs"          then vAttrs
    else if t == "path"           then vPath
    else if t == "derivation"     then vDerivation
    else if t == "function"       then vFunction
    else if t == "any"            then vAny
    else if t == "string-lit"     then vStringLit tm.value
    else if t == "int-lit"        then vIntLit tm.value
    else if t == "float-lit"      then vFloatLit tm.value
    else if t == "attrs-lit"      then vAttrsLit
    else if t == "path-lit"       then vPathLit
    else if t == "derivation-lit" then vDerivationLit
    else if t == "fn-lit"         then vFnLit
    else if t == "any-lit"        then vAnyLit
    else if t == "U" && tm.level.tag == "level-zero" then vUZero
    else if evDeferTags ? ${t} then deferTm env tm
    else if t == "ann" then self.forceVal (evalAnnV env tm)
    else if t == "desc-con" then self.forceVal (deferTm env tm)
    else evDirectArms.${t} env tm;

  # Lazy `_descRef` finalizer: mirrors `core.nix:428-433`'s `evalDescRef`.
  # All fields stay as Nix thunks; consumers (typechecker) force on demand.
  evalDescRefLazy = env: ref: ref // {
    I = ev env ref.I;
    level = ev env ref.level;
    params = map (ev env) (ref.params or [ ]);
  };

  # Bounded-tier Val builders, shared by the evalDispatch arms below and
  # `ev`'s tier-3 routing: one expression per tag, closed over (env, tm)
  # only, so the in-driver and direct paths cannot drift. Each is exactly
  # the Val the 2-step machine run (Eval → Apply → Done) for that tag
  # produces.
  evalAnnV = env: tm:
    let
      hasMeta = tm ? _descRef || tm ? _label || tm ? _conLabel;
      v  = if hasMeta then self.forceVal (ev env tm.term) else ev env tm.term;
      v1 = if tm ? _descRef then v // { _descRef = evalDescRefLazy env tm._descRef; } else v;
      v2 = if tm ? _label    then v1 // { _label    = tm._label;    } else v1;
      v3 = if tm ? _conLabel then v2 // { _conLabel = tm._conLabel; } else v2;
    in v3;
  evalPiV = env: tm:
    let v = vPi tm.name (ev env tm.domain) (mkClosure env tm.codomain); in
    if tm ? _plicity then v // { _plicity = tm._plicity; } else v;
  evalLamV = env: tm:
    let v = vLam tm.name (ev env tm.domain) (mkClosure env tm.body); in
    if tm ? _plicity then v // { _plicity = tm._plicity; } else v;
  evalSigmaV = env: tm: vSigma tm.name (ev env tm.fst) (mkClosure env tm.snd);
  evalPairV = env: tm: vPair (ev env tm.fst) (ev env tm.snd);
  evalBootSumV = env: tm: vBootSum (ev env tm.left) (ev env tm.right);
  evalBootInlV = env: tm: vBootInl (ev env tm.left) (ev env tm.right) (ev env tm.term);
  evalBootInrV = env: tm: vBootInr (ev env tm.left) (ev env tm.right) (ev env tm.term);
  evalBootEqV = env: tm: vBootEq (ev env tm.type) (ev env tm.lhs) (ev env tm.rhs);
  evalSquashV = env: tm: vSquash (ev env tm.A);
  evalSquashIntroV = env: tm: vSquashIntro (ev env tm.a);
  evalMuV = env: tm: vMu (ev env tm.I) (ev env tm.D) (ev env tm.i);
  evalUV = env: tm:
    if tm.level.tag == "level-zero" then vUZero
    else vU (ev env tm.level);
  evalDescAtV = env: tm:
    let
      iLevV = if tm.iLev.tag == "level-zero" then vLevelZero else ev env tm.iLev;
      kV    = if tm.k.tag    == "level-zero" then vLevelZero else ev env tm.k;
    in vDescAt kV iLevV (ev env tm.I);
  evalOpaqueLamV = env: tm: val.vOpaqueLam tm._fnBox (ev env tm.piTy);
  evalDescDescAppV = env: tm:
    let iLevV = if tm.iLev.tag == "level-zero" then vLevelZero else ev env tm.iLev;
    in self.mkDescDescAppVF self.defaultFuel iLevV (ev env tm.I) (ev env tm.L);
  evalCanonAppV = env: tm:
    self.mkCanonAppVF self.defaultFuel tm.id (map (ev env) tm.params) (ev env tm.body);
  evalDescConChainV = env: tm:
    let
      outerDV  = ev env tm.outerD;
      leftV    = ev env tm.payloadLeft;
      rightV   = ev env tm.payloadRight;
      baseDV   = ev env tm.base.D;
      baseIV   = if tm.base.i.tag == "tt" then vTt else ev env tm.base.i;
      baseDdV  = ev env tm.base.d;
      baseVal  = vDescCon baseDV baseIV baseDdV;
      layerVals = map (l: {
        i     = if l.i.tag == "tt" then vTt else ev env l.i;
        heads = map (ev env) l.heads;
        cert  = null;
      }) tm.layers;
      finalOuterI =
        if layerVals == [ ] then baseIV
        else (builtins.head layerVals).i;
    in vDescConChain outerDV finalOuterI tm.payloadTag
      leftV rightV layerVals baseVal;
  # Certified desc-con chain-prepend fast path, gated once in the
  # `evalDispatch` desc-con arm — the funnel every desc-con eval path
  # reaches (`ev` tier-3 and the hybrid front end's punt both enter the
  # driver, whose dispatch arm tries it; gating those callers directly
  # was measured and rejected: the redundant guard call taxes every
  # non-firing desc-con eval, double-guarding the ev route, for ~2
  # saved entry steps per firing). For the statically recognizable safe subset —
  # certified linearChain ctor whose payload Tm is literally the
  # cert-side boot-inl/inr over its nFields pair spine ending in
  # (lit-val tail, boot-refl), with the forced tail already chain-form
  # under the matching payload tag — the peel cascade's output is one
  # layer prepended onto the tail's layers, fully determined without
  # running the machine. Mirrors the KDescConPeel_Start → BaseD output
  # exactly: the Tm-level peel cannot extend past a lit-val tail (n=0),
  # `forceAndPeelChainV`'s peel1 trusts payload shape alone (no D-compat
  # check), layer heads are the same lazy `ev` thunks the payload's
  # VPair fields would carry, payloadTag/left/right are reused from the
  # tail (denotationally equal to the view sides, view-free), and the D
  # slot defers as a memoized VThunkTm (legal for stored sub-Vals —
  # read sites force), skipping the per-layer D eval and the
  # descView/`_descRef` forces entirely. Returns null outside the
  # subset; callers fall through to the machine path.
  # Spine walkers for `evalDescConFastV`, hoisted so the per-eval guard
  # allocates no closures. `descConSpineTail` hops `k` pair-snd links to
  # the terminal pair and returns its lit-val tail Tm (or null);
  # `descConSpineField` reads the j-th data-field Tm of the same spine.
  descConSpineTail = k: p:
    if p.tag != "pair" then null
    else if k == 0 then
      if p.snd.tag == "boot-refl" && p.fst.tag == "lit-val" then p.fst else null
    else descConSpineTail (k - 1) p.snd;
  descConSpineField = j: p:
    if j == 0 then p.fst else descConSpineField (j - 1) p.snd;

  # Guard structure: cascaded early exits, cheapest reads first, each
  # `let` entered only when the previous guard passed — the common
  # rejection paths allocate nothing beyond the call itself.
  evalDescConFastV = env: tm:
    if tm.i.tag != "tt" || !(tm ? _descConCert) then null
    else
      let certLinear = tm._descConCert.ref.linearChain or null; in
      if certLinear == null then null
      else if tm.d.tag != (if certLinear.side == "inl" then "boot-inl" else "boot-inr") then null
      else
        let tailTm = descConSpineTail certLinear.dataFieldCount tm.d.term; in
        if tailTm == null then null
        else
          let tailV = self.forceVal tailTm.val; in
          if (tailV._shape or null) != "linearChain"
             || (tailV._payloadTag or null)
                != (if certLinear.side == "inl" then "VBootInl" else "VBootInr")
          then null
          else
            vDescConChain (deferTm env tm.D) vTt
              tailV._payloadTag tailV._payloadLeft tailV._payloadRight
              ([{
                i = vTt;
                heads = builtins.genList
                  (j: ev env (descConSpineField j tm.d.term))
                  certLinear.dataFieldCount;
                cert = tm._descConCert;
              }] ++ self.effLayers tailV)
              tailV._base;

  # Nocert `descDesc`-headed plain build, the second statically
  # recognizable subset gated in the dispatch arm (same funnel rationale
  # as `evalDescConFastV` above; the arm tries it after the
  # chain-prepend rejects, behind a `D.tag` guard).
  # When the head Tm is literally `desc-desc-app`, its Val is
  # `mkDescDescAppVF`'s `_canonRef` shell (eval/desc.nix) — never
  # `_descRef` — so the peel cascade's classify has no ref source;
  # absent a certified linearChain it falls back to `linearProfileF`
  # over `descDesc`'s own view sides, which is not a linear profile
  # (multiple constructors, mixed recursive positions — a fixed
  # property of the desc universe encoding). classify is therefore
  # null, the peel cannot walk (n = 0, chain form off), and the
  # cascade's output is exactly the plain cert-preserving `vDescCon` —
  # fully determined without the machine entry, `kDescView`, profile
  # walks, or peel. The D slot is `evalDescDescAppV`'s shell — the same
  # concrete `_canonRef` record the cascade's D eval produces (readers
  # peek `.D` fields without a force, so a deferred slot is NOT legal
  # here; the shell itself is one record with lazy fields). `i`/`d`
  # force to WHNF as the machine runs would have, with sub-fields
  # staying lazy; nested desc-cons in the payload re-enter this arm on
  # force. Certified-linearChain Tms keep a non-null classify (chain
  # territory) and stay on the cascade. Returns null outside the
  # subset.
  evalDescConPlainV = env: tm:
    if (tm._descConCert.ref.linearChain or null) != null then null
    else
      let
        v = vDescCon (evalDescDescAppV env tm.D)
          (if tm.i.tag == "tt" then vTt else self.forceVal (ev env tm.i))
          (self.forceVal (ev env tm.d));
      in
      if tm ? _descConCert then v // { _descConCert = tm._descConCert; } else v;

  # `vLiftF` reads `A.tag` and `vLiftIntroF` reads `a.tag`/`a.spine`; the
  # kont appliers receive those positions machine-driven to WHNF, so the
  # direct arms force them explicitly (same leaves, same forcing depth).
  evalLiftV = env: tm:
    let
      lV = if tm.l.tag == "level-zero" then vLevelZero else ev env tm.l;
      mV = if tm.m.tag == "level-zero" then vLevelZero else ev env tm.m;
    in self.vLiftF lV mV (ev env tm.eq) (self.forceVal (ev env tm.A));
  evalLiftIntroV = env: tm:
    let
      lV = if tm.l.tag == "level-zero" then vLevelZero else ev env tm.l;
      mV = if tm.m.tag == "level-zero" then vLevelZero else ev env tm.m;
    in self.vLiftIntroF lV mV (ev env tm.eq) (ev env tm.A)
      (self.forceVal (ev env tm.a));

  # `ev` tier-3 routing table. `ann` is routed separately in `ev` (its
  # passthrough case needs a forceVal the in-driver arm must not pay);
  # `lift`/`lift-intro` appear here only — their in-driver dispatch arms
  # keep the kont path so a sub-descent stays inside the running driver.
  evDirectArms = {
    "pi" = evalPiV; "lam" = evalLamV; "sigma" = evalSigmaV;
    "pair" = evalPairV; "boot-sum" = evalBootSumV;
    "boot-inl" = evalBootInlV; "boot-inr" = evalBootInrV;
    "boot-eq" = evalBootEqV; "squash" = evalSquashV;
    "squash-intro" = evalSquashIntroV; "mu" = evalMuV;
    "U" = evalUV; "desc" = evalDescAtV; "opaque-lam" = evalOpaqueLamV;
    "desc-desc-app" = evalDescDescAppV; "canon-app" = evalCanonAppV;
    "desc-con-chain" = evalDescConChainV;
    "lift" = evalLiftV; "lift-intro" = evalLiftIntroV;
  };

  evalDispatch = {
    # `var`: inlined envNth i≤7 (frame-cut, see value.nix); do not re-wrap.
    "var" = state: { mode = "Apply"; val =
      (if state.tm.idx == 0 then state.env.head
       else if state.tm.idx == 1 then state.env.tail.head
       else if state.tm.idx == 2 then state.env.tail.tail.head
       else if state.tm.idx == 3 then state.env.tail.tail.tail.head
       else if state.tm.idx == 4 then state.env.tail.tail.tail.tail.head
       else if state.tm.idx == 5 then state.env.tail.tail.tail.tail.tail.head
       else if state.tm.idx == 6 then state.env.tail.tail.tail.tail.tail.tail.head
       else if state.tm.idx == 7 then state.env.tail.tail.tail.tail.tail.tail.tail.head
       else envNth state.env state.tm.idx); kont = state.kont; fuel = state.fuel - 1; };

    "unit"           = state: { mode = "Apply"; val = vUnit; kont = state.kont; fuel = state.fuel - 1; };
    "tt"             = state: { mode = "Apply"; val = vTt; kont = state.kont; fuel = state.fuel - 1; };
    "empty"          = state: { mode = "Apply"; val = vEmpty; kont = state.kont; fuel = state.fuel - 1; };
    "boot-refl"      = state: { mode = "Apply"; val = vBootRefl; kont = state.kont; fuel = state.fuel - 1; };
    "funext"         = state: { mode = "Apply"; val = vFunext; kont = state.kont; fuel = state.fuel - 1; };
    "level"          = state: { mode = "Apply"; val = vLevel; kont = state.kont; fuel = state.fuel - 1; };
    "level-zero"     = state: { mode = "Apply"; val = vLevelZero; kont = state.kont; fuel = state.fuel - 1; };
    "string"         = state: { mode = "Apply"; val = vString; kont = state.kont; fuel = state.fuel - 1; };
    "int"            = state: { mode = "Apply"; val = vInt; kont = state.kont; fuel = state.fuel - 1; };
    "float"          = state: { mode = "Apply"; val = vFloat; kont = state.kont; fuel = state.fuel - 1; };
    "attrs"          = state: { mode = "Apply"; val = vAttrs; kont = state.kont; fuel = state.fuel - 1; };
    "path"           = state: { mode = "Apply"; val = vPath; kont = state.kont; fuel = state.fuel - 1; };
    "derivation"     = state: { mode = "Apply"; val = vDerivation; kont = state.kont; fuel = state.fuel - 1; };
    "function"       = state: { mode = "Apply"; val = vFunction; kont = state.kont; fuel = state.fuel - 1; };
    "any"            = state: { mode = "Apply"; val = vAny; kont = state.kont; fuel = state.fuel - 1; };
    "string-lit"     = state: { mode = "Apply"; val = (vStringLit state.tm.value); kont = state.kont; fuel = state.fuel - 1; };
    "int-lit"        = state: { mode = "Apply"; val = (vIntLit state.tm.value); kont = state.kont; fuel = state.fuel - 1; };
    "float-lit"      = state: { mode = "Apply"; val = (vFloatLit state.tm.value); kont = state.kont; fuel = state.fuel - 1; };
    "attrs-lit"      = state: { mode = "Apply"; val = vAttrsLit; kont = state.kont; fuel = state.fuel - 1; };
    "path-lit"       = state: { mode = "Apply"; val = vPathLit; kont = state.kont; fuel = state.fuel - 1; };
    "derivation-lit" = state: { mode = "Apply"; val = vDerivationLit; kont = state.kont; fuel = state.fuel - 1; };
    "fn-lit"         = state: { mode = "Apply"; val = vFnLit; kont = state.kont; fuel = state.fuel - 1; };
    "any-lit"        = state: { mode = "Apply"; val = vAnyLit; kont = state.kont; fuel = state.fuel - 1; };
    "lit-val"        = state: { mode = "Apply"; val = state.tm.val; kont = state.kont; fuel = state.fuel - 1; };

    # `let` and `ann` are propagating-only dispatchers — no kont frame.
    # `let`: HEAD threads the binding as a thunk into env[0] and continues
    # evaluation of body in-place; the let's Val IS the body's Val.
    # `ann`: HEAD merges sidecars onto a thunk-Val via `//`; no field is
    # forced at eval time (typechecker reads `_descRef` etc. later).
    "let"   = state: { mode = "Eval"; env = ({ head = (ev state.env) state.tm.val; tail = state.env; }); tm = state.tm.body; kont = state.kont; fuel = state.fuel - 1; };
    # Meta-bearing anns wrap descriptions (shallow, always inspected).
    # The builder forces to WHNF before gluing the sidecar so it lands on
    # the real Val, not a VThunkTm wrapper — `forceVal`/the driver step
    # discard wrapper attrs when unwrapping a thunk, which would silently
    # drop `_descRef`/`_label`/`_conLabel` the typechecker reads later.
    "ann"   = state: { mode = "Apply"; val = (evalAnnV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    # Binder domains/fst and pair components are all propagated as lazy
    # thunks: their consumers (closure body, projection, conv) force on
    # demand. Matches HEAD's `vLam tm.name (ev tm.domain) (mkClosure ...)`.
    "pi"    = state: { mode = "Apply"; val = (evalPiV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "lam"   = state: { mode = "Apply"; val = (evalLamV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "sigma" = state: { mode = "Apply"; val = (evalSigmaV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    # `app` forces fn (need .tag for dispatch); arg is propagated as a
    # caller-env thunk into VLam closure / VDescViewFn / VNe spine.
    "app"   = state: { mode = "Eval"; env = state.env; tm = state.tm.fn; kont = { head = (kApp1  state.env state.tm.arg); tail = state.kont; }; fuel = state.fuel - 1; };
    "fst"   = state: { mode = "Eval"; env = state.env; tm = state.tm.pair; kont = { head = kFst; tail = state.kont; }; fuel = state.fuel - 1; };
    "snd"   = state: { mode = "Eval"; env = state.env; tm = state.tm.pair; kont = { head = kSnd; tail = state.kont; }; fuel = state.fuel - 1; };

    "boot-sum-elim" = state: { mode = "Eval"; env = state.env; tm = state.tm.scrut; kont = { head = (kBootSumElim_Scrut state.env state.tm); tail = state.kont; }; fuel = state.fuel - 1; };
    "boot-j"        = state: { mode = "Eval"; env = state.env; tm = state.tm.eq; kont = { head = (kBootJ_Scrut       state.env state.tm); tail = state.kont; }; fuel = state.fuel - 1; };

    "pair"         = state: { mode = "Apply"; val = (evalPairV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "boot-sum"     = state: { mode = "Apply"; val = (evalBootSumV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "boot-inl"     = state: { mode = "Apply"; val = (evalBootInlV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "boot-inr"     = state: { mode = "Apply"; val = (evalBootInrV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "boot-eq"      = state: { mode = "Apply"; val = (evalBootEqV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "squash"       = state: { mode = "Apply"; val = (evalSquashV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "squash-intro" = state: { mode = "Apply"; val = (evalSquashIntroV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    "level-suc"    = state: { mode = "Apply"; val = (vLevelSuc ((ev state.env) state.tm.pred)); kont = state.kont; fuel = state.fuel - 1; };
    "level-max"    = state: { mode = "Apply"; val = (vLevelMax ((ev state.env) state.tm.lhs) ((ev state.env) state.tm.rhs)); kont = state.kont; fuel = state.fuel - 1; };
    "mu"           = state: { mode = "Apply"; val = (evalMuV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };

    "U" = state: { mode = "Apply"; val = (evalUV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };

    "desc" = state: { mode = "Apply"; val = (evalDescAtV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };

    "lift" = state:
      let
        lV = if state.tm.l.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.l;
        mV = if state.tm.m.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.m;
      in { mode = "Eval"; env = state.env; tm = state.tm.A; kont = { head = (kLift_X lV mV ((ev state.env) state.tm.eq)); tail = state.kont; }; fuel = state.fuel - 1; };

    "lift-intro" = state:
      let
        lV = if state.tm.l.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.l;
        mV = if state.tm.m.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.m;
      in { mode = "Eval"; env = state.env; tm = state.tm.a; kont = { head = (kLiftIntro_X lV mV ((ev state.env) state.tm.eq) ((ev state.env) state.tm.A)); tail = state.kont; }; fuel = state.fuel - 1; };

    "opaque-lam" = state: { mode = "Apply"; val = (evalOpaqueLamV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
    # `vStrEq` forces both operands to WHNF internally before reading their
    # tag/level, so passing lazy thunks here is safe (string operands are
    # atomic — forcing is O(1) in user-recursion depth).
    "str-eq" = state: { mode = "Apply"; val = (self.vStrEq ((ev state.env) state.tm.lhs) ((ev state.env) state.tm.rhs)); kont = state.kont; fuel = state.fuel - 1; };

    "lift-elim" = state:
      let
        lV = if state.tm.l.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.l;
        mV = if state.tm.m.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.m;
      in { mode = "Eval"; env = state.env; tm = state.tm.x; kont = { head = (kLiftElim_X lV mV ((ev state.env) state.tm.eq) ((ev state.env) state.tm.A)); tail = state.kont; }; fuel = state.fuel - 1; };

    "squash-elim" = state:
      { mode = "Eval"; env = state.env; tm = state.tm.x; kont = { head = (kSquashElim_X ((ev state.env) state.tm.A) ((ev state.env) state.tm.B) ((ev state.env) state.tm.f)); tail = state.kont; }; fuel = state.fuel - 1; };

    "absurd" = state: { mode = "Eval"; env = state.env; tm = state.tm.term; kont = { head = (kAbsurd_Term ((ev state.env) state.tm.type)); tail = state.kont; }; fuel = state.fuel - 1; };

    "interp-d" = state:
      let
        levelV = if state.tm.level.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.level;
        IV = (ev state.env) state.tm.I;
        XV = (ev state.env) state.tm.X;
        iV = (ev state.env) state.tm.i;
      in { mode = "Eval"; env = state.env; tm = state.tm.D; kont = { head = (kInterpD levelV IV XV iV); tail = state.kont; }; fuel = state.fuel - 1; };

    "all-d" = state:
      let
        LV = if state.tm.level.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.level;
        KV = if state.tm.K.tag     == "level-zero" then vLevelZero else (ev state.env) state.tm.K;
        IV = (ev state.env) state.tm.I;
        XV = (ev state.env) state.tm.X;
        MV = (ev state.env) state.tm.M;
        iV = (ev state.env) state.tm.i;
        dV = (ev state.env) state.tm.d;
      in { mode = "Eval"; env = state.env; tm = state.tm.D; kont = { head = (kAllD LV IV KV XV MV iV dV); tail = state.kont; }; fuel = state.fuel - 1; };

    "everywhere-d" = state:
      let
        LV = if state.tm.level.tag == "level-zero" then vLevelZero else (ev state.env) state.tm.level;
        KV = if state.tm.K.tag     == "level-zero" then vLevelZero else (ev state.env) state.tm.K;
        IV  = (ev state.env) state.tm.I;
        XV  = (ev state.env) state.tm.X;
        MV  = (ev state.env) state.tm.M;
        ihV = (ev state.env) state.tm.ih;
        iV  = (ev state.env) state.tm.i;
        dV  = (ev state.env) state.tm.d;
      in { mode = "Eval"; env = state.env; tm = state.tm.D; kont = { head = (kEverywhereD LV IV KV XV MV ihV iV dV); tail = state.kont; }; fuel = state.fuel - 1; };

    "desc-ind" = state:
      let
        DV    = (ev state.env) state.tm.D;
        motV  = (ev state.env) state.tm.motive;
        stepV = (ev state.env) state.tm.step;
        iV    = (ev state.env) state.tm.i;
      in { mode = "Eval"; env = state.env; tm = state.tm.scrut; kont = { head = (kDescInd DV motV stepV iV); tail = state.kont; }; fuel = state.fuel - 1; };

    "desc-desc-app" = state: { mode = "Apply"; val = (evalDescDescAppV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };

    "canon-app" = state: { mode = "Apply"; val = (evalCanonAppV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };

    # Fast-subset order matters: `evalDescConFastV`'s guards read only
    # `i.tag` and cert presence — its firing case never forces the D Tm
    # (the chain output defers it), so the `D.tag` read for the plain
    # build must come after its rejection. The plain build forces the D
    # Tm anyway (it builds the head shell), and rejected entries pay
    # the read the cascade's own D eval subsumes. The plain try's `let`
    # is entered only behind the `D.tag` guard, so the chain-prepend
    # and cascade routes allocate exactly one binding, as before.
    "desc-con" = state:
      let fast = evalDescConFastV state.env state.tm; in
      if fast != null
      then { mode = "Apply"; val = fast; kont = state.kont; fuel = state.fuel - 1; }
      else if state.tm.D.tag == "desc-desc-app"
      then
        let plain = evalDescConPlainV state.env state.tm; in
        if plain != null
        then { mode = "Apply"; val = plain; kont = state.kont; fuel = state.fuel - 1; }
        else { mode = "Eval"; env = state.env; tm = state.tm.D; kont = { head = (kDescConPeel_Start state.env state.tm); tail = state.kont; }; fuel = state.fuel - 1; }
      else { mode = "Eval"; env = state.env; tm = state.tm.D; kont = { head = (kDescConPeel_Start state.env state.tm); tail = state.kont; }; fuel = state.fuel - 1; };

    # Canonical flat-form chain. No peel — the Tm IS the canonical
    # form. Layers iterate via `map` (libnix-iterative); sub-Val
    # evals are lazy thunks (`ev env`), so the machine emits this
    # in a single apply step with O(1) frame depth.
    "desc-con-chain" = state: { mode = "Apply"; val = (evalDescConChainV state.env state.tm); kont = state.kont; fuel = state.fuel - 1; };
  };

  applyDispatch = {
    # `KApp1` subsumes the former two-step `evalThen-fn → KApp2`. fn is
    # forced (needed for dispatch); arg stays as a caller-env Nix thunk and
    # is threaded into VLam closure env / VDescViewFn dispatch / VNe spine
    # without forcing — matches the value-level `vAppF` byte-for-byte.
    "KApp1" = state:
      let fn = state.val; in
      if fn.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else
        let argThunk = ev state.kont.head.env state.kont.head.argTm; in
        if fn.tag == "VDescViewFn" then applyDescViewFnArm state fn argThunk
        else if fn.tag == "VLam" then { mode = "Eval"; env = ({ head = argThunk; tail = fn.closure.env; }); tm = fn.closure.body; kont = state.kont.tail; fuel = state.fuel - 1; }
        else if fn.tag == "VNe"  then { mode = "Apply"; val = (vNeSnoc fn (eApp argThunk)); kont = state.kont.tail; fuel = state.fuel - 1; }
        else throw "tc: vApp on non-function (tag=${fn.tag})";

    "KApp_VV" = state:
      let fn = state.val; arg = state.kont.head.arg; in
      if fn.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if fn.tag == "VDescViewFn" then applyDescViewFnArm state fn arg
      else if fn.tag == "VLam" then { mode = "Eval"; env = ({ head = arg; tail = fn.closure.env; }); tm = fn.closure.body; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if fn.tag == "VNe"  then { mode = "Apply"; val = (vNeSnoc fn (eApp arg)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vApp on non-function (tag=${fn.tag})";

    "KFst" = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if state.val.tag == "VPair" then { mode = "Apply"; val = state.val.fst; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if state.val.tag == "VNe" then { mode = "Apply"; val = (vNeSnoc state.val eFst); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vFst on non-pair (tag=${state.val.tag})";

    "KSnd" = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if state.val.tag == "VPair" then { mode = "Apply"; val = state.val.snd; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if state.val.tag == "VNe" then { mode = "Apply"; val = (vNeSnoc state.val eSnd); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vSnd on non-pair (tag=${state.val.tag})";

    # Eliminator-scrutinee resumes: each forces the scrut for tag dispatch,
    # then on the stuck-VNe path threads the remaining sub-Tms into the
    # spine as Nix-lazy thunks (mirrors HEAD's `vBootSumElimF`/`vBootJ` on
    # `VNe`, which pass thunk args into `eBootSumElim`/`eBootJ` directly).
    "KBootSumElim_Scrut" = state:
      let tm = state.kont.head.tm; env = state.kont.head.env; in
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if state.val.tag == "VBootInl" then
        { mode = "Eval"; env = env; tm = tm.onLeft; kont = ({ head = (kAppVV state.val.val); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if state.val.tag == "VBootInr" then
        { mode = "Eval"; env = env; tm = tm.onRight; kont = ({ head = (kAppVV state.val.val); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if state.val.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc state.val
          (eBootSumElim
            (ev env tm.left)
            (ev env tm.right)
            (ev env tm.motive)
            (ev env tm.onLeft)
            (ev env tm.onRight))); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${state.val.tag})";

    "KBootJ_Scrut" = state:
      let tm = state.kont.head.tm; env = state.kont.head.env; in
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if state.val.tag == "VBootRefl" then { mode = "Eval"; env = env; tm = tm.base; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if state.val.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc state.val
          (eBootJ
            (ev env tm.type)
            (ev env tm.lhs)
            (ev env tm.motive)
            (ev env tm.base)
            (ev env tm.rhs))); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vBootJ on non-eq (tag=${state.val.tag})";

    "KLiftElim_X"   = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else { mode = "Apply"; val = (self.vLiftElimF state.kont.head.lV state.kont.head.mV state.kont.head.eqV state.kont.head.AV state.val); kont = state.kont.tail; fuel = state.fuel - 1; };
    # `vLiftF` reads `A.tag` for the inner-Lift composition rule and
    # `vLiftIntroF` reads `a.tag`/`a.spine` for the η-collapse; the inspected
    # argument is driven to WHNF here (delivered as `state.val`) before the leaf,
    # per the public-leaf forcing rule.
    "KLift_X"       = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else { mode = "Apply"; val = (self.vLiftF state.kont.head.lV state.kont.head.mV state.kont.head.eqV state.val); kont = state.kont.tail; fuel = state.fuel - 1; };
    "KLiftIntro_X"  = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else { mode = "Apply"; val = (self.vLiftIntroF state.kont.head.lV state.kont.head.mV state.kont.head.eqV state.kont.head.AV state.val); kont = state.kont.tail; fuel = state.fuel - 1; };
    "KSquashElim_X" = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else { mode = "Apply"; val = (self.vSquashElimF self.defaultFuel state.kont.head.AV state.kont.head.BV state.kont.head.fV state.val); kont = state.kont.tail; fuel = state.fuel - 1; };
    "KAbsurd_Term"  = state:
      if state.val.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else { mode = "Apply"; val = (self.vAbsurd state.kont.head.tyV state.val); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KBootSumElim_ScrutV" = state:
      let k = state.kont.head; scrut = state.val; in
      if scrut.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if scrut.tag == "VBootInl" then
        { mode = "Apply"; val = k.onLeft; kont = ({ head = (kAppVV scrut.val); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if scrut.tag == "VBootInr" then
        { mode = "Apply"; val = k.onRight; kont = ({ head = (kAppVV scrut.val); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if scrut.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc scrut
          (eBootSumElim k.left k.right k.motive k.onLeft k.onRight)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${scrut.tag})";

    "KInterpD" = state:
      let
        k = state.kont.head;
        D = state.val;
        L = k.L; I = k.I; X = k.X; i = k.i;
      in
      if D.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc D (eInterpD L I X i)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if D.tag == "VDescCon" then
        { mode = "Apply"; val = (self.interpDDirectF state.fuel L I D X i); kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = D; kont = ({ head = kDescView; tail = ({ head = (kResume_KInterpD_GotView L I X i); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KInterpD_PlusGotA" = state:
      let k = state.kont.head; AInterp = state.val; in
      { mode = "Apply"; val = k.B; kont = ({ head = (kInterpD k.L k.I k.X k.i); tail = ({ head = (kInterpD_PlusCombine AInterp); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KInterpD_PlusCombine" = state:
      { mode = "Apply"; val = (vBootSum state.kont.head.AInterp state.val); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KAllD" = state:
      let
        k = state.kont.head;
        D = state.val;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i; d = k.d;
      in
      if D.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc D (eAllD L I K X M i d)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = D; kont = ({ head = kDescView; tail = ({ head = (kResume_KAllD_GotView L I K X M i d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KAllD_ArgGotSubD" = state:
      let k = state.kont.head; in
      { mode = "Apply"; val = state.val; kont = ({ head = (kAllD k.L k.I k.K k.X k.M k.i k.sndD); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KAllD_RecCombine" = state:
      let
        k = state.kont.head;
        Mjfd = state.val;
        ihClosure = mkClosure [ k.L k.I k.K k.X k.M k.i k.sndD k.sub ]
          (term.mkAllD (term.mkVar 1) (term.mkVar 2) (term.mkVar 8)
            (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
            (term.mkVar 6) (term.mkVar 7));
      in { mode = "Apply"; val = (vSigma "_" Mjfd ihClosure); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KAllD_PlusStuck_GotAInterp" = state:
      let k = state.kont.head; AInterp = state.val; in
      { mode = "Apply"; val = k.viewB; kont = ({ head = (kInterpD k.L k.I k.X k.i); tail = ({ head = (kAllD_PlusStuck_GotBInterp k.L k.I k.K k.X k.M k.i k.d k.viewA k.viewB AInterp); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KAllD_PlusStuck_GotBInterp" = state:
      let
        k = state.kont.head;
        BInterp = state.val;
        AInterp = k.AInterp;
        motive = vLam "_" (vBootSum AInterp BInterp) (mkClosure [ k.K ]
          (term.mkU (term.mkVar 1)));
        onLeftLam = vLam "a" AInterp
          (mkClosure [ k.L k.I k.K k.X k.M k.i k.viewA ]
            (term.mkAllD (term.mkVar 1) (term.mkVar 2) (term.mkVar 7)
              (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
              (term.mkVar 6) (term.mkVar 0)));
        onRightLam = vLam "b" BInterp
          (mkClosure [ k.L k.I k.K k.X k.M k.i k.viewB ]
            (term.mkAllD (term.mkVar 1) (term.mkVar 2) (term.mkVar 7)
              (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
              (term.mkVar 6) (term.mkVar 0)));
      in { mode = "Apply"; val = k.d; kont = ({ head = (kBootSumElim_ScrutV AInterp BInterp motive onLeftLam onRightLam); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KEverywhereD" = state:
      let
        k = state.kont.head;
        D = state.val;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i; d = k.d;
      in
      if D.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc D (eEverywhereD L I K X M ih i d)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = D; kont = ({ head = kDescView; tail = ({ head = (kResume_KEverywhereD_GotView L I K X M ih i d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KEverywhereD_ArgGotSubD" = state:
      let k = state.kont.head; in
      { mode = "Apply"; val = state.val; kont = ({ head = (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i k.sndD); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KEverywhereD_RecGotIhHere" = state:
      let k = state.kont.head; ihHere = state.val; in
      { mode = "Apply"; val = k.sub; kont = ({ head = (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i k.sndD); tail = ({ head = (kEverywhereD_RecCombine ihHere); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KEverywhereD_RecCombine" = state:
      { mode = "Apply"; val = (vPair state.kont.head.ihHere state.val); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KEverywhereD_PiCombine" = state:
      { mode = "Apply"; val = (vPair state.kont.head.piLam state.val); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KEverywhereD_PlusStuck_GotAInterp" = state:
      let k = state.kont.head; AInterp = state.val; in
      { mode = "Apply"; val = k.viewB; kont = ({ head = (kInterpD k.L k.I k.X k.i); tail = ({ head = (kEverywhereD_PlusStuck_GotBInterp k.L k.I k.K k.X k.M k.ih k.i k.d k.viewA k.viewB AInterp); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KEverywhereD_PlusStuck_GotBInterp" = state:
      let
        k = state.kont.head;
        BInterp = state.val;
        AInterp = k.AInterp;
        motive = vLam "_" (vBootSum AInterp BInterp) (mkClosure [ k.K ]
          (term.mkU (term.mkVar 1)));
        onLeftLam = vLam "a" AInterp
          (mkClosure [ k.L k.I k.K k.X k.M k.ih k.i k.viewA ]
            (term.mkEverywhereD (term.mkVar 1) (term.mkVar 2) (term.mkVar 8)
              (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
              (term.mkVar 6) (term.mkVar 7) (term.mkVar 0)));
        onRightLam = vLam "b" BInterp
          (mkClosure [ k.L k.I k.K k.X k.M k.ih k.i k.viewB ]
            (term.mkEverywhereD (term.mkVar 1) (term.mkVar 2) (term.mkVar 8)
              (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
              (term.mkVar 6) (term.mkVar 7) (term.mkVar 0)));
      in { mode = "Apply"; val = k.d; kont = ({ head = (kBootSumElim_ScrutV AInterp BInterp motive onLeftLam onRightLam); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KDescInd" = state:
      let
        k = state.kont.head;
        scrut = state.val;
        D = k.D; motive = k.motive; step = k.step; i = k.i;
        f = state.fuel;
      in
      if scrut.tag == "VLazyDescIndAccLayer" then forceLazyLayer state
      else if scrut.tag == "VNe" then
        { mode = "Apply"; val = (vNeSnoc scrut (eDescInd D motive step i)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if scrut.tag == "VDescCon" then
        let
          # A computed motive arrives as a deferred Tm; force at the point of
          # demand (the memoized `forced` field makes this one shared machine
          # run). `I` stays lazy, so entries that never read the domain —
          # the cert path, undemanded ihVal/muFam binders — pay nothing.
          # Eager frame-level forcing here measured +2…3.8‰ envs/functionCalls
          # on desc-ind-heavy workloads.
          I = let m = self.forceVal motive; in
              if m.tag != "VLam"
              then throw "tc: vDescInd on VDescCon requires VLam motive (got ${m.tag})"
              else m.domain;
          ihValRaw = vLam "j" I
            (mkClosure [ step motive D I ]
              (term.mkLam "x"
                (term.mkMu (term.mkVar 4) (term.mkVar 3) (term.mkVar 0))
                (term.mkDescInd (term.mkVar 4) (term.mkVar 3) (term.mkVar 2)
                  (term.mkVar 1) (term.mkVar 0))));
          muFam = vLam "j" I
            (mkClosure [ I D ]
              (term.mkMu (term.mkVar 1) (term.mkVar 2) (term.mkVar 0)));
          ihVal = ihValRaw // {
            _ihShortcut = { inherit D motive step muFam I; };
          };
          # Cert path: ctorMeta + !hasIH triggers triple-apply step on (i, d, vTt).
          cert = scrut._descConCert or null;
          ref = if cert == null then null else cert.ref;
          ctorMeta =
            if ref == null
              || (cert.kind or null) != "datatype-con-payload"
              || !(ref ? constructors)
              || cert.ctor >= builtins.length ref.constructors
            then null
            else builtins.elemAt ref.constructors cert.ctor;
          hasIH =
            ctorMeta != null
            && builtins.any
              (kk: kk == "recAt" || kk == "pi" || kk == "piAt" || kk == "piD" || kk == "piDAt")
              (ctorMeta.fieldKinds or [ ]);
          certApplies = ctorMeta != null && !hasIH;
        in
        if certApplies then
          # vAppF (vAppF (vAppF step scrut.i) scrut.d) vTt
          { mode = "Apply"; val = step; kont = ({ head = (kAppVV scrut.i); tail = ({ head = (kAppVV scrut.d); tail = ({ head = (kAppVV vTt); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; }
        # Chain-form: synthesize the per-layer chain directly from
        # `_layers`/`_base` via the lazy-build kont. Per-layer
        # `.d` references the next item lazily — never forced unless
        # step recurses into the rec position (atypical; IH covers it).
        else if (scrut._shape or null) == "linearChain" then
          let
            fullLayers = scrut._layers;
            layersOff = scrut._layersOff or 0;
            chainBase = scrut._base;
            nLay = (builtins.length fullLayers) - layersOff;
            layerAt = idx: builtins.elemAt fullLayers (layersOff + idx);
            buildInner = hs: tail:
              if hs == [ ] then tail
              else vPair (builtins.head hs) (buildInner (builtins.tail hs) tail);
            wrapPayload = inner:
              if scrut._payloadTag == "VBootInr"
              then vBootInr scrut._payloadLeft scrut._payloadRight inner
              else if scrut._payloadTag == "VBootInl"
              then vBootInl scrut._payloadLeft scrut._payloadRight inner
              else throw "tc.descInd: chain-form payloadTag must be VBootInl/VBootInr (got ${scrut._payloadTag})";
            # Chain-form sub-vals for each level: outermost (idx=0) carries
            # the full chain, innermost (idx=nLay) is the base wrapped as a
            # 0-layer chain-form. These are what step bodies see when they
            # extract the rec-position from layer.d (e.g. predNat, vtail);
            # returning chain-form sub-vals preserves encoding through
            # projection-like eliminators. The base must also be chain-form
            # so that step bodies returning the base case (vtail on a
            # singleton vec) match the direct-construction encoding.
            chainSubVal = idx:
              # O(1) predecessor: share `fullLayers`, advance the offset
              # instead of copying via `builtins.tail`. `effLayers` slices the
              # shared array on cold reads; re-entry into this branch reads the
              # advanced offset directly. Base case (idx == nLay) yields offset
              # `layersOff + nLay`, which `effLayers` slices to `[ ]`.
              if idx == nLay then
                (vDescConChain scrut.D chainBase.i
                  scrut._payloadTag scrut._payloadLeft scrut._payloadRight
                  fullLayers chainBase) // { _layersOff = layersOff + nLay; }
              else
                (vDescConChain scrut.D (layerAt idx).i
                  scrut._payloadTag scrut._payloadLeft scrut._payloadRight
                  fullLayers chainBase) // { _layersOff = layersOff + idx; };
            # Per-layer synthesis on demand (a function, not `builtins.genList`):
            # genList would allocate O(nLay) list elements + thunk Values per
            # invocation, and a diagonal recursion (decideLeNat N N) re-enters
            # this branch O(N) times with nLay = N…1 ⇒ O(N²) allocation, even
            # though `buildFrom`'s lazy spine forces only O(1) layers per entry.
            # As a function each call costs O(1) and runs only for forced layers
            # ⇒ O(N) total.
            synthChainFn = idx:
              if idx == nLay then { val = chainBase; }
              else
                let layer = layerAt idx;
                    recVal = chainSubVal (idx + 1);
                    dVal = wrapPayload
                      (buildInner layer.heads (vPair recVal vBootRefl));
                in { val = {
                       tag = "VDescCon";
                       D = scrut.D;
                       i = layer.i;
                       d = dVal;
                     }; };
          in
          if nLay == 0 then
            { mode = "Apply"; val = D; kont = ({ head = (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal chainBase.i chainBase.d); tail = ({ head = (kDescIndLayer_GotEvResult step chainBase.i chainBase.d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
          else if nLay > f then throw "normalization budget exceeded"
          else
            { mode = "Apply"; val = D; kont = ({ head = (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal chainBase.i chainBase.d); tail = ({ head = (kDescIndLayer_GotEvResult step chainBase.i chainBase.d); tail = ({ head = (kDescIndLinear_LazyBuild synthChainFn nLay step); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; }
        else
          # Fallback: vDescIndFLayer(D, motive, step, ihVal, muFam, I, i, scrut.d).
          { mode = "Apply"; val = D; kont = ({ head = (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal i scrut.d); tail = ({ head = (kDescIndLayer_GotEvResult step i scrut.d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else throw "tc: vDescInd on non-mu (tag=${scrut.tag})";

    "KDescIndLayer_GotEvResult" = state:
      # vAppF (vAppF (vAppF step i) d) evResult — fires layer.i first.
      let k = state.kont.head; evResult = state.val; in
      { mode = "Apply"; val = k.step; kont = ({ head = (kAppVV k.i); tail = ({ head = (kAppVV k.d); tail = ({ head = (kAppVV evResult); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; };

    "KDescIndLinear_LazyBuild" = state:
      # `state.val` is `baseResult` — the deepest layer's already-forced accumulator,
      # produced by the preceding KDescIndLayer_GotEvResult. Build the chain
      # top-down with a LAZY spine: `vLazyDescIndAccLayer` stores `prevAcc`
      # unforced, so `buildFrom 0` allocates only the topmost layer; deeper
      # layers materialize on demand when the cascade forces `prevAcc` (via
      # `forceLazyLayer`). A genuine recursion forces the whole chain (identical
      # to an eager build); a non-recursive eliminator (e.g. a one-level case
      # whose step ignores the IH) forces only the top, so the chain costs O(1)
      # instead of O(depth). Each layer's body — `step layer.i layer.d
      # (vPair prevAcc vTt)` — is never fired here.
      let
        k = state.kont.head;
        baseResult = state.val;
        buildFrom = idx:
          if idx == k.n then baseResult
          else
            let layer = (k.chainFn idx).val; in
            vLazyDescIndAccLayer k.step layer.i layer.d (buildFrom (idx + 1));
      in
      { mode = "Apply"; val = (buildFrom 0); kont = state.kont.tail; fuel = state.fuel - 1; };

    # dVal arrives via tm.D through the machine. classify/chain/peel
    # are pure Tm/Val walks. sameD's conv fallback and LayerI's
    # wrapPayload evalTm are sub-driver re-entries.
    "KDescConPeel_Start" = state:
      { mode = "Apply"; val = state.val; kont = ({ head = kDescView; tail = ({ head = (kResume_KDescConPeel_GotView { env = state.kont.head.env; tm = state.kont.head.tm; }); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KDescConPeel_GotView" = state:
      let
        env  = state.kont.head.state.env;
        tm   = state.kont.head.state.tm;
        dVal = state.val.D;
        f    = self.defaultFuel;
        cert       = tm._descConCert or null;
        certRef    = if cert    == null then null else cert.ref;
        certLinear = if certRef == null then null else certRef.linearChain or null;
        dRef    = dVal._descRef or null;
        dLinear = if dRef == null then null else dRef.linearChain or null;
        sameCertRef = other:
          certRef != null
          && other != null
          && (other.kind    or null) == (certRef.kind    or null)
          && (other.name    or null) == (certRef.name    or null)
          && (other.arity   or null) == (certRef.arity   or null)
          && (other.indexed or null) == (certRef.indexed or null)
          && builtins.length (other.params or [ ]) == builtins.length (certRef.params or [ ])
          && (other.linearChain or null) == certLinear;
        certClassify =
          if certLinear == null then null
          else { side = certLinear.side; fieldCount = certLinear.dataFieldCount; ctor = certLinear.ctor; certified = true; };
        refClassify =
          if dLinear == null then null
          else { side = dLinear.side; fieldCount = dLinear.dataFieldCount; ctor = dLinear.ctor; };
        refDeclinesLinear =
          (certRef != null && certLinear == null)
          || (dRef != null && dLinear == null);
        plusSides =
          let view = state.val.view; in
          if view != null && view.idx == 4
          then { A = view.A; B = view.B; }
          else null;
        classify =
          if certClassify != null then certClassify
          else if refClassify != null then refClassify
          else if refDeclinesLinear then null
          else if plusSides == null then null
          else
            let
              pA = self.linearProfileF f plusSides.A;
              pB = self.linearProfileF f plusSides.B;
            in
            if pA != null && pB == null then { profile = pA; side = "inl"; }
            else if pB != null && pA == null then { profile = pB; side = "inr"; }
            else null;
        profile = if classify == null then [ ] else classify.profile;
        nFields =
          if classify == null then 0
          else classify.fieldCount or (builtins.length profile);
        depth = envLen env;
        # Sub-driver re-entry.
        sameD = node:
          if classify ? certified then
            let nodeCert = node._descConCert or null; in
            nodeCert != null
            && (nodeCert.kind or null) == "datatype-con-payload"
            && nodeCert.ctor == classify.ctor
            && sameCertRef nodeCert.ref
          else if node.D == tm.D then true
          else fx.tc.conv.conv depth (self.evalF f env node.D) dVal;
        collectPairs = inner:
          let
            isRetLeaf = p:
              p.tag == "boot-refl"
              || (p.tag == "lift-intro" && p.a.tag == "boot-refl");
            collect = i: p: acc:
              if i == nFields then
                if p.tag != "pair" then null
                else if !(isRetLeaf p.snd) then null
                else if p.fst.tag != "desc-con" then null
                else { heads = acc; tail = p.fst; }
              else
                if p.tag != "pair" then null
                else collect (i + 1) p.snd (acc ++ [ p.fst ]);
          in
          collect 0 inner [ ];
        walkPayload = payload:
          if classify == null then null
          else
            let
              sv = self.sumPayloadTmView payload;
              inner =
                if sv == null || sv.side != classify.side
                then null
                else collectPairs sv.value;
            in
            if inner == null then null
            else inner // { rebuildVal = sv.rebuildVal; };
        peel = node:
          if classify == null then null
          else if node.tag != "desc-con" then null
          else if !(sameD node) then null
          else walkPayload node.d;
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = tm; peeled = peel tm; }];
          operator = item:
            if item.peeled == null then [ ]
            else
              let val_ = item.peeled.tail; in
              [{ key = item.key + 1; val = val_; peeled = peel val_; }];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        topPeel = if n >= 1 then (builtins.elemAt chain 0).peeled else null;
        withCert = node: iVal: dPayload:
          let raw = vDescCon dVal iVal dPayload; in
          if node ? _descConCert
          then raw // { _descConCert = node._descConCert; }
          else raw;
        chainForm = classify != null && plusSides != null;
        payloadInfo =
          if !chainForm then null
          else {
            tag = if classify.side == "inl" then "VBootInl" else "VBootInr";
            left = plusSides.A;
            right = plusSides.B;
          };
        # `peelState`, not `state`: a let-rec binding named `state` would
        # shadow the machine-state arm parameter across the whole let body.
        peelState = {
          inherit env tm chain n base topPeel withCert dVal chainForm payloadInfo nFields;
        };
      in
        if n > f then throw "normalization budget exceeded"
        else if base.i.tag == "tt"
        then { mode = "Eval"; env = env; tm = base.d; kont = ({ head = (kDescConPeel_BaseD peelState vTt); tail = state.kont.tail; }); fuel = state.fuel - 1; }
        else { mode = "Eval"; env = env; tm = base.i; kont = ({ head = (kDescConPeel_BaseI peelState); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KDescConPeel_BaseI" = state:
      let s = state.kont.head.state; in
      { mode = "Eval"; env = s.env; tm = s.base.d; kont = ({ head = (kDescConPeel_BaseD s state.val); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KDescConPeel_BaseD" = state:
      let
        s = state.kont.head.state;
        baseVal = s.withCert s.base state.kont.head.baseI state.val;
      in
        if s.chainForm then
          let
            tmLayers = builtins.genList
              (k:
                let
                  layerItem = builtins.elemAt s.chain k;
                  layerTm   = layerItem.val;
                in {
                  i =
                    if layerTm.i.tag == "tt" then vTt
                    else self.evalF self.defaultFuel s.env layerTm.i;
                  heads = map
                    (h: self.evalF self.defaultFuel s.env h)
                    layerItem.peeled.heads;
                  cert = layerTm._descConCert or null;
                })
              s.n;
            # Val-level canonicalization: when the Tm-level peel terminates at
            # a runtime `var` whose bound Val is itself a recursive-side ctor
            # (the typical `step ih` result during descInd reduction), recover
            # the remaining layers and flatten any nested chain base at the Val
            # level. Without it descInd yields a degenerate n=0 chain whose
            # `_base` is a non-base ctor, breaking Q.nf idempotency and
            # structural equality with directly constructed values.
            chainNF = self.forceAndPeelChainV s.payloadInfo.tag s.nFields baseVal;
            allLayers = tmLayers ++ chainNF.layers;
            finalBase = chainNF.base;
            finalOuterI =
              if allLayers == [ ] then finalBase.i
              else (builtins.head allLayers).i;
          in
            { mode = "Apply"; val = (vDescConChain s.dVal finalOuterI
              s.payloadInfo.tag s.payloadInfo.left s.payloadInfo.right
              allLayers finalBase); kont = state.kont.tail; fuel = state.fuel - 1; }
        # When `classify != null` (peel can walk) but `chainForm` is false
        # (`plusSides == null` — Desc has no sum-shaped descView even though
        # cert/ref says linearChain), `n` cannot exceed 0 in practice. The
        # full suite empirically confirms this invariant; the assert documents
        # it and traps any future regression.
        else if s.n == 0 then { mode = "Apply"; val = baseVal; kont = state.kont.tail; fuel = state.fuel - 1; }
        else throw "tc: KDescConPeel_BaseD non-chainForm n>=1 path reached (n=${toString s.n})";

    # Resume handlers: rebuild the original frame with the previously-forced
    # sub-Val substituted in, then deliver the captured originally-consumed
    # val. The handler above re-fires with the field now non-VThunkTm.
    "KResume_KAllD_d" = state:
      let k = state.kont.head; forcedD = state.val; in
      { mode = "Apply"; val = k.D; kont = ({ head = (kAllD k.L k.I k.K k.X k.M k.i forcedD); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KEverywhereD_d" = state:
      let k = state.kont.head; forcedD = state.val; in
      { mode = "Apply"; val = k.D; kont = ({ head = (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i forcedD); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    # Continuation of `KAllD` / `KEverywhereD` view.idx == 4 after the
    # `kSumPayloadView` dispatcher has run on a (pre-forced) `d`.
    # `state.val` is the VRawSV wrapper; `k.d` is the forced sum value used
    # for the VNe fallback spine and the throw-tag diagnostic.
    "KResume_KAllD_view4_GotSV" = state:
      let k = state.kont.head; sv = state.val.sv; in
      if sv != null then
        if sv.side == "inl"
        then { mode = "Apply"; val = k.viewA; kont = ({ head = (kAllD k.L k.I k.K k.X k.M k.i sv.value); tail = state.kont.tail; }); fuel = state.fuel - 1; }
        else { mode = "Apply"; val = k.viewB; kont = ({ head = (kAllD k.L k.I k.K k.X k.M k.i sv.value); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if k.d.tag == "VNe" then
        { mode = "Apply"; val = k.viewA; kont = ({ head = (kInterpD k.L k.I k.X k.i); tail = ({ head = (kAllD_PlusStuck_GotAInterp k.L k.I k.K k.X k.M k.i k.d k.viewA k.viewB); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else throw "tc: vAllD on plus with non-sum d (tag=${k.d.tag})";

    "KResume_KEverywhereD_view4_GotSV" = state:
      let k = state.kont.head; sv = state.val.sv; in
      if sv != null then
        if sv.side == "inl"
        then { mode = "Apply"; val = k.viewA; kont = ({ head = (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i sv.value); tail = state.kont.tail; }); fuel = state.fuel - 1; }
        else { mode = "Apply"; val = k.viewB; kont = ({ head = (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i sv.value); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else if k.d.tag == "VNe" then
        { mode = "Apply"; val = k.viewA; kont = ({ head = (kInterpD k.L k.I k.X k.i); tail = ({ head = (kEverywhereD_PlusStuck_GotAInterp k.L k.I k.K k.X k.M k.ih k.i k.d k.viewA k.viewB); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else throw "tc: vEverywhereD on plus with non-sum d (tag=${k.d.tag})";

    # Continuation of `KInterpD` after `kDescView` has run on the original
    # descriptor. `state.val` is the VRawView wrapper carrying `view` and the
    # (forced) `D` used in the throw diagnostic.
    "KResume_KInterpD_GotView" = state:
      let
        k = state.kont.head;
        view = state.val.view; D = state.val.D;
        L = k.L; I = k.I; X = k.X; i = k.i;
      in
      if view == null then throw "tc: vInterpD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        let
          iLev = view.iLev or vLevelZero;
          retLevel = self.levelMaxOpt L iLev;
        in { mode = "Apply"; val = (self.vLiftF iLev retLevel vBootRefl (vBootEq I view.j i)); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if view.idx == 1 then
        let
          ihClosure = mkClosure [ view.tFn L I X i ]
            (term.mkInterpD (term.mkVar 2) (term.mkVar 3)
              (term.mkApp (term.mkVar 1) (term.mkVar 0))
              (term.mkVar 4)
              (term.mkVar 5));
        in { mode = "Apply"; val = (vSigma "s" view.sTy ihClosure); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if view.idx == 2 then
        { mode = "Apply"; val = X; kont = ({ head = (kAppVV view.j); tail = ({ head = (kResume_KInterpD_view2_GotXj L I X i view.sub); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else if view.idx == 3 then
        let
          piTy = vPi "s" view.sTy (mkClosure [ X view.fn ]
            (term.mkApp (term.mkVar 1)
              (term.mkApp (term.mkVar 2) (term.mkVar 0))));
          ihClosure = mkClosure [ L I X i view.sub ]
            (term.mkInterpD (term.mkVar 1) (term.mkVar 2) (term.mkVar 5)
              (term.mkVar 3)
              (term.mkVar 4));
        in { mode = "Apply"; val = (vSigma "_" piTy ihClosure); kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = view.A; kont = ({ head = (kInterpD L I X i); tail = ({ head = (kInterpD_PlusGotA L I X i view.B); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KInterpD_view2_GotXj" = state:
      let
        k = state.kont.head;
        Xj = state.val;
        ihClosure = mkClosure [ k.L k.I k.X k.i k.sub ]
          (term.mkInterpD (term.mkVar 1) (term.mkVar 2) (term.mkVar 5)
            (term.mkVar 3)
            (term.mkVar 4));
      in { mode = "Apply"; val = (vSigma "_" Xj ihClosure); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KResume_KAllD_GotView" = state:
      let
        k = state.kont.head;
        view = state.val.view; D = state.val.D;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i; d = k.d;
      in
      if view == null then throw "tc: vAllD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        { mode = "Apply"; val = (self.vLiftF vLevelZero K vBootRefl vUnit); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if view.idx == 1 || view.idx == 2 || view.idx == 3 then
        { mode = "Apply"; val = d; kont = ({ head = kFst; tail = ({ head = (kResume_KAllD_GotFstD L I K X M i d view); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else
        if (d.tag or "") == "VThunkTm" then
          { mode = "Apply"; val = d; kont = ({ head = (kResume_KAllD_d L I K X M i D); tail = state.kont.tail; }); fuel = state.fuel - 1; }
        else
          { mode = "Apply"; val = d; kont = ({ head = kSumPayloadView; tail = ({ head = (kResume_KAllD_view4_GotSV L I K X M i view.A view.B d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KAllD_GotFstD" = state:
      let k = state.kont.head; fstD = state.val; in
      { mode = "Apply"; val = k.d; kont = ({ head = kSnd; tail = ({ head = (kResume_KAllD_GotSndD k.L k.I k.K k.X k.M k.i fstD k.view); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KAllD_GotSndD" = state:
      let
        k = state.kont.head;
        sndD = state.val;
        fstD = k.fstD; view = k.view;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i;
      in
      if view.idx == 1 then
        { mode = "Apply"; val = view.tFn; kont = ({ head = (kAppVV fstD); tail = ({ head = (kAllD_ArgGotSubD L I K X M i sndD); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else if view.idx == 2 then
        { mode = "Apply"; val = M; kont = ({ head = (kAppVV view.j); tail = ({ head = (kAppVV fstD); tail = ({ head = (kAllD_RecCombine sndD view.sub L I K X M i); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; }
      else
        let
          piTy = vPi "s" view.sTy (mkClosure [ M view.fn fstD ]
            (term.mkApp
              (term.mkApp (term.mkVar 1)
                (term.mkApp (term.mkVar 2) (term.mkVar 0)))
              (term.mkApp (term.mkVar 3) (term.mkVar 0))));
          ihClosure = mkClosure [ L I K X M i sndD view.sub ]
            (term.mkAllD (term.mkVar 1) (term.mkVar 2) (term.mkVar 8)
              (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
              (term.mkVar 6) (term.mkVar 7));
        in { mode = "Apply"; val = (vSigma "_" piTy ihClosure); kont = state.kont.tail; fuel = state.fuel - 1; };

    "KResume_KEverywhereD_GotView" = state:
      let
        k = state.kont.head;
        view = state.val.view; D = state.val.D;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i; d = k.d;
      in
      if view == null then throw "tc: vEverywhereD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        { mode = "Apply"; val = (self.vLiftIntroF vLevelZero K vBootRefl vUnit vTt); kont = state.kont.tail; fuel = state.fuel - 1; }
      else if view.idx == 1 || view.idx == 2 || view.idx == 3 then
        { mode = "Apply"; val = d; kont = ({ head = kFst; tail = ({ head = (kResume_KEverywhereD_GotFstD L I K X M ih i d view); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else
        if (d.tag or "") == "VThunkTm" then
          { mode = "Apply"; val = d; kont = ({ head = (kResume_KEverywhereD_d L I K X M ih i D); tail = state.kont.tail; }); fuel = state.fuel - 1; }
        else
          { mode = "Apply"; val = d; kont = ({ head = kSumPayloadView; tail = ({ head = (kResume_KEverywhereD_view4_GotSV L I K X M ih i view.A view.B d); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KEverywhereD_GotFstD" = state:
      let k = state.kont.head; fstD = state.val; in
      { mode = "Apply"; val = k.d; kont = ({ head = kSnd; tail = ({ head = (kResume_KEverywhereD_GotSndD k.L k.I k.K k.X k.M k.ih k.i fstD k.view); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KEverywhereD_GotSndD" = state:
      let
        k = state.kont.head;
        sndD = state.val;
        fstD = k.fstD; view = k.view;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i;
      in
      if view.idx == 1 then
        { mode = "Apply"; val = view.tFn; kont = ({ head = (kAppVV fstD); tail = ({ head = (kEverywhereD_ArgGotSubD L I K X M ih i sndD); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else if view.idx == 2 then
        # `ih._ihShortcut` + canonical fstD bypass the
        # `vAppF ∘ vAppF ∘ evalF` roundtrip via the reduction core's frame
        # encoding (kEverywhereD → kDescIndLayer_GotEvResult → recombine).
        if ih ? _ihShortcut && fstD.tag == "VDescCon"
        then
          let s = ih._ihShortcut; in
          { mode = "Apply"; val = s.D; kont = ({ head = (kEverywhereD vLevelZero s.I vLevelZero s.muFam s.motive ih view.j fstD.d); tail = ({ head = (kDescIndLayer_GotEvResult s.step view.j fstD.d); tail = ({ head = (kEverywhereD_RecGotIhHere L I K X M ih i sndD view.sub); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; }
        else
          { mode = "Apply"; val = ih; kont = ({ head = (kAppVV view.j); tail = ({ head = (kAppVV fstD); tail = ({ head = (kEverywhereD_RecGotIhHere L I K X M ih i sndD view.sub); tail = state.kont.tail; }); }); }); fuel = state.fuel - 1; }
      else
        let
          piLam = vLam "s" view.sTy (mkClosure [ ih view.fn fstD ]
            (term.mkApp
              (term.mkApp (term.mkVar 1)
                (term.mkApp (term.mkVar 2) (term.mkVar 0)))
              (term.mkApp (term.mkVar 3) (term.mkVar 0))));
        in { mode = "Apply"; val = view.sub; kont = ({ head = (kEverywhereD L I K X M ih i sndD); tail = ({ head = (kEverywhereD_PiCombine piLam); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    # Quote-side resume. mkQEvalStep pushes `kqResumeQuote d` and switches
    # to Eval when it meets a VThunkTm; once Eval reaches Apply with a forced
    # val, this handler restores Q-Eval at binder depth `d` so the original
    # quote kont resumes.
    "KQResumeQuote" = state:
      { mode = "Q-Eval"; v = state.val; d = state.kont.head.d; fuel = state.fuel; kont = state.kont.tail; };

    # Helper dispatchers — step-by-step replications of `desc.nix`'s
    # `descViewF` and `sumPayloadValView` bodies via machine frames. Every
    # sub-Val tag read happens on a forced Val (the driver step's Apply-mode peek
    # force-routes any VThunkTm state.val through Eval before the dispatcher body
    # runs). Every `vLiftElimF` call goes through a `kLiftElim_X` push per
    # the public-leaf forcing rule. The helpers in `desc.nix` stay for
    # external callers but are no longer reachable from a handler.
    #
    # VRaw* sentinels (VRawView / VRawSV / VRawDecode / VRawPeel) never
    # reach the tag-dispatch fallthrough because they appear only between
    # consecutive paired frames structurally placed by the call-site push.
    "KDescView" = state:
      let D = state.val; in
      let
        isDViewTag = D.tag == "DViewRet" || D.tag == "DViewArg"
                  || D.tag == "DViewRec" || D.tag == "DViewPi"
                  || D.tag == "DViewPlus";
      in
      if isDViewTag then
        { mode = "Apply"; val = { tag = "VRawView"; view = D; inherit D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if D.tag == "VDescCon" && D ? _canonRef then
        if D._canonRef.id == "descDesc" then
          let
            ref = D._canonRef;
            params =
              if ref ? params && builtins.length ref.params == 3
              then ref.params
              else throw "descViewF: malformed descDesc canonical reference";
            iLev_arg = builtins.elemAt params 0;
            I_arg = builtins.elemAt params 1;
            L_arg = builtins.elemAt params 2;
            view = self.descDescCanonicalViewF (state.fuel - 1) iLev_arg I_arg L_arg;
          in { mode = "Apply"; val = { tag = "VRawView"; inherit view; inherit D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
        else { mode = "Apply"; val = { tag = "VRawView"; view = null; inherit D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if D.tag == "VDescCon" then
        let
          hasDescDescRef =
            D ? D
            && builtins.isAttrs D.D
            && D.D ? _canonRef
            && (D.D._canonRef.id or null) == "descDesc"
            && D.D._canonRef ? params
            && builtins.length D.D._canonRef.params == 3;
          ddRef = if hasDescDescRef then D.D._canonRef else null;
          iLev_val = if !hasDescDescRef then null else builtins.elemAt ddRef.params 0;
          I_val    = if !hasDescDescRef then null else builtins.elemAt ddRef.params 1;
          k_val    = if !hasDescDescRef then null else builtins.elemAt ddRef.params 2;
          dDescL_val =
            if !hasDescDescRef then null
            else vLevelSuc (self.levelMaxOpt k_val iLev_val);
          label_val    = D._label    or null;
          conLabel_val = D._conLabel or null;
          meta = {
            inherit D hasDescDescRef iLev_val I_val k_val dDescL_val
                    label_val conLabel_val;
          };
        in
        { mode = "Apply"; val = D.d; kont = ({ head = (kDecodeWalk 0); tail = ({ head = (kResume_KDescView_GotDecode meta); tail = state.kont.tail; }); }); fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = { tag = "VRawView"; view = null; inherit D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    "KDecodeWalk" = state:
      let node = state.val; depth = state.kont.head.depth; in
      if depth >= 4 then
        { mode = "Apply"; val = { tag = "VRawDecode"; idx = 4; payload = node; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if node.tag == "VBootInl" then
        { mode = "Apply"; val = { tag = "VRawDecode"; idx = depth; payload = node.val; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if node.tag == "VBootInr" then
        { mode = "Apply"; val = node.val; kont = ({ head = (kDecodeWalk (depth + 1)); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = { tag = "VRawDecode"; idx = null; payload = null; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    "KResume_KDescView_GotDecode" = state:
      let info = state.val; meta = state.kont.head.meta; in
      if info.idx == null then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let
          gotPayloadFrame =
            if      info.idx == 0 then kResume_KDescView_Idx0_GotPayload meta
            else if info.idx == 1 then kResume_KDescView_Idx1_GotPayload meta
            else if info.idx == 2 then kResume_KDescView_Idx2_GotPayload meta
            else if info.idx == 3 then kResume_KDescView_Idx3_GotPayload meta
            else                       kResume_KDescView_Idx4_GotPayload meta;
        in { mode = "Apply"; val = info.payload; kont = ({ head = gotPayloadFrame; tail = state.kont.tail; }); fuel = state.fuel - 1; };

    # Idx 0: payload → (optional vLiftElim) → j → view.

    "KResume_KDescView_Idx0_GotPayload" = state:
      let payload = state.val; meta = state.kont.head.meta; in
      if payload.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let chainToJ = { head = (kResume_KDescView_Idx0_GotJ meta); tail = state.kont.tail; };
            chainBefore =
              if meta.hasDescDescRef
              then { head = (kLiftElim_X meta.iLev_val meta.dDescL_val vBootRefl meta.I_val); tail = chainToJ; }
              else chainToJ;
        in { mode = "Apply"; val = payload.fst; kont = chainBefore; fuel = state.fuel - 1; };

    "KResume_KDescView_Idx0_GotJ" = state:
      let j = state.val; meta = state.kont.head.meta; in
      let view = {
            idx = 0;
            inherit j;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
          };
      in { mode = "Apply"; val = { tag = "VRawView"; inherit view; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Idx 1: payload → payload.snd → sMeta (vLiftElim) → view.

    "KResume_KDescView_Idx1_GotPayload" = state:
      let payload = state.val; meta = state.kont.head.meta; in
      if payload.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = payload.snd; kont = ({ head = (kResume_KDescView_Idx1_GotSnd meta payload); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KDescView_Idx1_GotSnd" = state:
      let payloadSnd = state.val; payload = state.kont.head.payload; meta = state.kont.head.meta; in
      if payloadSnd.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let tPayload = payloadSnd.fst;
            chainToSMeta = { head = (kResume_KDescView_Idx1_GotSMeta meta tPayload); tail = state.kont.tail; };
            chainBefore =
              if meta.hasDescDescRef
              then { head = (kLiftElim_X (vLevelSuc meta.k_val) meta.dDescL_val vBootRefl (vU meta.k_val)); tail = chainToSMeta; }
              else chainToSMeta;
        in { mode = "Apply"; val = payload.fst; kont = chainBefore; fuel = state.fuel - 1; };

    "KResume_KDescView_Idx1_GotSMeta" = state:
      let sMeta = state.val; tPayload = state.kont.head.tPayload; meta = state.kont.head.meta; in
      let tFn = {
            tag = "VDescViewFn"; kind = "vapp";
            inherit tPayload;
            liftK = meta.k_val;
            liftDDescL = meta.dDescL_val;
            liftSTy = sMeta;
            noLift = !meta.hasDescDescRef;
          };
          lift =
            if (sMeta.tag or null) == "VLift"
            then { l = sMeta.l; eq = sMeta.eq; sTyRaw = sMeta.A; }
            else { l = meta.k_val; eq = vBootRefl; sTyRaw = sMeta; };
          view = {
            idx = 1;
            sTy = sMeta;
            inherit tFn;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
            inherit (lift) l eq sTyRaw;
          };
      in { mode = "Apply"; val = { tag = "VRawView"; inherit view; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Idx 2: payload → payload.snd → (optional vLiftElim) → j → view.

    "KResume_KDescView_Idx2_GotPayload" = state:
      let payload = state.val; meta = state.kont.head.meta; in
      if payload.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = payload.snd; kont = ({ head = (kResume_KDescView_Idx2_GotSnd meta payload); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KDescView_Idx2_GotSnd" = state:
      let payloadSnd = state.val; payload = state.kont.head.payload; meta = state.kont.head.meta; in
      if payloadSnd.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let sub = payloadSnd.fst;
            chainToJ = { head = (kResume_KDescView_Idx2_GotJ meta sub); tail = state.kont.tail; };
            chainBefore =
              if meta.hasDescDescRef
              then { head = (kLiftElim_X meta.iLev_val meta.dDescL_val vBootRefl meta.I_val); tail = chainToJ; }
              else chainToJ;
        in { mode = "Apply"; val = payload.fst; kont = chainBefore; fuel = state.fuel - 1; };

    "KResume_KDescView_Idx2_GotJ" = state:
      let j = state.val; sub = state.kont.head.sub; meta = state.kont.head.meta; in
      let view = {
            idx = 2;
            inherit j sub;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
          };
      in { mode = "Apply"; val = { tag = "VRawView"; inherit view; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Idx 3: payload → payload.snd → payload.snd.snd → sMeta (vLiftElim)
    #     → fn (vLiftElim) → view.

    "KResume_KDescView_Idx3_GotPayload" = state:
      let payload = state.val; meta = state.kont.head.meta; in
      if payload.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = payload.snd; kont = ({ head = (kResume_KDescView_Idx3_GotSnd meta payload); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KDescView_Idx3_GotSnd" = state:
      let payloadSnd = state.val; payload = state.kont.head.payload; meta = state.kont.head.meta; in
      if payloadSnd.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = payloadSnd.snd; kont = ({ head = (kResume_KDescView_Idx3_GotSndSnd meta payload payloadSnd); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KDescView_Idx3_GotSndSnd" = state:
      let payloadSndSnd = state.val;
          payload = state.kont.head.payload; psnd = state.kont.head.psnd; meta = state.kont.head.meta;
      in
      if payloadSndSnd.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let sub = payloadSndSnd.fst;
            psndFst = psnd.fst;
            chainToSMeta = { head = (kResume_KDescView_Idx3_GotSMeta meta psndFst sub); tail = state.kont.tail; };
            chainBefore =
              if meta.hasDescDescRef
              then { head = (kLiftElim_X (vLevelSuc meta.k_val) meta.dDescL_val vBootRefl (vU meta.k_val)); tail = chainToSMeta; }
              else chainToSMeta;
        in { mode = "Apply"; val = payload.fst; kont = chainBefore; fuel = state.fuel - 1; };

    "KResume_KDescView_Idx3_GotSMeta" = state:
      let sMeta = state.val; psndFst = state.kont.head.psndFst; sub = state.kont.head.sub; meta = state.kont.head.meta; in
      let fTy = vPi "_" sMeta (mkClosure [ meta.I_val ] (term.mkVar 1));
          chainToFn = { head = (kResume_KDescView_Idx3_GotFn meta sMeta sub); tail = state.kont.tail; };
          chainBefore =
            if meta.hasDescDescRef
            then { head = (kLiftElim_X (self.levelMaxOpt meta.k_val meta.iLev_val) meta.dDescL_val vBootRefl fTy); tail = chainToFn; }
            else chainToFn;
      in { mode = "Apply"; val = psndFst; kont = chainBefore; fuel = state.fuel - 1; };

    "KResume_KDescView_Idx3_GotFn" = state:
      let fn = state.val; sMeta = state.kont.head.sMeta; sub = state.kont.head.sub; meta = state.kont.head.meta; in
      let lift =
            if (sMeta.tag or null) == "VLift"
            then { l = sMeta.l; eq = sMeta.eq; sTyRaw = sMeta.A; }
            else { l = meta.k_val; eq = vBootRefl; sTyRaw = sMeta; };
          view = {
            idx = 3;
            sTy = sMeta;
            inherit fn sub;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
            inherit (lift) l eq sTyRaw;
          };
      in { mode = "Apply"; val = { tag = "VRawView"; inherit view; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Idx 4: payload → payload.snd → view.

    "KResume_KDescView_Idx4_GotPayload" = state:
      let payload = state.val; meta = state.kont.head.meta; in
      if payload.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = payload.snd; kont = ({ head = (kResume_KDescView_Idx4_GotSnd meta payload); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KDescView_Idx4_GotSnd" = state:
      let payloadSnd = state.val; payload = state.kont.head.payload; meta = state.kont.head.meta; in
      if payloadSnd.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawView"; view = null; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let view = {
              idx = 4;
              A = payload.fst;
              B = payloadSnd.fst;
              iLev = meta.iLev_val;
              I = meta.I_val;
              k = meta.k_val;
              label = meta.label_val;
              conLabel = meta.conLabel_val;
            };
        in { mode = "Apply"; val = { tag = "VRawView"; inherit view; D = meta.D; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Step-by-step replication of `sumPayloadValView`.

    "KSumPayloadView" = state:
      let d = state.val; in
      if d.tag == "VBootInl" then
        let sv = {
              side = "inl";
              value = d.val;
              rebuild = payload: vBootInl d.left d.right payload;
            };
        in { mode = "Apply"; val = { tag = "VRawSV"; inherit sv; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if d.tag == "VBootInr" then
        let sv = {
              side = "inr";
              value = d.val;
              rebuild = payload: vBootInr d.left d.right payload;
            };
        in { mode = "Apply"; val = { tag = "VRawSV"; inherit sv; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if d.tag == "VDescCon" then
        { mode = "Apply"; val = d.D; kont = ({ head = (kResume_KSumPayloadView_GotDDesc d); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = { tag = "VRawSV"; sv = null; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    "KResume_KSumPayloadView_GotDDesc" = state:
      let dD = state.val; d = state.kont.head.d; in
      if !(dD ? _descRef) then
        { mode = "Apply"; val = { tag = "VRawSV"; sv = null; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else if !(self.isSumDescRef dD._descRef) then
        { mode = "Apply"; val = { tag = "VRawSV"; sv = null; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = d.d; kont = ({ head = (kResume_KSumPayloadView_GotDD d); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KSumPayloadView_GotDD" = state:
      let dDInner = state.val; d = state.kont.head.d; in
      if dDInner.tag != "VBootInl" && dDInner.tag != "VBootInr" then
        { mode = "Apply"; val = { tag = "VRawSV"; sv = null; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = dDInner.val; kont = ({ head = (kResume_KSumPayloadView_GotDDVal d dDInner); tail = state.kont.tail; }); fuel = state.fuel - 1; };

    "KResume_KSumPayloadView_GotDDVal" = state:
      let dDValForced = state.val; d = state.kont.head.d; dD = state.kont.head.dD; in
      if dDValForced.tag != "VPair" then
        { mode = "Apply"; val = { tag = "VRawSV"; sv = null; }; kont = state.kont.tail; fuel = state.fuel - 1; }
      else
        let pair = dDValForced; pairSnd = pair.snd; in
        { mode = "Apply"; val = pair.fst; kont = ({ head = (kPeelLiftIntroVal (payload: payload)); tail = ({ head = (kResume_KSumPayloadView_GotField d dD pairSnd); tail = state.kont.tail; }); }); fuel = state.fuel - 1; };

    "KResume_KSumPayloadView_GotField" = state:
      let field = state.val; d = state.kont.head.d; dD = state.kont.head.dD; pairSnd = state.kont.head.pairSnd; in
      let side = if dD.tag == "VBootInl" then "inl" else "inr";
          sv = {
            inherit side;
            inherit (field) value;
            rebuild = payload:
              vDescCon d.D d.i
                (if side == "inl"
                then vBootInl dD.left dD.right (vPair (field.rebuild payload) pairSnd)
                else vBootInr dD.left dD.right (vPair (field.rebuild payload) pairSnd));
          };
      in { mode = "Apply"; val = { tag = "VRawSV"; inherit sv; }; kont = state.kont.tail; fuel = state.fuel - 1; };

    # Iterative walker over VLiftIntro layers, accumulating the rebuild fn
    # into the frame. Non-VLiftIntro `state.val` terminates with a VRawPeel
    # carrying `{ value, rebuild }`.
    "KPeelLiftIntroVal" = state:
      let v = state.val; rb = state.kont.head.rebuildAcc; in
      if v.tag == "VLiftIntro" then
        let newRb = payload: rb (vLiftIntro v.l v.m v.eq v.A payload);
        in { mode = "Apply"; val = v.a; kont = ({ head = (kPeelLiftIntroVal newRb); tail = state.kont.tail; }); fuel = state.fuel - 1; }
      else
        { mode = "Apply"; val = { tag = "VRawPeel"; value = v; rebuild = rb; }; kont = state.kont.tail; fuel = state.fuel - 1; };
  };

  # Sentinel for the eval-only entry: any flow that lands a Q-Apply frame
  # with `qApplyDispatch.${tag}` invoking `fallback` is a routing bug — the
  # eval driver should never reach a Q-fallback path.
  evalDefaultFallback = _d: v:
    throw "tc.eval: Q-fallback reached from eval-only path (val.tag=${v.tag or "?"})";

  # Trace-eliding driver: a chunked `foldl'` threads only the current state,
  # so intermediate states GC immediately (the driver retains no trace).
  # The chunk ladder is a linked chain of SHARED CONSTANT index lists of
  # doubling length (4 … 32768): the loop walks `next` to reach the
  # bigger chunk without allocating per run. The small seed keeps
  # shallow machine entries (`ev`'s eager forces and hybrid punts,
  # typically <5 steps) from wasting post-Done iterations; the shared
  # constants avoid the O(steps) list cells a per-level `chunk ++
  # chunk` doubling would allocate per entry. The top node links to
  # itself, so past the cap the loop consumes fuel in 32768-step
  # chunks: native loop depth is ladder height + steps/32768 — ~320
  # frames at the 1e7 fuel ceiling, far inside the libnix stack
  # budget. A fixed-size loop at the seed length would instead accrue
  # steps/4 frames (Nix has no TCO) and overflow the 8 MiB stack.
  # Starts at 8: the driver steps the first four transitions inline (see
  # `driver`), so the cumulative chunk boundaries (4, 12, 28, 60, …) match a
  # plain 4-start ladder while tiny entries never reach the foldl' at all.
  driverChunkLadder =
    let
      cap = 32768;
      build = size:
        let chunk = builtins.genList (n: n) size; in
        if size >= cap
        then let top = { inherit chunk; next = top; }; in top
        else { inherit chunk; next = build (size * 2); };
    in build 8;

  # The complete per-iteration step: Done/Q-Done absorption, fuel check, and
  # the unified mode dispatch fused into one lambda (the driver loop applies
  # it once per chunk element, so every extra function layer here costs an
  # Env + call per machine step).
  #
  # When the driver reaches `Done` with a `VLazyDescIndAccLayer` Val, transform
  # to `Apply` with the three force-frames pushed — the cascade resolves in
  # the same driver loop (the kont stack absorbs the depth; libnix sees one
  # frame). Similarly, a `VThunkTm` at Done transitions to Eval to force the
  # deferred Tm. `Q-Done` is terminal: the quote driver consumes `state.tm`.
  # The invariant `runMachineAtF returns only forced Vals` is enforced here.
  #
  # Eval seq-forces `state.env`/`state.kont`: they are threaded into the next
  # Eval state by reference, and a descent that never reads them (e.g. a deep
  # application spine, whose env is untouched until the head variable and
  # whose kont is consumed only on the return apply) would leave them as an
  # N-deep chain of attribute-select thunks, forced all at once at the leaf —
  # N-deep native recursion that overflows the C stack. Forcing each to WHNF
  # per step keeps them flat (O(1)); the select chain never accumulates.
  #
  # Apply peeks for a `VThunkTm` val and forces the deferred Tm before
  # letting the active frame consume it (kont preserved; the frame fires once
  # Eval produces a forced Val) — the cascade stays inside the driver, no
  # fresh runMachineF entry. Q-Eval delegates to a `mkQEvalStep`-built
  # closure; the `fallback` parameter is the quote-side leaf fallback it
  # consumes. Q-Apply hands the state to `qApplyDispatch` or completes via
  # a terminal Q-Done state when the kont is empty.
  mkStepIf = fallback:
    let qEvalStep = mkQEvalStep fallback; in
    state: _i:
      if state.mode == "Done" then
        if (state.val.tag or "") == "VLazyDescIndAccLayer" then
          let fn = state.val; in
          {
            mode = "Apply"; val = fn.step; fuel = state.fuel;
            kont = { head = (kAppVV fn.i); tail = ({ head = (kAppVV fn.d); tail = ({ head = (kAppVV (vPair fn.prevAcc vTt)); tail = null; }); }); };
          }
        else if (state.val.tag or "") == "VThunkTm" then
          { mode = "Eval"; env = state.val.env; tm = state.val.tm;
            fuel = state.fuel; kont = null; }
        else state
      else if state.mode == "Q-Done" then state
      else if state.fuel <= 0 then state // { mode = "__exhausted__"; }
      else if state.mode == "Eval" then
        builtins.seq state.env
          (builtins.seq state.kont (evalDispatch.${state.tm.tag} state))
      else if state.mode == "Apply" then
        if state.kont == null then { mode = "Done"; val = state.val; fuel = state.fuel; }
        else if (state.val.tag or "") == "VThunkTm" then
          { mode = "Eval"; env = state.val.env; tm = state.val.tm; kont = state.kont; fuel = state.fuel - 1; }
        else applyDispatch.${state.kont.head.tag} state
      else if state.mode == "Q-Eval" then qEvalStep state
      else if state.mode == "Q-Apply" then
        if state.kont == null
        then { mode = "Q-Done"; fuel = state.fuel; tm = state.tm; }
        else qApplyDispatch.${state.kont.head.tag} state
      else state;

  stepIf = mkStepIf evalDefaultFallback;

  # Exit predicate shared by the drivers' unrolled prefix: Done with a fully
  # forced Val (a `VLazyDescIndAccLayer`/`VThunkTm` at Done is transformed
  # back to work by `stepIf` on the next iteration), or a terminal Q-Done.
  stepExited = s:
    (s.mode == "Done"
      && (s.val.tag or "") != "VLazyDescIndAccLayer"
      && (s.val.tag or "") != "VThunkTm")
    || s.mode == "Q-Done";

  driver = initState:
    let
      # Each level runs an iterative `foldl'` over the ladder node's
      # chunk (`stepIf` ignores the index elements), then advances to
      # `lad.next`; threading a single state keeps peak heap
      # independent of step count. See `driverChunkLadder` for the
      # depth bound.
      loop = lad: state:
        let after = builtins.foldl' stepIf state lad.chunk; in
        # Only exit on `Done` if the returned Val is fully forced. A
        # `VLazyDescIndAccLayer` at the boundary gets transformed back to
        # `Apply` by `stepIf` on the next chunk iteration, ensuring the
        # invariant: `runMachineAtF` never returns a deferred layer.
        if after.mode == "Done"
           && (after.val.tag or "") != "VLazyDescIndAccLayer"
           && (after.val.tag or "") != "VThunkTm"
        then after.val
        else if after.mode == "Q-Done"
        then after.tm
        else if after.mode == "__exhausted__"
        then throw "normalization budget exceeded"
        else loop lad.next after;
      # Most entries are external `VThunkTm` forces finishing within a few
      # transitions: step the first four inline, exiting at Done exactly,
      # instead of padding them out to a full foldl' chunk.
      s1 = stepIf initState 0;
      s2 = stepIf s1 0;
      s3 = stepIf s2 0;
      s4 = stepIf s3 0;
    in
    if stepExited s1 then (if s1.mode == "Q-Done" then s1.tm else s1.val)
    else if stepExited s2 then (if s2.mode == "Q-Done" then s2.tm else s2.val)
    else if stepExited s3 then (if s3.mode == "Q-Done" then s3.tm else s3.val)
    else if stepExited s4 then (if s4.mode == "Q-Done" then s4.tm else s4.val)
    else loop driverChunkLadder s4;

  # Identical per-step work to `driver` (shares stepIf/driverChunkLadder);
  # differs only at the exit, retaining `after.fuel` for step counting.
  driverCounted = initState:
    let
      loop = lad: state:
        let after = builtins.foldl' stepIf state lad.chunk; in
        if after.mode == "Done"
           && (after.val.tag or "") != "VLazyDescIndAccLayer"
           && (after.val.tag or "") != "VThunkTm"
        then { val = after.val; fuel = after.fuel; }
        else if after.mode == "Q-Done"
        then { tm = after.tm; fuel = after.fuel; }
        else if after.mode == "__exhausted__"
        then throw "normalization budget exceeded"
        else loop lad.next after;
      exit = s:
        if s.mode == "Q-Done"
        then { tm = s.tm; fuel = s.fuel; }
        else { val = s.val; fuel = s.fuel; };
      s1 = stepIf initState 0;
      s2 = stepIf s1 0;
      s3 = stepIf s2 0;
      s4 = stepIf s3 0;
    in
    if stepExited s1 then exit s1
    else if stepExited s2 then exit s2
    else if stepExited s3 then exit s3
    else if stepExited s4 then exit s4
    else loop driverChunkLadder s4;

  runMachineF = fuel: env: tm:
    driver { mode = "Eval"; env = envFromList env; inherit tm fuel; kont = null; };

  # steps = Eval/Apply transitions for one run (each pays one fuel; Done does not).
  runMachineCountedF = fuel: env: tm:
    let r = driverCounted { mode = "Eval"; env = envFromList env; inherit tm fuel; kont = null; };
    in { val = r.val; steps = fuel - r.fuel; };

  # Apply-mode entry: resume the machine with `val` ready to be consumed by
  # `kont`'s top frame. Used by `desc.nix`'s helper wrappers, which preload
  # an entry frame and deliver the description as the seed Val.
  runMachineAtF = fuel: kont: val:
    driver { mode = "Apply"; inherit val kont fuel; };

  runDescIndAtF = fuel: D: motive: step: i: scrut:
    runMachineAtF fuel ({ head = (kDescInd D motive step i); tail = null; }) scrut;

  runDescIndLayerAtF = fuel: D: motive: step: ihVal: muFam: I: i: d:
    runMachineAtF fuel
      ({ head = (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal i d); tail = ({ head = (kDescIndLayer_GotEvResult step i d); tail = null; }); })
      D;

  runInterpDAtF = fuel: L: I: X: i: D:
    runMachineAtF fuel ({ head = (kInterpD L I X i); tail = null; }) D;

  runAllDAtF = fuel: L: I: K: X: M: i: d: D:
    runMachineAtF fuel ({ head = (kAllD L I K X M i d); tail = null; }) D;

  runEverywhereDAtF = fuel: L: I: K: X: M: ih: i: d: D:
    runMachineAtF fuel ({ head = (kEverywhereD L I K X M ih i d); tail = null; }) D;

  # Quote sub-machine — defunctionalized read-back `Val -> Tm`.
  #
  # State carries binding depth `d` in place of an environment. No
  # Done-transform: quote's Done is a built Tm.
  #
  #   { mode = "Q-Eval";  v;  d; kont; fuel; }
  #   { mode = "Q-Apply"; tm; d; kont; fuel; }
  #   { mode = "Q-Done";  tm;       fuel; }
  #
  # `KQ_App` is the generic n-ary builder: holds the remaining
  # `(d, Val)` pending list, a `mkTm : [Tm] -> Tm` closure, and the
  # accumulated sub-Tms. `runQuoteF` accepts a `fallback : d -> Val ->
  # Tm` for Val tags whose dispatch is not (yet) inlined into
  # `qEvalStep`.

  # `outerD` records the binder's own depth — the depth at which the
  # binder opens. The handler uses it to compute `freshVar` and the
  # body's start depth, and `KQ_Binder_Done` restores it on pop so
  # callers further out in the kont see the same `state.d` they would
  # have seen in a recursive `quote d (VPi …)` call. Without this, an
  # inner binder appearing in the domain would propagate `state.d =
  # outer+1` upward, so the outer handler would pick `freshVar(outer+1)`
  # and quote the body against a one-too-deep environment.
  kqBinderDomain = name: closure: ctor: outerD:
    { tag = "KQ_Binder_Domain"; inherit name closure ctor outerD; };
  kqBinderDone = name: domTm: ctor: outerD:
    { tag = "KQ_Binder_Done"; inherit name domTm ctor outerD; };

  # `KQ_Spine_Step` walks a `VNe` spine left-to-right, consuming
  # `state.tm` as the current head and threading the elim sub-Tms
  # through a `KQ_App` frame whose `mkTm` closure builds the
  # next-step head. The frame re-pushes itself at `idx + 1` so the
  # fold drives one elim per handler firing.
  kqSpineStep = spine: idx:
    { tag = "KQ_Spine_Step"; inherit spine idx; };

  # Chain-form VDescCon → flat-form `mkDescConChain` Tm. The setup
  # The `KQ_App` frame quotes the 6 fixed sub-Vals (outerD + payload left/right
  # + base.{D,i,d}) as an attrset; `KQ_DescConChain_Build` then
  # receives the bundle via `state.tm`, materialises the `layers`
  # field via `genList (idx: { i = runQuoteF …; heads = map runQuoteF …; })`
  # over the chain's `layerInfo`, and emits a single
  # `mkDescConChain { layers; base; outerD; payloadTag; … }` Tm.
  # Each per-layer `runQuoteF` is a sub-driver call with its own
  # `genericClosure` loop — O(1) libnix frames per sub-quote,
  # O(N) sub-quotes total. `forceValueDeep` on the output Tm walks
  # the Nix-list iteratively, so depth is O(1) regardless of N.
  kqDescConChainBuild = fallback: layerInfo: n: dDepth: payloadTag:
    { tag = "KQ_DescConChain_Build";
      inherit fallback layerInfo n payloadTag;
      d = dDepth; };

  # `quoteElimSpec` decomposes a single elim into `{ pending; mkTm; }`
  # where `pending` is the `[(d, Val)]` list of sub-Vals to quote and
  # `mkTm` is the closure consumed by `KQ_App` that splices the
  # resulting Tms into the elim's term constructor alongside the
  # captured head. Sub-Val order matches the recursive `quoteElim`
  # bodies in `tc/quote.nix`; ordering changes here would alter the
  # Tm shape that downstream callers see.
  quoteElimSpec = d: headTm: e:
    let t = e.tag; in
         if t == "EApp" then {
      pending = [ { inherit d; v = e.arg; } ];
      mkTm = ts: term.mkApp headTm (builtins.elemAt ts 0);
    }
    else if t == "EFst" then {
      pending = [ ]; mkTm = _ts: term.mkFst headTm;
    }
    else if t == "ESnd" then {
      pending = [ ]; mkTm = _ts: term.mkSnd headTm;
    }
    else if t == "EStrEq" then {
      pending = [ { inherit d; v = e.arg; } ];
      mkTm = ts: term.mkStrEq headTm (builtins.elemAt ts 0);
    }
    else if t == "EAbsurd" then {
      pending = [ { inherit d; v = e.type; } ];
      mkTm = ts: term.mkAbsurd (builtins.elemAt ts 0) headTm;
    }
    else if t == "EBootSumElim" then {
      pending = [
        { inherit d; v = e.left; }
        { inherit d; v = e.right; }
        { inherit d; v = e.motive; }
        { inherit d; v = e.onLeft; }
        { inherit d; v = e.onRight; }
      ];
      mkTm = ts: term.mkBootSumElim
        (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)
        (builtins.elemAt ts 3) (builtins.elemAt ts 4)
        headTm;
    }
    else if t == "EBootJ" then {
      pending = [
        { inherit d; v = e.type; }
        { inherit d; v = e.lhs; }
        { inherit d; v = e.motive; }
        { inherit d; v = e.base; }
        { inherit d; v = e.rhs; }
      ];
      mkTm = ts: term.mkBootJ
        (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)
        (builtins.elemAt ts 3) (builtins.elemAt ts 4)
        headTm;
    }
    else if t == "EDescInd" then {
      pending = [
        { inherit d; v = e.D; }
        { inherit d; v = e.motive; }
        { inherit d; v = e.step; }
        { inherit d; v = e.i; }
      ];
      mkTm = ts: term.mkDescInd
        (builtins.elemAt ts 0) (builtins.elemAt ts 1)
        (builtins.elemAt ts 2) (builtins.elemAt ts 3)
        headTm;
    }
    # `EInterpD` / `EAllD` / `EEverywhereD` round-trip stuck
    # eliminators on a neutral D scrutinee; the spine head is D,
    # so each elim's pending list omits D and `mkTm` splices
    # `headTm` into D's slot. Level-zero sub-Vals route through
    # `mkQEvalStep`'s leaf dispatch and round-trip to the shared
    # `term.mkLevelZero` sentinel; no per-elim fast-path needed.
    else if t == "EInterpD" then {
      pending = [
        { inherit d; v = e.level; }
        { inherit d; v = e.I; }
        { inherit d; v = e.X; }
        { inherit d; v = e.i; }
      ];
      mkTm = ts: term.mkInterpD
        (builtins.elemAt ts 0) (builtins.elemAt ts 1)
        headTm
        (builtins.elemAt ts 2) (builtins.elemAt ts 3);
    }
    else if t == "EAllD" then {
      pending = [
        { inherit d; v = e.level; }
        { inherit d; v = e.I; }
        { inherit d; v = e.K; }
        { inherit d; v = e.X; }
        { inherit d; v = e.M; }
        { inherit d; v = e.i; }
        { inherit d; v = e.d; }
      ];
      mkTm = ts: term.mkAllD
        (builtins.elemAt ts 0) (builtins.elemAt ts 1)
        headTm
        (builtins.elemAt ts 2) (builtins.elemAt ts 3) (builtins.elemAt ts 4)
        (builtins.elemAt ts 5) (builtins.elemAt ts 6);
    }
    else if t == "EEverywhereD" then {
      pending = [
        { inherit d; v = e.level; }
        { inherit d; v = e.I; }
        { inherit d; v = e.K; }
        { inherit d; v = e.X; }
        { inherit d; v = e.M; }
        { inherit d; v = e.ih; }
        { inherit d; v = e.i; }
        { inherit d; v = e.d; }
      ];
      mkTm = ts: term.mkEverywhereD
        (builtins.elemAt ts 0) (builtins.elemAt ts 1)
        headTm
        (builtins.elemAt ts 2) (builtins.elemAt ts 3) (builtins.elemAt ts 4)
        (builtins.elemAt ts 5) (builtins.elemAt ts 6) (builtins.elemAt ts 7);
    }
    else if t == "ELiftElim" then {
      pending = [
        { inherit d; v = e.l; }
        { inherit d; v = e.m; }
        { inherit d; v = e.eq; }
        { inherit d; v = e.A; }
      ];
      mkTm = ts: term.mkLiftElim
        (builtins.elemAt ts 0) (builtins.elemAt ts 1)
        (builtins.elemAt ts 2) (builtins.elemAt ts 3)
        headTm;
    }
    else if t == "ESquashElim" then {
      pending = [
        { inherit d; v = e.A; }
        { inherit d; v = e.B; }
        { inherit d; v = e.f; }
      ];
      mkTm = ts: term.mkSquashElim
        (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)
        headTm;
    }
    else throw "qmachine: quoteElimSpec unknown elim tag: ${t}";

  qApplyDispatch = {
    "KQ_App" = state:
      let
        k    = state.kont.head;
        rest = state.kont.tail;
        acc' = k.acc ++ [ state.tm ];
      in
      if k.pending == [ ]
      then { mode = "Q-Apply"; kont = rest; fuel = state.fuel; d = state.d; tm = (k.mkTm acc'); }
      else
        let next = builtins.head k.pending; in
        { mode = "Q-Eval"; kont = ({ head = ({ tag = "KQ_App"; pending = (builtins.tail k.pending); mkTm = k.mkTm; acc = acc'; }); tail = rest; }); fuel = state.fuel; d = next.d; v = next.v; };

    # Materialise the binder body via a mode switch onto the shared driver:
    # Eval on `(freshVar :: closure.env, closure.body)`, with `kqResumeQuote
    # (outerD + 1)` riding above `kqBinderDone` so the resumed Q-Eval lands
    # at the under-binder depth and the binder finalisation fires once the
    # body Tm is built. No fresh `runMachineF` entry.
    "KQ_Binder_Domain" = state:
      let
        k = state.kont.head; rest = state.kont.tail;
        domTm = state.tm;
      in
        { mode = "Eval";
          env  = { head = freshVar k.outerD; tail = k.closure.env; };
          tm   = k.closure.body;
          fuel = state.fuel - 1;
          kont = { head = (kqResumeQuote (k.outerD + 1)); tail = ({ head = (kqBinderDone k.name domTm k.ctor k.outerD); tail = rest; }); }; };

    "KQ_Binder_Done" = state:
      let
        k = state.kont.head; rest = state.kont.tail;
        bodyTm = state.tm;
        tm =
               if k.ctor == "pi"    then term.mkPi    k.name k.domTm bodyTm
          else if k.ctor == "lam"   then term.mkLam   k.name k.domTm bodyTm
          else if k.ctor == "sigma" then term.mkSigma k.name k.domTm bodyTm
          else throw "qmachine: bad binder ctor: ${k.ctor}";
      in { mode = "Q-Apply"; kont = rest; fuel = state.fuel; d = k.outerD; tm = tm; };

    "KQ_Spine_Step" = state:
      let
        k = state.kont.head; rest = state.kont.tail;
        headTm = state.tm;
        n = builtins.length k.spine;
      in
      if k.idx == n
      then { mode = "Q-Apply"; kont = rest; fuel = state.fuel; d = state.d; tm = headTm; }
      else
        let
          e = builtins.elemAt k.spine k.idx;
          spec = quoteElimSpec state.d headTm e;
          restAfter = { head = (kqSpineStep k.spine (k.idx + 1)); tail = rest; };
        in
          if spec.pending == [ ]
          then { mode = "Q-Apply"; kont = restAfter; fuel = state.fuel; d = state.d; tm = (spec.mkTm [ ]); }
          else
            let first = builtins.head spec.pending; in
            { mode = "Q-Eval"; kont = ({ head = ({ tag = "KQ_App"; pending = (builtins.tail spec.pending); mkTm = spec.mkTm; acc = [ ]; }); tail = restAfter; }); fuel = state.fuel; d = first.d; v = first.v; };

    # Builds the layers field by direct-recursive `quote` on each
    # layer's sub-Vals. Trivial Vals short-circuit at the `quote`
    # source; compound sub-Vals re-enter via `runQ`. Emits one
    # `mkDescConChain` Tm whose `forceValueDeep` walk is iterative,
    # so output depth is O(1) in n.
    "KQ_DescConChain_Build" = state:
      let
        k    = state.kont.head;
        rest = state.kont.tail;
        setup = state.tm;
        qf = k.fallback k.d;
        layerTms = builtins.genList
          (idx:
            let layer = builtins.elemAt k.layerInfo idx; in
            { i = qf layer.i;
              heads = map qf layer.heads;
            })
          k.n;
        chainTm = term.mkDescConChain {
          layers       = layerTms;
          base         = setup.baseTm;
          outerD       = setup.outerDTm;
          payloadTag   = k.payloadTag;
          payloadLeft  = setup.leftTm;
          payloadRight = setup.rightTm;
        };
      in { mode = "Q-Apply"; kont = rest; fuel = state.fuel; d = k.d; tm = chainTm; };
  };

  mkQEvalStep = fallback: state:
    let v = state.v; t = v.tag; kont = state.kont; fuel = state.fuel; d = state.d; in

    # Force a deferred Tm before quoting via a mode switch through the shared
    # driver. `kqResumeQuote d` rides on top of the Q kont; once Eval reaches
    # Apply with a forced val, the resume handler switches back to Q-Eval at
    # the captured binder depth. No fresh `runMachineF` entry.
         if t == "VThunkTm"        then
           { mode = "Eval"; env = v.env; tm = v.tm;
             fuel = fuel - 1; kont = { head = (kqResumeQuote d); tail = kont; }; }
    else if t == "VUnit"          then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkUnit; }
    else if t == "VTt"            then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkTt; }
    else if t == "VEmpty"         then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkEmpty; }
    else if t == "VBootRefl"      then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkBootRefl; }
    else if t == "VFunext"        then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkFunext; }
    else if t == "VLevel"         then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkLevel; }
    else if t == "VLevelZero"     then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkLevelZero; }
    else if t == "VString"        then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkString; }
    else if t == "VInt"           then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkInt; }
    else if t == "VFloat"         then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkFloat; }
    else if t == "VAttrs"         then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkAttrs; }
    else if t == "VPath"          then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkPath; }
    else if t == "VDerivation"    then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkDerivation; }
    else if t == "VFunction"      then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkFunction; }
    else if t == "VAny"           then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkAny; }
    else if t == "VStringLit"     then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = (term.mkStringLit v.value); }
    else if t == "VIntLit"        then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = (term.mkIntLit v.value); }
    else if t == "VFloatLit"      then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = (term.mkFloatLit v.value); }
    else if t == "VAttrsLit"      then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkAttrsLit; }
    else if t == "VPathLit"       then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkPathLit; }
    else if t == "VDerivationLit" then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkDerivationLit; }
    else if t == "VFnLit"         then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkFnLit; }
    else if t == "VAnyLit"        then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = term.mkAnyLit; }

    else if t == "VPair" then
      let fr = { tag = "KQ_App"; pending = [ { inherit d; v = v.snd; } ]; mkTm = (ts: term.mkPair (builtins.elemAt ts 0) (builtins.elemAt ts 1)); acc = [ ]; };
      in { mode = "Q-Eval"; kont = ({ head = fr; tail = kont; }); fuel = fuel; d = d; v = v.fst; }

    else if t == "VPi" then
      { mode = "Q-Eval"; kont = ({ head = (kqBinderDomain v.name v.closure "pi" d); tail = kont; }); fuel = fuel; d = d; v = v.domain; }
    else if t == "VLam" then
      { mode = "Q-Eval"; kont = ({ head = (kqBinderDomain v.name v.closure "lam" d); tail = kont; }); fuel = fuel; d = d; v = v.domain; }
    else if t == "VSigma" then
      { mode = "Q-Eval"; kont = ({ head = (kqBinderDomain v.name v.closure "sigma" d); tail = kont; }); fuel = fuel; d = d; v = v.fst; }

    else if t == "VNe" then
      let headTm = term.mkVar (d - v.level - 1); in
      if v.spine == [ ]
      then { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = headTm; }
      else { mode = "Q-Apply"; kont = ({ head = (kqSpineStep v.spine 0); tail = kont; }); fuel = fuel; d = d; tm = headTm; }

    # VDescCon: `_canonRef` short-circuits to the canonical-app Tm
    # without forcing `.D`; `linearChain` iterates `_layers`; the
    # canonical fallback peels the linear-recursive chain once. Each
    # branch queues sub-Vals on one `KQ_App` so libnix depth is O(1).
    else if t == "VDescCon" then
      if v ? _canonRef then
        let
          ref = v._canonRef;
          params =
            if ref ? params then ref.params
            else throw "quote: canonical reference missing params";
        in
        if ref.id == "descDesc" then
          if builtins.length params != 3
          then throw "quote: descDesc canonical reference expects three params"
          else
            let fr = { tag = "KQ_App"; pending = [ { inherit d; v = builtins.elemAt params 1; }
                { inherit d; v = builtins.elemAt params 2; }
              ]; mkTm = (ts: term.mkDescDescAppAt
                (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)); acc = [ ]; };
            in { mode = "Q-Eval"; kont = ({ head = fr; tail = kont; }); fuel = fuel; d = d; v = (builtins.elemAt params 0); }
        else
          if !(ref ? body)
          then throw "quote: canonical reference '${ref.id}' missing body (synthetic stamp?)"
          else
            let
              nParams = builtins.length params;
              paramsPending = map (p: { inherit d; v = p; }) params;
              allPending = paramsPending ++ [ { inherit d; v = ref.body; } ];
              mkTm = ts:
                let paramTms = builtins.genList (i: builtins.elemAt ts i) nParams;
                    bodyTm   = builtins.elemAt ts nParams; in
                term.mkCanonApp ref.id paramTms bodyTm;
              first = builtins.head allPending;
              fr    = { tag = "KQ_App"; pending = (builtins.tail allPending); mkTm = mkTm; acc = [ ]; };
            in { mode = "Q-Eval"; kont = ({ head = fr; tail = kont; }); fuel = fuel; d = first.d; v = first.v; }

      else if (v._shape or null) == "linearChain" then
        let
          base   = v._base;
          layers = self.effLayers v;
          n      = builtins.length layers;
        in
        if n == 0 then
          # n=0 chain-form Val is conv-equal to its plain base; emit
          # plain `mkDescCon` so consumers pattern-matching `.d.tag`
          # keep working.
          let fr = { tag = "KQ_App"; pending = [ { inherit d; v = base.i; }
              { inherit d; v = base.d; }
            ]; mkTm = (ts: term.mkDescCon
              (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)); acc = [ ]; };
          in { mode = "Q-Eval"; kont = ({ head = fr; tail = kont; }); fuel = fuel; d = d; v = base.D; }
        else if n == 1 then
          # Single layer — emit plain `mkDescCon` so consumers
          # pattern-matching `.d.tag` keep working. Payload:
          # `mkBootInr/Inl L R (pair h_0 (... (pair tail refl)))`.
          let
            qf      = fallback d;
            layer0  = builtins.head layers;
            heads   = layer0.heads;
            nFields = builtins.length heads;
            baseTm  = term.mkDescCon (qf base.D) (qf base.i) (qf base.d);
            headTms = map qf heads;
            # Right-to-left fold: walk head indices from `nFields-1`
            # down to 0, prepending each pair onto the accumulator.
            innerTm = builtins.foldl'
              (acc: idx: term.mkPair (builtins.elemAt headTms idx) acc)
              (term.mkPair baseTm term.mkBootRefl)
              (builtins.genList (i: nFields - 1 - i) nFields);
            payloadCtor =
                   if v._payloadTag == "VBootInr" then term.mkBootInr
              else if v._payloadTag == "VBootInl" then term.mkBootInl
              else throw "qmachine chain-form n=1: bad payloadTag ${v._payloadTag}";
            payloadTm = payloadCtor (qf v._payloadLeft) (qf v._payloadRight) innerTm;
            outerTm   = term.mkDescCon (qf v.D) (qf v.i) payloadTm;
          in { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = outerTm; }
        else
          # Chain-form Val (n≥2) → `mkDescConChain` Tm. Setup a `KQ_App` frame
          # quotes the 6 chain-wide sub-Vals (outerD + payload
          # left/right + base.{D,i,d}); the `KQ_DescConChain_Build`
          # terminal frame materialises per-layer Tms via recursive
          # `quote` (through `k.fallback k.d`) and emits one flat
          # `mkDescConChain` Tm. Output Tm walks iteratively under
          # `forceValueDeep`, so its depth is O(1) regardless of n.
          let
            payloadTag = v._payloadTag;
            sixSubVals = [
              { inherit d; v = v.D; }
              { inherit d; v = v._payloadLeft; }
              { inherit d; v = v._payloadRight; }
              { inherit d; v = base.D; }
              { inherit d; v = base.i; }
              { inherit d; v = base.d; }
            ];
            setupMkTm = ts: {
              outerDTm = builtins.elemAt ts 0;
              leftTm   = builtins.elemAt ts 1;
              rightTm  = builtins.elemAt ts 2;
              baseTm   = {
                D = builtins.elemAt ts 3;
                i = builtins.elemAt ts 4;
                d = builtins.elemAt ts 5;
              };
            };
            first      = builtins.head sixSubVals;
            buildFrame = kqDescConChainBuild fallback layers n d payloadTag;
            setupApp   = { tag = "KQ_App"; pending = (builtins.tail sixSubVals); mkTm = setupMkTm; acc = [ ]; };
          in { mode = "Q-Eval"; kont = ({ head = setupApp; tail = ({ head = buildFrame; tail = kont; }); }); fuel = fuel; d = first.d; v = first.v; }

      else
        # Raw recursive VDescCon node → canonicalize via the shared
        # `forceAndPeelChainV` (forces every inspection, recursively
        # flattens nested chain bases). `nFields`/`pTag` for read-back
        # are descriptor-derived: the recursive sub-descriptor's linear
        # profile fixes the per-layer arity and the payload sits in the
        # recursive injection.
        let
          view    = self.descViewF self.defaultFuel v.D;
          bSide   = if view != null && view.idx == 4 then view.B else null;
          profile = if bSide == null then null
                    else self.linearProfileF self.defaultFuel bSide;
          nFields = if profile == null then 0 else builtins.length profile;
          chainNF = self.forceAndPeelChainV "VBootInr" nFields v;
          layers  = chainNF.layers;
          n       = builtins.length layers;
          base    = chainNF.base;
        in
        if n <= 1 then
          # Shallow (n=0: no chain; n=1: a single peelable layer). Quote
          # the outer `v` directly as plain `mkDescCon` so consumers
          # pattern-matching `.d.tag` keep working; `quote v.d`
          # recursively packages the layer payload.
          let fr = { tag = "KQ_App"; pending = [ { inherit d; v = v.i; }
              { inherit d; v = v.d; }
            ]; mkTm = (ts: term.mkDescCon
              (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2)); acc = [ ]; };
          in { mode = "Q-Eval"; kont = ({ head = fr; tail = kont; }); fuel = fuel; d = d; v = v.D; }
        else
          # Deeper canonical-fallback (n≥2) → `mkDescConChain` Tm via
          # the same Build pathway as chain-form. Peel guarantees the
          # recursive injection, so `payloadTag` is fixed.
          let
            payloadTag = "VBootInr";
            sixSubVals = [
              { inherit d; v = v.D; }
              { inherit d; v = chainNF.outerLeft; }
              { inherit d; v = chainNF.outerRight; }
              { inherit d; v = base.D; }
              { inherit d; v = base.i; }
              { inherit d; v = base.d; }
            ];
            setupMkTm = ts: {
              outerDTm = builtins.elemAt ts 0;
              leftTm   = builtins.elemAt ts 1;
              rightTm  = builtins.elemAt ts 2;
              baseTm   = {
                D = builtins.elemAt ts 3;
                i = builtins.elemAt ts 4;
                d = builtins.elemAt ts 5;
              };
            };
            first      = builtins.head sixSubVals;
            buildFrame = kqDescConChainBuild fallback layers n d payloadTag;
            setupApp   = { tag = "KQ_App"; pending = (builtins.tail sixSubVals); mkTm = setupMkTm; acc = [ ]; };
          in { mode = "Q-Eval"; kont = ({ head = setupApp; tail = ({ head = buildFrame; tail = kont; }); }); fuel = fuel; d = first.d; v = first.v; }

    else { mode = "Q-Apply"; kont = kont; fuel = fuel; d = d; tm = (fallback d v); };

  # The quote driver shares `mkStepIf` with the eval driver, parameterized by
  # the caller's `fallback` so Q-Eval's leaf dispatch routes correctly. The
  # outer `genericClosure` advances by |quoteChunkList| steps per operator
  # call; `[]` terminates on Q-Done or exhaustion.
  quoteChunkList = builtins.genList (n: n) 32;
  mkQuoteDriver = fallback:
    let qStepIf = mkStepIf fallback; in
    initState:
      let
        trace = builtins.genericClosure {
          startSet = [ { key = 0; state = initState; } ];
          operator = item:
            if item.state.mode == "Q-Done"
               || item.state.mode == "__exhausted__"
            then [ ]
            else
              let after = builtins.foldl'
                qStepIf item.state quoteChunkList;
              in [ { key = item.key + 1; state = after; } ];
        };
        final = builtins.foldl'
          (acc: item:
            if item.state.mode == "Q-Done"          then item.state.tm
            else if item.state.mode == "__exhausted__"
              then throw "quote budget exceeded"
            else acc)
          null trace;
      in
        if final == null
        then throw "quote: machine produced no Done state (driver bug)"
        else final;

  runQuoteF = fallback:
    let driver = mkQuoteDriver fallback; in
    fuel: d: v: driver { mode = "Q-Eval"; inherit fuel d v; kont = null; };

  # Conversion sub-machine — a defunctionalized `d -> Val -> Val -> Bool` checker.
  #
  # cPeel decomposes one node into a spine-next pair (na/nb at depth nd) plus
  # per-layer sibling goals. Binder arms (VPi/VLam/eta/VSigma) descend a layer via
  # cPeelBinder (nd = d+1, instantiate/vApp); structural arms peel at constant d
  # (nd = d); anything else is a base goal handed whole to convStep.
  #
  #   VPair         spine=.snd        sibling=.fst
  #   Sigma-eta     spine=.snd/vSnd   sibling=.fst/vFst
  #   VBootSum      spine=.left       sibling=.right
  #   VBootInl/Inr  spine=.val        siblings=.left,.right
  cPeel = d: ga: gb:
    let
      a = self.forceVal ga; b = self.forceVal gb;
      ta = a.tag; tb = b.tag;
      goal = x: y: { inherit d; a = x; b = y; };
      binder = fx.tc.conv.cPeelBinder d a b;
    in
         if binder != null then binder
    else if ta == "VPair" && tb == "VPair" then
      { kind = "layer"; goals = [ (goal a.fst b.fst) ]; na = a.snd; nb = b.snd; nd = d; }
    else if ta == "VBootSum" && tb == "VBootSum" then
      { kind = "layer"; goals = [ (goal a.right b.right) ]; na = a.left; nb = b.left; nd = d; }
    else if ta == "VBootInl" && tb == "VBootInl" then
      { kind = "layer"; goals = [ (goal a.left b.left) (goal a.right b.right) ]; na = a.val; nb = b.val; nd = d; }
    else if ta == "VBootInr" && tb == "VBootInr" then
      { kind = "layer"; goals = [ (goal a.left b.left) (goal a.right b.right) ]; na = a.val; nb = b.val; nd = d; }
    else if ta == "VPair" && tb == "VNe" then
      { kind = "layer"; goals = [ (goal a.fst (self.vFst b)) ]; na = a.snd; nb = self.vSnd b; nd = d; }
    else if ta == "VNe" && tb == "VPair" then
      { kind = "layer"; goals = [ (goal (self.vFst a) b.fst) ]; na = self.vSnd a; nb = b.snd; nd = d; }
    else
      { kind = "base"; goals = [ (goal a b) ]; nd = d; };

  # Walk one goal's spine flat. The genericClosure trace is a materialized
  # vector, so map/concatLists over it stay iterative (O(1) C-stack). Returns
  # the per-layer sibling goals plus the spine-terminus base goal.
  cPeelSpine = fuel: g:
    let
      walk = builtins.genericClosure {
        startSet = [ { key = 0; s = cPeel g.d g.a g.b; } ];
        operator = item:
          if item.s.kind == "base" then [ ]
          else if item.key >= fuel then throw "conv budget exceeded"
          else [ { key = item.key + 1; s = cPeel item.s.nd item.s.na item.s.nb; } ];
      };
    in builtins.concatLists (map (it: it.s.goals) walk);

  # BFS over sibling-turns: each round peels every frontier goal's spine flat,
  # runs convStep on the non-structural goals, and routes structural goals into
  # the next frontier — so convStep never recurses on a user-depth value. Flat
  # because the outer genericClosure is keyed by a round counter (branching is
  # in the frontier vector, not the keys), the next frontier is eagerly forced
  # (no lazy frontier cascade), and the verdict is conjoined + branched per
  # round (never force-walked at the end).
  runConvF = fuel: d: a: b:
    let
      isStruct = g: (cPeel g.d g.a g.b).kind == "layer";
      roundStep = st:
        let
          allGoals = builtins.concatLists (map (cPeelSpine fuel) st.frontier);
          tagged   = map (g: { inherit g; s = isStruct g; }) allGoals;
          struct   = map (t: t.g) (builtins.filter (t: t.s) tagged);
          bases    = map (t: t.g) (builtins.filter (t: !t.s) tagged);
          ok       = builtins.all (g: fx.tc.conv.convStep g.d g.a g.b) bases;
          v        = st.verdict && ok;
          nextFrontier = builtins.seq (builtins.length struct) struct;  # force: break the frontier cascade
        in builtins.seq v { frontier = nextFrontier; verdict = v; };
      rounds = builtins.genericClosure {
        startSet = [ { key = 0; st = roundStep { frontier = [ { inherit d a b; } ]; verdict = true; }; } ];
        operator = item:
          if !item.st.verdict then [ ]
          else if item.st.frontier == [ ] then [ ]
          else if item.key >= fuel then throw "conv budget exceeded"
          else [ { key = item.key + 1; st = roundStep item.st; } ];
      };
    in builtins.all (it: it.st.verdict) rounds;

  # Counted sibling of runConvF (shares cPeel/cPeelSpine): identical BFS,
  # differs only in carrying the per-round goal count. steps = Σ |allGoals| —
  # conv obligations dispatched, the work scalar gated by the bench step axis.
  runConvCountedF = fuel: d: a: b:
    let
      isStruct = g: (cPeel g.d g.a g.b).kind == "layer";
      roundStep = st:
        let
          allGoals = builtins.concatLists (map (cPeelSpine fuel) st.frontier);
          tagged   = map (g: { inherit g; s = isStruct g; }) allGoals;
          struct   = map (t: t.g) (builtins.filter (t: t.s) tagged);
          bases    = map (t: t.g) (builtins.filter (t: !t.s) tagged);
          ok       = builtins.all (g: fx.tc.conv.convStep g.d g.a g.b) bases;
          v        = st.verdict && ok;
          nextFrontier = builtins.seq (builtins.length struct) struct;
        in builtins.seq v { frontier = nextFrontier; verdict = v; goals = builtins.length allGoals; };
      rounds = builtins.genericClosure {
        startSet = [ { key = 0; st = roundStep { frontier = [ { inherit d a b; } ]; verdict = true; }; } ];
        operator = item:
          if !item.st.verdict then [ ]
          else if item.st.frontier == [ ] then [ ]
          else if item.key >= fuel then throw "conv budget exceeded"
          else [ { key = item.key + 1; st = roundStep item.st; } ];
      };
    in {
      ok = builtins.all (it: it.st.verdict) rounds;
      steps = builtins.foldl' (acc: it: acc + it.st.goals) 0 rounds;
    };

  T = fx.tc.term;
  H = fx.tc.hoas;

  encRet = H.elab (H.retI H.unit 0 H.tt);

  # Out-of-bounds var: throws if forced, harmless as a thunk.
  broken = T.mkVar 99999;

  noFallback = _d: v: throw "qmachine test: unhandled tag ${v.tag}";
in
{
  scope = {
    inherit runMachineF runMachineCountedF runMachineAtF
      runDescIndAtF runDescIndLayerAtF
      runInterpDAtF runAllDAtF runEverywhereDAtF
      runQuoteF runConvF runConvCountedF;
  };

  tests = {
    "machine-eval-tt"            = { expr = (runMachineF self.defaultFuel [ ] T.mkTt).tag; expected = "VTt"; };
    "machine-eval-unit"          = { expr = (runMachineF self.defaultFuel [ ] T.mkUnit).tag; expected = "VUnit"; };
    "machine-eval-empty"         = { expr = (runMachineF self.defaultFuel [ ] T.mkEmpty).tag; expected = "VEmpty"; };
    "machine-eval-int-lit"       = { expr = (runMachineF self.defaultFuel [ ] (T.mkIntLit 42)).value; expected = 42; };
    "machine-eval-string-lit"    = { expr = (runMachineF self.defaultFuel [ ] (T.mkStringLit "hi")).value; expected = "hi"; };
    "machine-eval-level-zero"    = { expr = (runMachineF self.defaultFuel [ ] T.mkLevelZero).tag; expected = "VLevelZero"; };
    "machine-eval-level-suc"     = { expr = (runMachineF self.defaultFuel [ ] (T.mkLevelSuc T.mkLevelZero)).tag; expected = "VLevelSuc"; };
    "machine-eval-level-max"     = { expr = (runMachineF self.defaultFuel [ ] (T.mkLevelMax T.mkLevelZero T.mkLevelZero)).tag; expected = "VLevelMax"; };
    "machine-eval-U0"            = { expr = (runMachineF self.defaultFuel [ ] (T.mkU T.mkLevelZero)).tag; expected = "VU"; };

    "machine-eval-var-0"         = { expr = (runMachineF self.defaultFuel [ vTt vUnit ] (T.mkVar 0)).tag; expected = "VTt"; };
    "machine-eval-var-1"         = { expr = (runMachineF self.defaultFuel [ vTt vUnit ] (T.mkVar 1)).tag; expected = "VUnit"; };

    "machine-eval-let" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0))).tag;
      expected = "VTt";
    };

    "machine-eval-beta" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt)).tag;
      expected = "VTt";
    };

    # `ev`'s bounded tier (tier 3) builds Vals directly via the shared
    # `eval*V` builders instead of a 2-step machine entry. `fst (pair X tt)`
    # routes X through `ev` (the pair arm's components are ev-thunks);
    # parity against a bare machine run of X pins both paths to the same
    # Val. Empty list = every probe converts.
    "machine-ev-direct-parity" = {
      expr =
        let
          viaEv = x: runMachineF self.defaultFuel [ ]
            (T.mkFst (T.mkPair x T.mkTt));
          bare = x: runMachineF self.defaultFuel [ ] x;
          lv1 = T.mkLevelSuc T.mkLevelZero;
          probes = {
            lam = T.mkLam "x" T.mkUnit (T.mkVar 0);
            pi = T.mkPi "x" T.mkUnit T.mkUnit;
            sigma = T.mkSigma "x" T.mkUnit T.mkUnit;
            pair = T.mkPair T.mkTt T.mkTt;
            boot-sum = T.mkBootSum T.mkUnit T.mkEmpty;
            boot-inl = T.mkBootInl T.mkUnit T.mkUnit T.mkTt;
            boot-inr = T.mkBootInr T.mkUnit T.mkUnit T.mkTt;
            boot-eq = T.mkBootEq T.mkUnit T.mkTt T.mkTt;
            squash = T.mkSquash T.mkUnit;
            squash-intro = T.mkSquashIntro T.mkTt;
            mu = T.mkMu T.mkUnit T.mkTt T.mkTt;
            U1 = T.mkU lv1;
            desc = T.mkDesc T.mkLevelZero T.mkUnit;
            lift-collapse = T.mkLift T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit;
            lift = T.mkLift T.mkLevelZero lv1 T.mkBootRefl T.mkUnit;
            lift-intro = T.mkLiftIntro T.mkLevelZero lv1 T.mkBootRefl T.mkUnit T.mkTt;
            ann-passthrough = T.mkAnn
              (T.mkApp (T.mkLam "y" T.mkUnit (T.mkVar 0)) T.mkTt) T.mkUnit;
          };
        in
        builtins.filter
          (n: !(fx.tc.conv.conv 0 (viaEv probes.${n}) (bare probes.${n})))
          (builtins.attrNames probes);
      expected = [ ];
    };

    "machine-ev-direct-pi-plicity" = {
      expr =
        (runMachineF self.defaultFuel [ ]
          (T.mkFst (T.mkPair
            (T.mkPi "x" T.mkUnit T.mkUnit // { _plicity = "implicit"; })
            T.mkTt)))._plicity or null;
      expected = "implicit";
    };

    # Meta-bearing ann over a deferred-tag term, forced through the
    # bounded tier: the sidecar must land on the real Val — a missing
    # forceVal would glue it onto a VThunkTm wrapper and the driver's
    # unwrap would silently discard it.
    "machine-ev-direct-ann-sidecar" = {
      expr =
        let
          v = runMachineF self.defaultFuel [ ]
            (T.mkFst (T.mkPair
              (T.mkAnn (T.mkApp (T.mkLam "y" T.mkUnit (T.mkVar 0)) T.mkTt)
                T.mkUnit
                // { _label = "probe"; })
              T.mkTt));
        in
        { label = v._label or null; tag = v.tag; };
      expected = { label = "probe"; tag = "VTt"; };
    };

    # Bounded-tier forces never touch a counting run's budget (the eager
    # force previously ran on a fresh defaultFuel, equally invisible);
    # pinned at the pre-bypass step counts.
    "machine-ev-direct-step-neutral" = {
      expr = {
        lamSub = (runMachineCountedF self.defaultFuel [ ]
          (T.mkFst (T.mkPair (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt))).steps;
        annSub = (runMachineCountedF self.defaultFuel [ ]
          (T.mkFst (T.mkPair
            (T.mkAnn (T.mkApp (T.mkLam "y" T.mkUnit (T.mkVar 0)) T.mkTt)
              T.mkUnit)
            T.mkTt))).steps;
      };
      expected = { lamSub = 3; annSub = 3; };
    };

    # Deep let/beta chains build an N-deep cons environment in the
    # iterative machine. Body variants exercise distinct env accesses:
    # tt (no lookup), var 0 (newest binding), var (n-1) (deepest binding,
    # full envNth descent). The chain itself never consumes native stack
    # and the result stays a shallow `.tag`. Regression for the cons-env
    # representation: a Nix-list env (`++` extension) is O(N^2) memory and
    # a cached `depth` field overflows max-call-depth at this depth.
    "machine-let-chain-tt-10000" = {
      expr = (runMachineF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
          T.mkTt (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };
    "machine-let-chain-var0-10000" = {
      expr = (runMachineF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
          (T.mkVar 0) (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };
    "machine-let-chain-deep-10000" = {
      expr = (runMachineF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
          (T.mkVar 9999) (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };
    "machine-beta-chain-10000" = {
      expr = (runMachineF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkApp (T.mkLam "x" T.mkUnit acc) T.mkTt)
          T.mkTt (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };
    "machine-beta-chain-deep-10000" = {
      expr = (runMachineF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkApp (T.mkLam "x" T.mkUnit acc) T.mkTt)
          (T.mkVar 9999) (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };

    # A Val that captures a deep environment internally (a VLam closure
    # over a 10000-deep env) quotes to a shallow, env-erased Tm: the deep
    # env lives only inside the machine and is never reachable by an
    # external deep-force. Quoting instantiates the body under the deep
    # env (single O(1) index-0 read) and the result carries no env.
    "machine-deep-env-quote-erased" = {
      expr =
        let
          deepLam = runMachineF self.defaultFuel [ ]
            (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
              (T.mkLam "y" T.mkUnit (T.mkVar 0))
              (builtins.genList (i: i) 10000));
          q = runQuoteF noFallback self.defaultFuel 0 deepLam;
        in { tag = q.tag; body = q.body.tag; };
      expected = { tag = "lam"; body = "var"; };
    };

    "machine-eval-lam-closure" = {
      expr = (runMachineF self.defaultFuel [ vTt ]
        (T.mkLam "x" T.mkUnit (T.mkVar 1))).tag;
      expected = "VLam";
    };

    "machine-eval-pi" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkPi "x" T.mkUnit T.mkUnit)).tag;
      expected = "VPi";
    };

    "machine-eval-sigma" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkSigma "x" T.mkUnit T.mkUnit)).tag;
      expected = "VSigma";
    };

    "machine-eval-pair-fst" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkFst (T.mkPair T.mkTt T.mkUnit))).tag;
      expected = "VTt";
    };
    "machine-eval-pair-snd" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkSnd (T.mkPair T.mkTt T.mkUnit))).tag;
      expected = "VUnit";
    };
    "machine-eval-fst-stuck" = {
      expr = (runMachineF self.defaultFuel [ (freshVar 0) ]
        (T.mkFst (T.mkVar 0))).tag;
      expected = "VNe";
    };
    "machine-eval-snd-stuck" = {
      expr = (runMachineF self.defaultFuel [ (freshVar 0) ]
        (T.mkSnd (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "machine-eval-ann" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkAnn T.mkTt T.mkUnit)).tag;
      expected = "VTt";
    };

    "machine-eval-ann-descRef" = {
      expr =
        let descRef = {
              I = T.mkUnit;
              level = T.mkLevelZero;
              params = [ T.mkTt ];
              kind = "x";
            };
        in (runMachineF self.defaultFuel [ ]
             ((T.mkAnn T.mkTt T.mkUnit) // { _descRef = descRef; }))._descRef.I.tag;
      expected = "VUnit";
    };

    "machine-eval-ann-label" = {
      expr = (runMachineF self.defaultFuel [ ]
        ((T.mkAnn T.mkTt T.mkUnit) // { _label = "tag-x"; }))._label;
      expected = "tag-x";
    };
    "machine-eval-ann-conLabel" = {
      expr = (runMachineF self.defaultFuel [ ]
        ((T.mkAnn T.mkTt T.mkUnit) // { _conLabel = "ctor-x"; }))._conLabel;
      expected = "ctor-x";
    };

    "machine-eval-pi-plicity" = {
      expr = (runMachineF self.defaultFuel [ ]
        ((T.mkPi "x" T.mkUnit T.mkUnit) // { _plicity = "implicit"; }))._plicity;
      expected = "implicit";
    };

    "machine-eval-lam-plicity" = {
      expr = (runMachineF self.defaultFuel [ ]
        ((T.mkLam "x" T.mkUnit (T.mkVar 0)) // { _plicity = "implicit"; }))._plicity;
      expected = "implicit";
    };

    "machine-eval-boot-sum-elim-inl" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootSumElim T.mkUnit T.mkUnit
          (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
          (T.mkLam "x" T.mkUnit T.mkTt)
          (T.mkLam "y" T.mkUnit T.mkTt)
          (T.mkBootInl T.mkUnit T.mkUnit T.mkTt))).tag;
      expected = "VTt";
    };
    "machine-eval-boot-sum-elim-inr" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootSumElim T.mkUnit T.mkUnit
          (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
          (T.mkLam "x" T.mkUnit T.mkTt)
          (T.mkLam "y" T.mkUnit T.mkTt)
          (T.mkBootInr T.mkUnit T.mkUnit T.mkTt))).tag;
      expected = "VTt";
    };
    "machine-eval-boot-sum-elim-stuck" = {
      expr = (runMachineF self.defaultFuel [ (freshVar 0) ]
        (T.mkBootSumElim T.mkUnit T.mkUnit
          (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
          (T.mkLam "x" T.mkUnit T.mkTt)
          (T.mkLam "y" T.mkUnit T.mkTt)
          (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "machine-eval-boot-j-refl" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootJ T.mkUnit T.mkTt
          (T.mkLam "y" T.mkUnit
            (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) T.mkUnit))
          T.mkTt T.mkTt T.mkBootRefl)).tag;
      expected = "VTt";
    };
    "machine-eval-boot-j-stuck" = {
      expr = (runMachineF self.defaultFuel [ (freshVar 0) ]
        (T.mkBootJ T.mkUnit T.mkTt
          (T.mkLam "y" T.mkUnit
            (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) T.mkUnit))
          T.mkTt T.mkTt (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "machine-eval-squash-intro" = {
      expr = (runMachineF self.defaultFuel [ ] (T.mkSquashIntro T.mkTt)).tag;
      expected = "VSquashIntro";
    };

    "machine-eval-mu" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkMu T.mkUnit encRet T.mkTt)).tag;
      expected = "VMu";
    };

    "machine-eval-desc-con" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkDescCon encRet T.mkTt T.mkBootRefl)).tag;
      expected = "VDescCon";
    };

    "machine-eval-lift-idempotent" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLift T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit)).tag;
      expected = "VUnit";
    };

    "machine-eval-lift-intro-idempotent" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLiftIntro T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };

    "machine-eval-lift-elim-idempotent" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLiftElim T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };

    "machine-eval-desc-desc-app-canonRef" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.id;
      expected = "descDesc";
    };

    "machine-eval-U-nonzero" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkU (T.mkLevelSuc T.mkLevelZero))).tag;
      expected = "VU";
    };

    "machine-eval-str-eq-stuck" = {
      expr = (runMachineF self.defaultFuel [ (freshVar 0) ]
        (T.mkStrEq (T.mkVar 0) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "machine-fuel-exhaustion-throws" = {
      expr = builtins.tryEval (runMachineF 1 [ ] T.mkTt);
      expected = { success = false; value = false; };
    };

    "machine-force-pair-snd-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkPair T.mkTt broken)).tag;
      expected = "VPair";
    };
    "machine-force-boot-sum-right-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootSum T.mkUnit broken)).tag;
      expected = "VBootSum";
    };
    "machine-force-boot-inl-right-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootInl T.mkUnit broken T.mkTt)).tag;
      expected = "VBootInl";
    };
    "machine-force-boot-inr-left-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootInr broken T.mkUnit T.mkTt)).tag;
      expected = "VBootInr";
    };
    "machine-force-boot-eq-rhs-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkBootEq T.mkUnit T.mkTt broken)).tag;
      expected = "VBootEq";
    };
    "machine-force-mu-D-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkMu T.mkUnit broken T.mkTt)).tag;
      expected = "VMu";
    };
    "machine-force-lift-eq-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero) broken T.mkUnit)).tag;
      expected = "VLift";
    };
    "machine-force-lift-intro-eq-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero) broken T.mkUnit T.mkTt)).tag;
      expected = "VLiftIntro";
    };
    "machine-force-squash-A-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkSquash broken)).tag;
      expected = "VSquash";
    };
    "machine-force-squash-intro-a-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkSquashIntro broken)).tag;
      expected = "VSquashIntro";
    };
    "machine-force-level-suc-pred-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLevelSuc broken)).tag;
      expected = "VLevelSuc";
    };
    "machine-force-level-max-rhs-unforced" = {
      expr = (runMachineF self.defaultFuel [ ]
        (T.mkLevelMax T.mkLevelZero broken)).tag;
      expected = "VLevelMax";
    };

    "qmachine-tt" = {
      expr = runQuoteF noFallback self.defaultFuel 0 vTt;
      expected = T.mkTt;
    };
    "qmachine-unit" = {
      expr = runQuoteF noFallback self.defaultFuel 0 vUnit;
      expected = T.mkUnit;
    };
    "qmachine-level-zero" = {
      expr = runQuoteF noFallback self.defaultFuel 0 vLevelZero;
      expected = T.mkLevelZero;
    };
    "qmachine-int-lit" = {
      expr = runQuoteF noFallback self.defaultFuel 0 (vIntLit 42);
      expected = T.mkIntLit 42;
    };
    "qmachine-string-lit" = {
      expr = runQuoteF noFallback self.defaultFuel 0 (vStringLit "hi");
      expected = T.mkStringLit "hi";
    };
    "qmachine-pair-tt-tt" = {
      expr = runQuoteF noFallback self.defaultFuel 0 (vPair vTt vTt);
      expected = T.mkPair T.mkTt T.mkTt;
    };
    "qmachine-pair-unit-tt" = {
      expr = runQuoteF noFallback self.defaultFuel 0 (vPair vUnit vTt);
      expected = T.mkPair T.mkUnit T.mkTt;
    };
    "qmachine-pair-nested" = {
      expr = runQuoteF noFallback self.defaultFuel 0
        (vPair (vPair vTt vUnit) (vPair vTt vTt));
      expected = T.mkPair
        (T.mkPair T.mkTt T.mkUnit)
        (T.mkPair T.mkTt T.mkTt);
    };
    "qmachine-fallback-receives-d-and-v" = {
      expr =
        let fb = d: v: T.mkStringLit "fb:${v.tag}:${toString d}"; in
        runQuoteF fb self.defaultFuel 3 (vSquash vUnit);
      expected = T.mkStringLit "fb:VSquash:3";
    };
    "qmachine-fallback-inside-pair" = {
      expr =
        let fb = _d: v: T.mkStringLit "fb:${v.tag}"; in
        runQuoteF fb self.defaultFuel 0
          (vPair (vSquash vUnit) vTt);
      expected = T.mkPair (T.mkStringLit "fb:VSquash") T.mkTt;
    };

    "qmachine-pi-tag" = {
      expr = (runQuoteF noFallback self.defaultFuel 0
        (vPi "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
      expected = "pi";
    };
    "qmachine-sigma-tag" = {
      expr = (runQuoteF noFallback self.defaultFuel 0
        (vSigma "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
      expected = "sigma";
    };
    "qmachine-pi-domain-and-codomain" = {
      expr = runQuoteF noFallback self.defaultFuel 0
        (vPi "x" vUnit (mkClosure [ ] T.mkUnit));
      expected = T.mkPi "x" T.mkUnit T.mkUnit;
    };
    "qmachine-lam-nested-pair-body" = {
      expr =
        let r = runQuoteF noFallback self.defaultFuel 0
          (vLam "x" vUnit
            (mkClosure [ ] (T.mkPair (T.mkVar 0) T.mkTt)));
        in r.body.tag;
      expected = "pair";
    };

    "qmachine-ne-var-shallow" = {
      expr = (runQuoteF noFallback self.defaultFuel 1 (vNe 0 [ ])).idx;
      expected = 0;
    };
    "qmachine-ne-var-deep" = {
      expr = (runQuoteF noFallback self.defaultFuel 3 (vNe 0 [ ])).idx;
      expected = 2;
    };
    "qmachine-ne-app" = {
      expr = runQuoteF noFallback self.defaultFuel 1
        (vNe 0 [ (eApp vTt) ]);
      expected = T.mkApp (T.mkVar 0) T.mkTt;
    };
    "qmachine-ne-fst-snd-chain" = {
      expr = (runQuoteF noFallback self.defaultFuel 1
        (vNe 0 [ eFst eSnd ])).tag;
      expected = "snd";
    };
    "qmachine-ne-boot-sum-elim" = {
      expr = (runQuoteF noFallback self.defaultFuel 1
        (vNe 0 [ (eBootSumElim vUnit vUnit vUnit vTt vTt) ])).tag;
      expected = "boot-sum-elim";
    };
    "qmachine-ne-interp-d-level-zero" = {
      expr = (runQuoteF noFallback self.defaultFuel 1
        (vNe 0 [ (eInterpD vLevelZero vUnit vUnit vTt) ])).level.tag;
      expected = "level-zero";
    };

    # Eliminator depth-flatness regression. Each chain nests N copies of one
    # eliminator in its scrutinee position over a neutral seed, so the machine
    # pushes N resume frames during eval descent and the read-back driver walks
    # an N-element spine. A depth-flat machine processes both in O(1) libnix
    # call frames; a regression that reintroduces depth-proportional Nix
    # call-depth overflows `max-call-depth` well before N=1000. `spine` confirms
    # eval materialised the full stuck spine (lift-elim is idempotent at equal
    # levels, so it collapses to the bare neutral); `head` confirms read-back is
    # iterative. The eliminators' non-scrutinee arguments ride on deferred
    # `VThunkTm` sub-evaluation, forced by the same driver — no per-argument
    # frame is needed.
    "machine-elim-depth-lift-elim-1000" = {
      expr =
        let
          lz = T.mkLevelZero; u = T.mkUnit;
          chain = builtins.foldl' (acc: _: T.mkLiftElim lz lz T.mkBootRefl u acc)
            (T.mkVar 0) (builtins.genList (i: i) 1000);
          v = runMachineF self.defaultFuel [ (freshVar 0) ] chain;
        in { tag = v.tag; spine = builtins.length v.spine;
             head = (runQuoteF noFallback self.defaultFuel 1 v).tag; };
      expected = { tag = "VNe"; spine = 0; head = "var"; };
    };
    "machine-elim-depth-boot-sum-elim-1000" = {
      expr =
        let
          u = T.mkUnit; mot = T.mkLam "_" u (T.mkVar 0);
          chain = builtins.foldl' (acc: _: T.mkBootSumElim u u mot mot mot acc)
            (T.mkVar 0) (builtins.genList (i: i) 1000);
          v = runMachineF self.defaultFuel [ (freshVar 0) ] chain;
        in { tag = v.tag; spine = builtins.length v.spine;
             head = (runQuoteF noFallback self.defaultFuel 1 v).tag; };
      expected = { tag = "VNe"; spine = 1000; head = "boot-sum-elim"; };
    };
    "machine-elim-depth-boot-j-1000" = {
      expr =
        let
          u = T.mkUnit; tt = T.mkTt; mot = T.mkLam "_" u (T.mkVar 0);
          chain = builtins.foldl' (acc: _: T.mkBootJ u tt mot tt tt acc)
            (T.mkVar 0) (builtins.genList (i: i) 1000);
          v = runMachineF self.defaultFuel [ (freshVar 0) ] chain;
        in { tag = v.tag; spine = builtins.length v.spine;
             head = (runQuoteF noFallback self.defaultFuel 1 v).tag; };
      expected = { tag = "VNe"; spine = 1000; head = "boot-j"; };
    };
    "machine-elim-depth-squash-elim-1000" = {
      expr =
        let
          u = T.mkUnit; mot = T.mkLam "_" u (T.mkVar 0);
          chain = builtins.foldl' (acc: _: T.mkSquashElim u u mot acc)
            (T.mkVar 0) (builtins.genList (i: i) 1000);
          v = runMachineF self.defaultFuel [ (freshVar 0) ] chain;
        in { tag = v.tag; spine = builtins.length v.spine;
             head = (runQuoteF noFallback self.defaultFuel 1 v).tag; };
      expected = { tag = "VNe"; spine = 1000; head = "squash-elim"; };
    };

    # Deep application spine: a free variable applied to N arguments. The
    # machine descends N application frames (threading env/kont by reference)
    # then snocs N frames onto the neutral; `spine` forces full in-order
    # materialisation. N is set above the libnix coroutine-stack ceiling
    # (~17000 frames at the 8 MiB default) so the test fails if the eval
    # descent reintroduces an N-deep attribute-select chain on the threaded
    # env/kont, or the spine reverts to an O(N) `++` snoc whose flattening
    # recurses N-deep. The shallower elim-depth chains above do not reach this
    # ceiling; this is the spine representation's depth sentinel.
    "machine-app-spine-depth-20000" = {
      expr =
        let
          chain = builtins.foldl' (acc: _: T.mkApp acc T.mkTt)
            (T.mkVar 0) (builtins.genList (i: i) 20000);
          v = runMachineF self.defaultFuel [ (freshVar 0) ] chain;
        in { tag = v.tag; spine = builtins.length v.spine; };
      expected = { tag = "VNe"; spine = 20000; };
    };

    # conv depth-flatness: N-deep nested values conv'd against themselves;
    # runConvF walks the spine on its goal stack in O(1) libnix frames. The
    # recursive `convStep` overflows the OS stack near ~5000, so N=10000 is the
    # depth sentinel. neq + short-circuit cases guard correctness.
    "machine-conv-depth-pair-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vPair vTt acc) vTt (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-bootinl-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vBootInl vUnit vUnit acc) vBootRefl (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-bootsum-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vBootSum acc vUnit) vUnit (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-pair-neq" = {
      expr =
        let mk = leaf: builtins.foldl' (acc: _: vPair vTt acc) leaf (builtins.genList (i: i) 1000);
        in runConvF self.defaultFuel 0 (mk vTt) (mk vUnit);
      expected = false;
    };
    "machine-conv-shortcircuit-false" = {
      expr = runConvF self.defaultFuel 0 (vPair vTt vUnit) (vPair vUnit vUnit);
      expected = false;
    };

    # Counted conv: steps = goals dispatched (Σ |allGoals| per round). A spine
    # chain emits one sibling goal per layer plus the terminus base (n+1);
    # bootInl emits two sibling goals per layer (2n+1). Goal count is a law of
    # the value pair — the neq chain dispatches the same goals.
    "machine-conv-counted-pair-1000" = {
      expr =
        let c = builtins.foldl' (acc: _: vPair vTt acc) vTt (builtins.genList (i: i) 1000);
        in runConvCountedF self.defaultFuel 0 c c;
      expected = { ok = true; steps = 1001; };
    };
    "machine-conv-counted-bootinl-1000" = {
      expr =
        let c = builtins.foldl' (acc: _: vBootInl vUnit vUnit acc) vBootRefl (builtins.genList (i: i) 1000);
        in runConvCountedF self.defaultFuel 0 c c;
      expected = { ok = true; steps = 2001; };
    };
    "machine-conv-counted-neq" = {
      expr =
        let mk = leaf: builtins.foldl' (acc: _: vPair vTt acc) leaf (builtins.genList (i: i) 1000);
        in runConvCountedF self.defaultFuel 0 (mk vTt) (mk vUnit);
      expected = { ok = false; steps = 1001; };
    };

    # Sibling-direction + balanced depth: these nest away from the spine, so the
    # spine-peeler bounced them off convStep and overflowed; the BFS frontier
    # keeps them flat.
    "machine-conv-depth-pair-left-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vPair acc vTt) vTt (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-bootsum-right-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vBootSum vUnit acc) vUnit (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-bootinl-left-10000" = {
      expr =
        let c = builtins.foldl' (acc: _: vBootInl acc vUnit vBootRefl) vBootRefl (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 c c;
      expected = true;
    };
    "machine-conv-depth-pair-balanced" = {
      expr =
        let t = d: if d == 0 then vTt else (let s = t (d - 1); in vPair s s);
        in runConvF self.defaultFuel 0 (t 14) (t 14);
      expected = true;
    };
    "machine-conv-depth-pair-left-neq" = {
      expr =
        let mk = leaf: builtins.foldl' (acc: _: vPair acc vTt) leaf (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0 (mk vTt) (mk vUnit);
      expected = false;
    };

    # Binder-descent depth-flatness: deep Pi/Lam/Sigma/eta chains conv'd against
    # themselves descend one binder layer per spine step (instantiate/vApp at d+1)
    # on runConvF's BFS, staying O(1) in libnix frames. The recursive convStep
    # binder/eta arms overflow near ~500, so N=10000 is the sentinel.
    "machine-conv-depth-pi-10000" = {
      expr =
        let
          u = T.mkUnit;
          t = builtins.foldl' (cod: _: T.mkPi "x" u cod) u (builtins.genList (i: i) 10000);
          v = runMachineF self.defaultFuel [ ] t;
        in runConvF self.defaultFuel 0 v v;
      expected = true;
    };
    "machine-conv-depth-lamlam-10000" = {
      expr =
        let
          u = T.mkUnit;
          t = builtins.foldl' (body: _: T.mkLam "x" u body) T.mkTt (builtins.genList (i: i) 10000);
          v = runMachineF self.defaultFuel [ ] t;
        in runConvF self.defaultFuel 0 v v;
      expected = true;
    };
    "machine-conv-depth-eta-10000" = {
      expr =
        let
          u = T.mkUnit;
          t = builtins.foldl' (body: _: T.mkLam "x" u body) T.mkTt (builtins.genList (i: i) 10000);
          v = runMachineF self.defaultFuel [ ] t;
        in runConvF self.defaultFuel 0 v (freshVar 0);
      expected = true;
    };
    "machine-conv-depth-sigma-10000" = {
      expr =
        let
          u = T.mkUnit;
          t = builtins.foldl' (snd: _: T.mkSigma "x" u snd) u (builtins.genList (i: i) 10000);
          v = runMachineF self.defaultFuel [ ] t;
        in runConvF self.defaultFuel 0 v v;
      expected = true;
    };
    # 5000 VPair∘VLam layers = 10000 interleaved structural+binder turns, one spine.
    "machine-conv-depth-mixed-10000" = {
      expr =
        let
          u = T.mkUnit;
          t = builtins.foldl' (acc: _: T.mkPair T.mkTt (T.mkLam "x" u acc)) T.mkTt (builtins.genList (i: i) 5000);
          v = runMachineF self.defaultFuel [ ] t;
        in runConvF self.defaultFuel 0 v v;
      expected = true;
    };

    # Binder-arm correctness.
    "machine-conv-pi-neq" = {
      expr =
        let
          u = T.mkUnit;
          v1 = runMachineF self.defaultFuel [ ] (T.mkPi "x" u u);
          v2 = runMachineF self.defaultFuel [ ] (T.mkPi "x" u (T.mkPi "y" u u));
        in runConvF self.defaultFuel 0 v1 v2;
      expected = false;
    };
    # λx. f x (syntactic eta) ≡ f via the etaReducedFn shortcut (no fresh-var descent).
    "machine-conv-eta-shortcut" = {
      expr =
        let
          u = T.mkUnit; f = freshVar 0;
          v = runMachineF self.defaultFuel [ f ] (T.mkLam "x" u (T.mkApp (T.mkVar 1) (T.mkVar 0)));
        in runConvF self.defaultFuel 0 v f;
      expected = true;
    };
    "machine-conv-lamlam-neq" = {
      expr =
        let
          u = T.mkUnit;
          mk = leaf: builtins.foldl' (body: _: T.mkLam "x" u body) leaf (builtins.genList (i: i) 10000);
        in runConvF self.defaultFuel 0
          (runMachineF self.defaultFuel [ ] (mk T.mkTt))
          (runMachineF self.defaultFuel [ ] (mk T.mkUnit));
      expected = false;
    };
  };
}
