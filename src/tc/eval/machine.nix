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
    vTt vUnit vEmpty vNe vLam vPi vSigma vPair
    vBootSum vBootInl vBootInr vBootEq vBootRefl vFunext
    vSquash vSquashIntro
    vDescAt vMu vDescCon vDescConChain vU vLazyDescIndAccLayer vThunkTm
    vLevel vLevelZero vLevelSuc vLevelMax vLiftIntro
    vString vInt vFloat vAttrs vPath vDerivation vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vDerivationLit vFnLit vAnyLit
    eApp eFst eSnd eBootSumElim eBootJ eInterpD eAllD eEverywhereD eDescInd;
  vUZero = vU vLevelZero;

  push = frame: kont: { head = frame; tail = kont; };

  # Force-required frames: each resume needs `c.v` forced to dispatch on `.tag`.
  # All other sub-Tm propagation goes through Nix-lazy thunks via `c.lazy` /
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
  # context plus the originally-consumed val, then `mkApply` on the sub-Val.
  # `stepApply`'s top-level VThunkTm peek transitions to Eval inside the same
  # driver; on return the resume handler rebuilds H with the forced field
  # substituted and re-delivers the consumed val. No fresh `runMachineF`.
  kForceFor       = { tag = "KForceFor"; };
  # Q→Eval→Q transition: forced val lands as state.val; resume pops itself
  # and switches state back to Q-Eval at binder depth `d`.
  kqResumeQuote   = d:               { tag = "KQResumeQuote";        inherit d; };
  kResume_KAllD_d        = L: I: K: X: M: i: D:
    { tag = "KResume_KAllD_d";        inherit L I K X M i D; };
  kResume_KEverywhereD_d = L: I: K: X: M: ih: i: D:
    { tag = "KResume_KEverywhereD_d"; inherit L I K X M ih i D; };
  kResume_KDescInd_motive = D: step: i: scrut:
    { tag = "KResume_KDescInd_motive"; inherit D step i scrut; };

  # Helper dispatchers. Each runs the corresponding `desc.nix` helper under
  # the unified driver and delivers the result to the paired `*_Got*` resume
  # frame structurally seated immediately above on the kont. The inspected
  # value flows through `state.val` (forced by `stepApply`'s top-level peek
  # if needed); only `kPeelLiftIntroVal` carries an accumulator field.
  kDescView         = { tag = "KDescView";         };
  kqDescView        = { tag = "KQDescView";        };
  kSumPayloadView   = { tag = "KSumPayloadView";   };
  kPeelLiftIntroVal = rb: { tag = "KPeelLiftIntroVal"; rebuildAcc = rb; };

  # Iterative walker frames over descCon chains.
  kCollectPairs = nFields: ii: acc: payload:
    { tag = "KCollectPairs"; inherit nFields ii acc payload; };
  kPeel = D: linear: payloadTag: nFields:
    { tag = "KPeel"; inherit D linear payloadTag nFields; };

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

  # Continuations for the `vFst` / `vSnd` chain at each handler branch:
  # `kFst d → *_GotFstD → kSnd d → *_GotSndD → original consumer push`.
  kResume_KAllD_view1_GotFstD = L: I: K: X: M: i: d: tFn:
    { tag = "KResume_KAllD_view1_GotFstD"; inherit L I K X M i d tFn; };
  kResume_KAllD_view1_GotSndD = L: I: K: X: M: i: fstD: tFn:
    { tag = "KResume_KAllD_view1_GotSndD"; inherit L I K X M i fstD tFn; };
  kResume_KAllD_view2_GotFstD = L: I: K: X: M: i: d: sub: j:
    { tag = "KResume_KAllD_view2_GotFstD"; inherit L I K X M i d sub j; };
  kResume_KAllD_view2_GotSndD = L: I: K: X: M: i: fstD: sub: j:
    { tag = "KResume_KAllD_view2_GotSndD"; inherit L I K X M i fstD sub j; };
  kResume_KAllD_view3_GotFstD = L: I: K: X: M: i: d: sTy: sub: fn:
    { tag = "KResume_KAllD_view3_GotFstD"; inherit L I K X M i d sTy sub fn; };
  kResume_KAllD_view3_GotSndD = L: I: K: X: M: i: fstD: sTy: sub: fn:
    { tag = "KResume_KAllD_view3_GotSndD"; inherit L I K X M i fstD sTy sub fn; };
  kResume_KEverywhereD_view1_GotFstD = L: I: K: X: M: ih: i: d: tFn:
    { tag = "KResume_KEverywhereD_view1_GotFstD"; inherit L I K X M ih i d tFn; };
  kResume_KEverywhereD_view1_GotSndD = L: I: K: X: M: ih: i: fstD: tFn:
    { tag = "KResume_KEverywhereD_view1_GotSndD"; inherit L I K X M ih i fstD tFn; };
  kResume_KEverywhereD_view2_GotFstD = L: I: K: X: M: ih: i: d: sub: j:
    { tag = "KResume_KEverywhereD_view2_GotFstD"; inherit L I K X M ih i d sub j; };
  kResume_KEverywhereD_view2_GotSndD = L: I: K: X: M: ih: i: fstD: sub: j:
    { tag = "KResume_KEverywhereD_view2_GotSndD"; inherit L I K X M ih i fstD sub j; };
  kResume_KEverywhereD_view3_GotFstD = L: I: K: X: M: ih: i: d: sTy: sub: fn:
    { tag = "KResume_KEverywhereD_view3_GotFstD"; inherit L I K X M ih i d sTy sub fn; };
  kResume_KEverywhereD_view3_GotSndD = L: I: K: X: M: ih: i: fstD: sTy: sub: fn:
    { tag = "KResume_KEverywhereD_view3_GotSndD"; inherit L I K X M ih i fstD sTy sub fn; };

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
  # next sub-Val via `mkApply` (stepApply's top-level VThunkTm peek does the
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

  # Eval-lift frames for `KDescConPeel_BaseD` layer/head evaluation and
  # `KDescConPeel_Start` sameD comparison.
  kEvalLayerI    = env: layerTm:                { tag = "KEvalLayerI";    inherit env layerTm; };
  kEvalLayerHead = env: heads: idx: layerAccum: { tag = "KEvalLayerHead"; inherit env heads idx layerAccum; };
  kEvalForConv   = depth: dVal:                 { tag = "KEvalForConv";   inherit depth dVal; };

  # Each step pays one fuel.
  mkApply = kont: fuel: v:       { mode = "Apply"; val = v; inherit kont; fuel = fuel - 1; };
  mkEval  = kont: fuel: env: tm: { mode = "Eval"; inherit env tm kont; fuel = fuel - 1; };
  mkDone  = fuel: v:             { mode = "Done"; val = v; inherit fuel; };

  # Force a `VLazyDescIndAccLayer` Val by expanding into three kAppVV frames
  # plus re-pushing the current dispatch frame on top of c.rest. After the
  # three force-apps consume — applying step to (layer.i, layer.d,
  # vPair prevAcc vTt) — the layer's accumulator value (a VLam, or another
  # VLazyDescIndAccLayer that this same helper re-fires) lands as `c.v` on
  # the original frame, which then re-dispatches with the resolved value.
  # The cascade lives entirely in the driver's kont stack; libnix sees
  # one frame regardless of chain depth.
  forceLazyLayer = c:
    let fn = c.v; in
    mkApply
      (push (kAppVV fn.i)
        (push (kAppVV fn.d)
          (push (kAppVV (vPair fn.prevAcc vTt))
            (push c.k c.rest))))
      c.fuel fn.step;

  # Defunctionalised VDescViewFn dispatch from `KApp1` / `KApp_VV`.
  # The "vapp" kind — the only shape whose body re-enters `runMachineF`
  # via `vAppF → instantiateF` — is resolved by frame-pushing
  # `kAppVV liftedArg` on `tPayload` and transitioning to Apply mode,
  # keeping the cascade inside the same driver. Other kinds are pure
  # value-constructor composition; resolve them synchronously through
  # the shared `applyDescViewFnByKindF` helper.
  applyDescViewFnArm = c: fn: arg:
    if fn.kind == "vapp" then
      let liftedArg =
        if fn.noLift then arg
        else self.vLiftIntroF fn.liftK fn.liftDDescL vBootRefl fn.liftSTy arg;
      in mkApply (push (kAppVV liftedArg) c.rest) c.fuel fn.tPayload
    else c.apply (self.applyDescViewFnByKindF c.fuel fn arg);

  # Sub-evaluator handle for lazy sub-Tm thunks at introduction-form
  # call sites. Two tiers:
  #
  #   1. Atomic tags (literals, singletons, var lookup, `U(0)`) — Val
  #      produced inline; no driver, no recursion.
  #   2. Everything else — wrapped as a deferred `VThunkTm { env; tm }`.
  #      Forced lazily at the consumer (eval-side `stepApply` peek,
  #      quote-side `mkQEvalStep` peek, or `forceVal` outside the
  #      machine). Top-level results are forced by the driver's `Done`
  #      arm in `stepIf`, so external callers see non-VThunkTm Vals.
  # Tags whose evaluation recurses through `eval` (application, let, the
  # eliminator and desc-ind families) stay deferred, so the single driver
  # loop handles their recursion iteratively and libnix stack depth stays
  # independent of user-recursion depth. Every other tag holds a bounded
  # type/description/constructor position and is forced to a concrete Val,
  # so Nix thunk-memoization classifies each description once rather than
  # re-deriving it on every force.
  evDeferTags = {
    "app" = true; "let" = true; "fst" = true; "snd" = true;
    "absurd" = true; "boot-sum-elim" = true; "boot-j" = true;
    "squash-elim" = true; "lift-elim" = true; "str-eq" = true;
    "desc-ind" = true; "interp-d" = true; "all-d" = true;
    "everywhere-d" = true;
  };
  ev = env: tm:
    let t = tm.tag; in
         if t == "var"            then builtins.elemAt env tm.idx
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
    else if evDeferTags ? ${t} then vThunkTm env tm
    else self.forceVal (vThunkTm env tm);

  # Lazy `_descRef` finalizer: mirrors `core.nix:428-433`'s `evalDescRef`.
  # All fields stay as Nix thunks; consumers (typechecker) force on demand.
  evalDescRefLazy = env: ref: ref // {
    I = ev env ref.I;
    level = ev env ref.level;
    params = map (ev env) (ref.params or [ ]);
  };

  evalDispatch = {
    "var" = c: c.apply (builtins.elemAt c.env c.tm.idx);

    "unit"           = c: c.apply vUnit;
    "tt"             = c: c.apply vTt;
    "empty"          = c: c.apply vEmpty;
    "boot-refl"      = c: c.apply vBootRefl;
    "funext"         = c: c.apply vFunext;
    "level"          = c: c.apply vLevel;
    "level-zero"     = c: c.apply vLevelZero;
    "string"         = c: c.apply vString;
    "int"            = c: c.apply vInt;
    "float"          = c: c.apply vFloat;
    "attrs"          = c: c.apply vAttrs;
    "path"           = c: c.apply vPath;
    "derivation"     = c: c.apply vDerivation;
    "function"       = c: c.apply vFunction;
    "any"            = c: c.apply vAny;
    "string-lit"     = c: c.apply (vStringLit c.tm.value);
    "int-lit"        = c: c.apply (vIntLit c.tm.value);
    "float-lit"      = c: c.apply (vFloatLit c.tm.value);
    "attrs-lit"      = c: c.apply vAttrsLit;
    "path-lit"       = c: c.apply vPathLit;
    "derivation-lit" = c: c.apply vDerivationLit;
    "fn-lit"         = c: c.apply vFnLit;
    "any-lit"        = c: c.apply vAnyLit;
    "lit-val"        = c: c.apply c.tm.val;

    # `let` and `ann` are propagating-only dispatchers — no kont frame.
    # `let`: HEAD threads the binding as a thunk into env[0] and continues
    # evaluation of body in-place; the let's Val IS the body's Val.
    # `ann`: HEAD merges sidecars onto a thunk-Val via `//`; no field is
    # forced at eval time (typechecker reads `_descRef` etc. later).
    "let"   = c: mkEval c.kont c.fuel ([ (c.lazy c.tm.val) ] ++ c.env) c.tm.body;
    "ann"   = c:
      let
        # Meta-bearing anns wrap descriptions (shallow, always inspected).
        # Force to WHNF before gluing the sidecar so it lands on the real
        # Val, not a VThunkTm wrapper — `forceVal`/`stepApply` discard
        # wrapper attrs when unwrapping a thunk, which would silently drop
        # `_descRef`/`_label`/`_conLabel` the typechecker reads later.
        hasMeta = c.tm ? _descRef || c.tm ? _label || c.tm ? _conLabel;
        v  = if hasMeta then self.forceVal (c.lazy c.tm.term) else c.lazy c.tm.term;
        v1 = if c.tm ? _descRef then v // { _descRef = evalDescRefLazy c.env c.tm._descRef; } else v;
        v2 = if c.tm ? _label    then v1 // { _label    = c.tm._label;    } else v1;
        v3 = if c.tm ? _conLabel then v2 // { _conLabel = c.tm._conLabel; } else v2;
      in c.apply v3;
    # Binder domains/fst and pair components are all propagated as lazy
    # thunks: their consumers (closure body, projection, conv) force on
    # demand. Matches HEAD's `vLam tm.name (ev tm.domain) (mkClosure ...)`.
    "pi"    = c:
      let v = vPi c.tm.name (c.lazy c.tm.domain) (mkClosure c.env c.tm.codomain); in
      c.apply (if c.tm ? _plicity then v // { _plicity = c.tm._plicity; } else v);
    "lam"   = c:
      let v = vLam c.tm.name (c.lazy c.tm.domain) (mkClosure c.env c.tm.body); in
      c.apply (if c.tm ? _plicity then v // { _plicity = c.tm._plicity; } else v);
    "sigma" = c:
      c.apply (vSigma c.tm.name (c.lazy c.tm.fst) (mkClosure c.env c.tm.snd));
    # `app` forces fn (need .tag for dispatch); arg is propagated as a
    # caller-env thunk into VLam closure / VDescViewFn / VNe spine.
    "app"   = c: c.evalThen (kApp1  c.env c.tm.arg) c.tm.fn;
    "fst"   = c: c.evalThen kFst c.tm.pair;
    "snd"   = c: c.evalThen kSnd c.tm.pair;

    "boot-sum-elim" = c: c.evalThen (kBootSumElim_Scrut c.env c.tm) c.tm.scrut;
    "boot-j"        = c: c.evalThen (kBootJ_Scrut       c.env c.tm) c.tm.eq;

    "pair"         = c: c.apply (vPair (c.lazy c.tm.fst) (c.lazy c.tm.snd));
    "boot-sum"     = c: c.apply (vBootSum (c.lazy c.tm.left) (c.lazy c.tm.right));
    "boot-inl"     = c: c.apply (vBootInl (c.lazy c.tm.left) (c.lazy c.tm.right) (c.lazy c.tm.term));
    "boot-inr"     = c: c.apply (vBootInr (c.lazy c.tm.left) (c.lazy c.tm.right) (c.lazy c.tm.term));
    "boot-eq"      = c: c.apply (vBootEq (c.lazy c.tm.type) (c.lazy c.tm.lhs) (c.lazy c.tm.rhs));
    "squash"       = c: c.apply (vSquash (c.lazy c.tm.A));
    "squash-intro" = c: c.apply (vSquashIntro (c.lazy c.tm.a));
    "level-suc"    = c: c.apply (vLevelSuc (c.lazy c.tm.pred));
    "level-max"    = c: c.apply (vLevelMax (c.lazy c.tm.lhs) (c.lazy c.tm.rhs));
    "mu"           = c: c.apply (vMu (c.lazy c.tm.I) (c.lazy c.tm.D) (c.lazy c.tm.i));

    "U" = c:
      if c.tm.level.tag == "level-zero" then c.apply vUZero
      else c.apply (vU (c.lazy c.tm.level));

    "desc" = c:
      let
        iLevV = if c.tm.iLev.tag == "level-zero" then vLevelZero else c.lazy c.tm.iLev;
        kV    = if c.tm.k.tag    == "level-zero" then vLevelZero else c.lazy c.tm.k;
      in c.apply (vDescAt kV iLevV (c.lazy c.tm.I));

    "lift" = c:
      let
        lV = if c.tm.l.tag == "level-zero" then vLevelZero else c.lazy c.tm.l;
        mV = if c.tm.m.tag == "level-zero" then vLevelZero else c.lazy c.tm.m;
      in c.evalThen (kLift_X lV mV (c.lazy c.tm.eq)) c.tm.A;

    "lift-intro" = c:
      let
        lV = if c.tm.l.tag == "level-zero" then vLevelZero else c.lazy c.tm.l;
        mV = if c.tm.m.tag == "level-zero" then vLevelZero else c.lazy c.tm.m;
      in c.evalThen (kLiftIntro_X lV mV (c.lazy c.tm.eq) (c.lazy c.tm.A)) c.tm.a;

    "opaque-lam" = c: c.apply (val.vOpaqueLam c.tm._fnBox (c.lazy c.tm.piTy));
    # `vStrEq` forces both operands to WHNF internally before reading their
    # tag/level, so passing lazy thunks here is safe (string operands are
    # atomic — forcing is O(1) in user-recursion depth).
    "str-eq" = c: c.apply (self.vStrEq (c.lazy c.tm.lhs) (c.lazy c.tm.rhs));

    "lift-elim" = c:
      let
        lV = if c.tm.l.tag == "level-zero" then vLevelZero else c.lazy c.tm.l;
        mV = if c.tm.m.tag == "level-zero" then vLevelZero else c.lazy c.tm.m;
      in c.evalThen (kLiftElim_X lV mV (c.lazy c.tm.eq) (c.lazy c.tm.A)) c.tm.x;

    "squash-elim" = c:
      c.evalThen (kSquashElim_X (c.lazy c.tm.A) (c.lazy c.tm.B) (c.lazy c.tm.f)) c.tm.x;

    "absurd" = c: c.evalThen (kAbsurd_Term (c.lazy c.tm.type)) c.tm.term;

    "interp-d" = c:
      let
        levelV = if c.tm.level.tag == "level-zero" then vLevelZero else c.lazy c.tm.level;
        IV = c.lazy c.tm.I;
        XV = c.lazy c.tm.X;
        iV = c.lazy c.tm.i;
      in c.evalThen (kInterpD levelV IV XV iV) c.tm.D;

    "all-d" = c:
      let
        LV = if c.tm.level.tag == "level-zero" then vLevelZero else c.lazy c.tm.level;
        KV = if c.tm.K.tag     == "level-zero" then vLevelZero else c.lazy c.tm.K;
        IV = c.lazy c.tm.I;
        XV = c.lazy c.tm.X;
        MV = c.lazy c.tm.M;
        iV = c.lazy c.tm.i;
        dV = c.lazy c.tm.d;
      in c.evalThen (kAllD LV IV KV XV MV iV dV) c.tm.D;

    "everywhere-d" = c:
      let
        LV = if c.tm.level.tag == "level-zero" then vLevelZero else c.lazy c.tm.level;
        KV = if c.tm.K.tag     == "level-zero" then vLevelZero else c.lazy c.tm.K;
        IV  = c.lazy c.tm.I;
        XV  = c.lazy c.tm.X;
        MV  = c.lazy c.tm.M;
        ihV = c.lazy c.tm.ih;
        iV  = c.lazy c.tm.i;
        dV  = c.lazy c.tm.d;
      in c.evalThen (kEverywhereD LV IV KV XV MV ihV iV dV) c.tm.D;

    "desc-ind" = c:
      let
        DV    = c.lazy c.tm.D;
        motV  = c.lazy c.tm.motive;
        stepV = c.lazy c.tm.step;
        iV    = c.lazy c.tm.i;
      in c.evalThen (kDescInd DV motV stepV iV) c.tm.scrut;

    "desc-desc-app" = c:
      let
        iLevV = if c.tm.iLev.tag == "level-zero" then vLevelZero else c.lazy c.tm.iLev;
        IV    = c.lazy c.tm.I;
        LV    = c.lazy c.tm.L;
      in c.apply (self.mkDescDescAppVF self.defaultFuel iLevV IV LV);

    "canon-app" = c:
      let
        paramVals = map c.lazy c.tm.params;
        bodyV     = c.lazy c.tm.body;
      in c.apply (self.mkCanonAppVF self.defaultFuel c.tm.id paramVals bodyV);

    "desc-con" = c: c.evalThen (kDescConPeel_Start c.env c.tm) c.tm.D;

    # Canonical flat-form chain. No peel — the Tm IS the canonical
    # form. Layers iterate via `map` (libnix-iterative); sub-Val
    # evals are lazy thunks (`c.lazy`), so the machine emits this
    # in a single apply step with O(1) frame depth.
    "desc-con-chain" = c:
      let
        tm       = c.tm;
        outerDV  = c.lazy tm.outerD;
        leftV    = c.lazy tm.payloadLeft;
        rightV   = c.lazy tm.payloadRight;
        baseDV   = c.lazy tm.base.D;
        baseIV   = if tm.base.i.tag == "tt" then vTt else c.lazy tm.base.i;
        baseDdV  = c.lazy tm.base.d;
        baseVal  = vDescCon baseDV baseIV baseDdV;
        layerVals = map (l: {
          i     = if l.i.tag == "tt" then vTt else c.lazy l.i;
          heads = map c.lazy l.heads;
          cert  = null;
        }) tm.layers;
        finalOuterI =
          if layerVals == [ ] then baseIV
          else (builtins.head layerVals).i;
      in c.apply (vDescConChain outerDV finalOuterI tm.payloadTag
        leftV rightV layerVals baseVal);
  };

  stepEval = state:
    let
      tm   = state.tm;
      env  = state.env;
      kont = state.kont;
      fuel = state.fuel;
      apply = mkApply kont fuel;
      evalThen = frame: nextTm: mkEval (push frame kont) fuel env nextTm;
      lazy = subTm: ev env subTm;
      ctx = { inherit tm env kont fuel apply evalThen lazy; };
    in evalDispatch.${tm.tag} ctx;

  applyDispatch = {
    # `KApp1` subsumes the former two-step `evalThen-fn → KApp2`. fn is
    # forced (needed for dispatch); arg stays as a caller-env Nix thunk and
    # is threaded into VLam closure env / VDescViewFn dispatch / VNe spine
    # without forcing — matches the value-level `vAppF` byte-for-byte.
    "KApp1" = c:
      let fn = c.v; in
      if fn.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else
        let argThunk = ev c.k.env c.k.argTm; in
        if fn.tag == "VDescViewFn" then applyDescViewFnArm c fn argThunk
        else if fn.tag == "VLam" then c.evalRest ([ argThunk ] ++ fn.closure.env) fn.closure.body
        else if fn.tag == "VNe"  then c.apply (vNe fn.level (fn.spine ++ [ (eApp argThunk) ]))
        else throw "tc: vApp on non-function (tag=${fn.tag})";

    "KApp_VV" = c:
      let fn = c.v; arg = c.k.arg; in
      if fn.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if fn.tag == "VDescViewFn" then applyDescViewFnArm c fn arg
      else if fn.tag == "VLam" then c.evalRest ([ arg ] ++ fn.closure.env) fn.closure.body
      else if fn.tag == "VNe"  then c.apply (vNe fn.level (fn.spine ++ [ (eApp arg) ]))
      else throw "tc: vApp on non-function (tag=${fn.tag})";

    "KFst" = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if c.v.tag == "VPair" then c.apply c.v.fst
      else if c.v.tag == "VNe" then c.apply (vNe c.v.level (c.v.spine ++ [ eFst ]))
      else throw "tc: vFst on non-pair (tag=${c.v.tag})";

    "KSnd" = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if c.v.tag == "VPair" then c.apply c.v.snd
      else if c.v.tag == "VNe" then c.apply (vNe c.v.level (c.v.spine ++ [ eSnd ]))
      else throw "tc: vSnd on non-pair (tag=${c.v.tag})";

    # Eliminator-scrutinee resumes: each forces the scrut for tag dispatch,
    # then on the stuck-VNe path threads the remaining sub-Tms into the
    # spine as Nix-lazy thunks (mirrors HEAD's `vBootSumElimF`/`vBootJ` on
    # `VNe`, which pass thunk args into `eBootSumElim`/`eBootJ` directly).
    "KBootSumElim_Scrut" = c:
      let tm = c.k.tm; env = c.k.env; in
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if c.v.tag == "VBootInl" then
        mkEval (push (kAppVV c.v.val) c.rest) c.fuel env tm.onLeft
      else if c.v.tag == "VBootInr" then
        mkEval (push (kAppVV c.v.val) c.rest) c.fuel env tm.onRight
      else if c.v.tag == "VNe" then
        c.apply (vNe c.v.level (c.v.spine ++ [
          (eBootSumElim
            (ev env tm.left)
            (ev env tm.right)
            (ev env tm.motive)
            (ev env tm.onLeft)
            (ev env tm.onRight))
        ]))
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${c.v.tag})";

    "KBootJ_Scrut" = c:
      let tm = c.k.tm; env = c.k.env; in
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if c.v.tag == "VBootRefl" then c.evalRest env tm.base
      else if c.v.tag == "VNe" then
        c.apply (vNe c.v.level (c.v.spine ++ [
          (eBootJ
            (ev env tm.type)
            (ev env tm.lhs)
            (ev env tm.motive)
            (ev env tm.base)
            (ev env tm.rhs))
        ]))
      else throw "tc: vBootJ on non-eq (tag=${c.v.tag})";

    "KLiftElim_X"   = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else c.apply (self.vLiftElimF c.k.lV c.k.mV c.k.eqV c.k.AV c.v);
    # `vLiftF` reads `A.tag` for the inner-Lift composition rule and
    # `vLiftIntroF` reads `a.tag`/`a.spine` for the η-collapse; the inspected
    # argument is driven to WHNF here (delivered as `c.v`) before the leaf,
    # per the public-leaf forcing rule.
    "KLift_X"       = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else c.apply (self.vLiftF c.k.lV c.k.mV c.k.eqV c.v);
    "KLiftIntro_X"  = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else c.apply (self.vLiftIntroF c.k.lV c.k.mV c.k.eqV c.k.AV c.v);
    "KSquashElim_X" = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else c.apply (self.vSquashElimF self.defaultFuel c.k.AV c.k.BV c.k.fV c.v);
    "KAbsurd_Term"  = c:
      if c.v.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else c.apply (self.vAbsurd c.k.tyV c.v);

    "KBootSumElim_ScrutV" = c:
      let k = c.k; scrut = c.v; in
      if scrut.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if scrut.tag == "VBootInl" then
        mkApply (push (kAppVV scrut.val) c.rest) c.fuel k.onLeft
      else if scrut.tag == "VBootInr" then
        mkApply (push (kAppVV scrut.val) c.rest) c.fuel k.onRight
      else if scrut.tag == "VNe" then
        c.apply (vNe scrut.level (scrut.spine ++ [
          (eBootSumElim k.left k.right k.motive k.onLeft k.onRight)
        ]))
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${scrut.tag})";

    "KInterpD" = c:
      let
        k = c.k;
        D = c.v;
        L = k.L; I = k.I; X = k.X; i = k.i;
      in
      if D.tag == "VNe" then
        c.apply (vNe D.level (D.spine ++ [ (eInterpD L I X i) ]))
      else
        mkApply
          (push kDescView
            (push (kResume_KInterpD_GotView L I X i) c.rest))
          c.fuel D;

    "KInterpD_PlusGotA" = c:
      let k = c.k; AInterp = c.v; in
      mkApply
        (push (kInterpD k.L k.I k.X k.i)
          (push (kInterpD_PlusCombine AInterp) c.rest))
        c.fuel k.B;

    "KInterpD_PlusCombine" = c:
      c.apply (vBootSum c.k.AInterp c.v);

    "KAllD" = c:
      let
        k = c.k;
        D = c.v;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i; d = k.d;
      in
      if D.tag == "VNe" then
        c.apply (vNe D.level (D.spine ++ [ (eAllD L I K X M i d) ]))
      else
        mkApply
          (push kDescView
            (push (kResume_KAllD_GotView L I K X M i d) c.rest))
          c.fuel D;

    "KAllD_ArgGotSubD" = c:
      let k = c.k; in
      mkApply (push (kAllD k.L k.I k.K k.X k.M k.i k.sndD) c.rest) c.fuel c.v;

    "KAllD_RecCombine" = c:
      let
        k = c.k;
        Mjfd = c.v;
        ihClosure = mkClosure [ k.L k.I k.K k.X k.M k.i k.sndD k.sub ]
          (term.mkAllD (term.mkVar 1) (term.mkVar 2) (term.mkVar 8)
            (term.mkVar 3) (term.mkVar 4) (term.mkVar 5)
            (term.mkVar 6) (term.mkVar 7));
      in c.apply (vSigma "_" Mjfd ihClosure);

    "KAllD_PlusStuck_GotAInterp" = c:
      let k = c.k; AInterp = c.v; in
      mkApply
        (push (kInterpD k.L k.I k.X k.i)
          (push (kAllD_PlusStuck_GotBInterp k.L k.I k.K k.X k.M k.i k.d k.viewA k.viewB AInterp) c.rest))
        c.fuel k.viewB;

    "KAllD_PlusStuck_GotBInterp" = c:
      let
        k = c.k;
        BInterp = c.v;
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
      in mkApply
           (push (kBootSumElim_ScrutV AInterp BInterp motive onLeftLam onRightLam) c.rest)
           c.fuel k.d;

    "KEverywhereD" = c:
      let
        k = c.k;
        D = c.v;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i; d = k.d;
      in
      if D.tag == "VNe" then
        c.apply (vNe D.level (D.spine ++ [ (eEverywhereD L I K X M ih i d) ]))
      else
        mkApply
          (push kDescView
            (push (kResume_KEverywhereD_GotView L I K X M ih i d) c.rest))
          c.fuel D;

    "KEverywhereD_ArgGotSubD" = c:
      let k = c.k; in
      mkApply (push (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i k.sndD) c.rest) c.fuel c.v;

    "KEverywhereD_RecGotIhHere" = c:
      let k = c.k; ihHere = c.v; in
      mkApply
        (push (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i k.sndD)
          (push (kEverywhereD_RecCombine ihHere) c.rest))
        c.fuel k.sub;

    "KEverywhereD_RecCombine" = c:
      c.apply (vPair c.k.ihHere c.v);

    "KEverywhereD_PiCombine" = c:
      c.apply (vPair c.k.piLam c.v);

    "KEverywhereD_PlusStuck_GotAInterp" = c:
      let k = c.k; AInterp = c.v; in
      mkApply
        (push (kInterpD k.L k.I k.X k.i)
          (push (kEverywhereD_PlusStuck_GotBInterp k.L k.I k.K k.X k.M k.ih k.i k.d k.viewA k.viewB AInterp) c.rest))
        c.fuel k.viewB;

    "KEverywhereD_PlusStuck_GotBInterp" = c:
      let
        k = c.k;
        BInterp = c.v;
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
      in mkApply
           (push (kBootSumElim_ScrutV AInterp BInterp motive onLeftLam onRightLam) c.rest)
           c.fuel k.d;

    "KDescInd" = c:
      let
        k = c.k;
        scrut = c.v;
        D = k.D; motive = k.motive; step = k.step; i = k.i;
        f = c.fuel;
      in
      if scrut.tag == "VLazyDescIndAccLayer" then forceLazyLayer c
      else if scrut.tag == "VNe" then
        c.apply (vNe scrut.level (scrut.spine ++ [ (eDescInd D motive step i) ]))
      else if scrut.tag == "VDescCon" then
        let
          I = if motive.tag != "VLam"
              then throw "tc: vDescInd on VDescCon requires VLam motive (got ${motive.tag})"
              else motive.domain;
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
          # Linear path: walk descCon chain via peel; same-D classifier mirrors desc.nix.
          dRef = D._descRef or null;
          linear = if dRef == null then null else dRef.linearChain or null;
          sameLinearDesc = desc:
            let other = desc._descRef or null; in
            dRef != null
            && linear != null
            && other != null
            && (other.kind or null) == (dRef.kind or null)
            && (other.name or null) == (dRef.name or null)
            && (other.arity or null) == (dRef.arity or null)
            && (other.indexed or null) == (dRef.indexed or null)
            && builtins.length (other.params or [ ]) == builtins.length (dRef.params or [ ])
            && (other.linearChain or null) == linear;
          payloadTag =
            if linear == null then null
            else if linear.side == "inl" then "VBootInl"
            else "VBootInr";
          nFields = if linear == null then 0 else linear.dataFieldCount;
          isRetLeaf = p:
            p.tag == "VBootRefl"
            || (p.tag == "VLiftIntro" && p.a.tag == "VBootRefl");
          collectPairs = inner:
            let
              collect = ii: p:
                if ii == nFields then
                  if p.tag != "VPair" then null
                  else if !(isRetLeaf p.snd) then null
                  else if p.fst.tag != "VDescCon" then null
                  else { tail = p.fst; }
                else if p.tag != "VPair" then null
                else collect (ii + 1) p.snd;
            in collect 0 inner;
          walkPayload = payload:
            if payload.tag == payloadTag
            then collectPairs payload.val
            else null;
          peel = node:
            if node.tag != "VDescCon" then null
            else if !(sameLinearDesc node.D) then null
            else
              let payload = walkPayload node.d; in
              if payload == null then null else payload.tail;
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = scrut; tail = peel scrut; }];
            operator = item:
              if item.tail == null then [ ]
              else [{ key = item.key + 1; val = item.tail; tail = peel item.tail; }];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in
        if certApplies then
          # vAppF (vAppF (vAppF step scrut.i) scrut.d) vTt
          mkApply
            (push (kAppVV scrut.i)
              (push (kAppVV scrut.d)
                (push (kAppVV vTt) c.rest)))
            c.fuel step
        # Chain-form: synthesize the per-layer chain directly from
        # `_layers`/`_base`; reuse the lazy-build kont below. Per-layer
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
            mkApply
              (push (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal chainBase.i chainBase.d)
                (push (kDescIndLayer_GotEvResult step chainBase.i chainBase.d) c.rest))
              c.fuel D
          else if nLay > f then throw "normalization budget exceeded"
          else
            mkApply
              (push (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal chainBase.i chainBase.d)
                (push (kDescIndLayer_GotEvResult step chainBase.i chainBase.d)
                  (push (kDescIndLinear_LazyBuild synthChainFn nLay step) c.rest)))
              c.fuel D
        else if linear != null && n >= 1 then
          if n > f then throw "normalization budget exceeded"
          else
            # baseResult via vDescIndFLayer(base.i, base.d); then build a
            # chain of `vLazyDescIndAccLayer` Vals bottom-up. The chain is
            # DATA (O(n) attrset allocations, zero body work). Forcing the
            # topmost layer fires the cascade through the driver's kont
            # stack via `forceLazyLayer`, not through libnix recursion.
            mkApply
              (push (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal base.i base.d)
                (push (kDescIndLayer_GotEvResult step base.i base.d)
                  (push (kDescIndLinear_LazyBuild (idx: builtins.elemAt chain idx) n step) c.rest)))
              c.fuel D
        else
          # Fallback: vDescIndFLayer(D, motive, step, ihVal, muFam, I, i, scrut.d).
          mkApply
            (push (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal i scrut.d)
              (push (kDescIndLayer_GotEvResult step i scrut.d) c.rest))
            c.fuel D
      else throw "tc: vDescInd on non-mu (tag=${scrut.tag})";

    "KDescIndLayer_GotEvResult" = c:
      # vAppF (vAppF (vAppF step i) d) evResult — fires layer.i first.
      let k = c.k; evResult = c.v; in
      mkApply
        (push (kAppVV k.i)
          (push (kAppVV k.d)
            (push (kAppVV evResult) c.rest)))
        c.fuel k.step;

    "KDescIndLinear_LazyBuild" = c:
      # `c.v` is `baseResult` — the deepest layer's already-forced accumulator,
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
        k = c.k;
        baseResult = c.v;
        buildFrom = idx:
          if idx == k.n then baseResult
          else
            let layer = (k.chainFn idx).val; in
            vLazyDescIndAccLayer k.step layer.i layer.d (buildFrom (idx + 1));
      in
      c.apply (buildFrom 0);

    # dVal arrives via tm.D through the machine. classify/chain/peel
    # are pure Tm/Val walks. sameD's conv fallback and LayerI's
    # wrapPayload evalTm are sub-driver re-entries.
    "KDescConPeel_Start" = c:
      mkApply
        (push kDescView
          (push (kResume_KDescConPeel_GotView { env = c.k.env; tm = c.k.tm; }) c.rest))
        c.fuel c.v;

    "KResume_KDescConPeel_GotView" = c:
      let
        env  = c.k.state.env;
        tm   = c.k.state.tm;
        dVal = c.v.D;
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
          let view = c.v.view; in
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
        depth = builtins.length env;
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
        state = {
          inherit env tm chain n base topPeel withCert dVal chainForm payloadInfo nFields;
        };
      in
        if n > f then throw "normalization budget exceeded"
        else if base.i.tag == "tt"
        then mkEval (push (kDescConPeel_BaseD state vTt) c.rest) c.fuel env base.d
        else mkEval (push (kDescConPeel_BaseI state) c.rest) c.fuel env base.i;

    "KDescConPeel_BaseI" = c:
      let s = c.k.state; in
      mkEval (push (kDescConPeel_BaseD s c.v) c.rest) c.fuel s.env s.base.d;

    "KDescConPeel_BaseD" = c:
      let
        s = c.k.state;
        baseVal = s.withCert s.base c.k.baseI c.v;
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
            c.apply (vDescConChain s.dVal finalOuterI
              s.payloadInfo.tag s.payloadInfo.left s.payloadInfo.right
              allLayers finalBase)
        # When `classify != null` (peel can walk) but `chainForm` is false
        # (`plusSides == null` — Desc has no sum-shaped descView even though
        # cert/ref says linearChain), `n` cannot exceed 0 in practice. The
        # full suite empirically confirms this invariant; the assert documents
        # it and traps any future regression.
        else if s.n == 0 then c.apply baseVal
        else throw "tc: KDescConPeel_BaseD non-chainForm n>=1 path reached (n=${toString s.n})";

    # Resume handlers: rebuild the original frame with the previously-forced
    # sub-Val substituted in, then deliver the captured originally-consumed
    # val. The handler above re-fires with the field now non-VThunkTm.
    "KResume_KAllD_d" = c:
      let k = c.k; forcedD = c.v; in
      mkApply (push (kAllD k.L k.I k.K k.X k.M k.i forcedD) c.rest) c.fuel k.D;

    "KResume_KEverywhereD_d" = c:
      let k = c.k; forcedD = c.v; in
      mkApply (push (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i forcedD) c.rest)
              c.fuel k.D;

    "KResume_KDescInd_motive" = c:
      let k = c.k; forcedMotive = c.v; in
      mkApply (push (kDescInd k.D forcedMotive k.step k.i) c.rest) c.fuel k.scrut;

    # Continuation of `KAllD` / `KEverywhereD` view.idx == 4 after the
    # `kSumPayloadView` dispatcher has run on a (pre-forced) `d`.
    # `c.v` is the VRawSV wrapper; `k.d` is the forced sum value used
    # for the VNe fallback spine and the throw-tag diagnostic.
    "KResume_KAllD_view4_GotSV" = c:
      let k = c.k; sv = c.v.sv; in
      if sv != null then
        if sv.side == "inl"
        then mkApply (push (kAllD k.L k.I k.K k.X k.M k.i sv.value) c.rest) c.fuel k.viewA
        else mkApply (push (kAllD k.L k.I k.K k.X k.M k.i sv.value) c.rest) c.fuel k.viewB
      else if k.d.tag == "VNe" then
        mkApply
          (push (kInterpD k.L k.I k.X k.i)
            (push (kAllD_PlusStuck_GotAInterp k.L k.I k.K k.X k.M k.i k.d k.viewA k.viewB)
              c.rest))
          c.fuel k.viewA
      else throw "tc: vAllD on plus with non-sum d (tag=${k.d.tag})";

    "KResume_KEverywhereD_view4_GotSV" = c:
      let k = c.k; sv = c.v.sv; in
      if sv != null then
        if sv.side == "inl"
        then mkApply (push (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i sv.value) c.rest) c.fuel k.viewA
        else mkApply (push (kEverywhereD k.L k.I k.K k.X k.M k.ih k.i sv.value) c.rest) c.fuel k.viewB
      else if k.d.tag == "VNe" then
        mkApply
          (push (kInterpD k.L k.I k.X k.i)
            (push (kEverywhereD_PlusStuck_GotAInterp k.L k.I k.K k.X k.M k.ih k.i k.d k.viewA k.viewB)
              c.rest))
          c.fuel k.viewA
      else throw "tc: vEverywhereD on plus with non-sum d (tag=${k.d.tag})";

    # Continuation of `KInterpD` after `kDescView` has run on the original
    # descriptor. `c.v` is the VRawView wrapper carrying `view` and the
    # (forced) `D` used in the throw diagnostic.
    "KResume_KInterpD_GotView" = c:
      let
        k = c.k;
        view = c.v.view; D = c.v.D;
        L = k.L; I = k.I; X = k.X; i = k.i;
      in
      if view == null then throw "tc: vInterpD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        let
          iLev = view.iLev or vLevelZero;
          retLevel = self.levelMaxOpt L iLev;
        in c.apply (self.vLiftF iLev retLevel vBootRefl (vBootEq I view.j i))
      else if view.idx == 1 then
        let
          ihClosure = mkClosure [ view.tFn L I X i ]
            (term.mkInterpD (term.mkVar 2) (term.mkVar 3)
              (term.mkApp (term.mkVar 1) (term.mkVar 0))
              (term.mkVar 4)
              (term.mkVar 5));
        in c.apply (vSigma "s" view.sTy ihClosure)
      else if view.idx == 2 then
        mkApply
          (push (kAppVV view.j)
            (push (kResume_KInterpD_view2_GotXj L I X i view.sub) c.rest))
          c.fuel X
      else if view.idx == 3 then
        let
          piTy = vPi "s" view.sTy (mkClosure [ X view.fn ]
            (term.mkApp (term.mkVar 1)
              (term.mkApp (term.mkVar 2) (term.mkVar 0))));
          ihClosure = mkClosure [ L I X i view.sub ]
            (term.mkInterpD (term.mkVar 1) (term.mkVar 2) (term.mkVar 5)
              (term.mkVar 3)
              (term.mkVar 4));
        in c.apply (vSigma "_" piTy ihClosure)
      else
        mkApply
          (push (kInterpD L I X i)
            (push (kInterpD_PlusGotA L I X i view.B) c.rest))
          c.fuel view.A;

    "KResume_KInterpD_view2_GotXj" = c:
      let
        k = c.k;
        Xj = c.v;
        ihClosure = mkClosure [ k.L k.I k.X k.i k.sub ]
          (term.mkInterpD (term.mkVar 1) (term.mkVar 2) (term.mkVar 5)
            (term.mkVar 3)
            (term.mkVar 4));
      in c.apply (vSigma "_" Xj ihClosure);

    "KResume_KAllD_GotView" = c:
      let
        k = c.k;
        view = c.v.view; D = c.v.D;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i; d = k.d;
      in
      if view == null then throw "tc: vAllD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        c.apply (self.vLiftF vLevelZero K vBootRefl vUnit)
      else if view.idx == 1 || view.idx == 2 || view.idx == 3 then
        mkApply
          (push kFst
            (push (kResume_KAllD_GotFstD L I K X M i d view) c.rest))
          c.fuel d
      else
        if (d.tag or "") == "VThunkTm" then
          mkApply (push (kResume_KAllD_d L I K X M i D) c.rest) c.fuel d
        else
          mkApply
            (push kSumPayloadView
              (push (kResume_KAllD_view4_GotSV L I K X M i view.A view.B d) c.rest))
            c.fuel d;

    "KResume_KAllD_GotFstD" = c:
      let k = c.k; fstD = c.v; in
      mkApply
        (push kSnd
          (push (kResume_KAllD_GotSndD k.L k.I k.K k.X k.M k.i fstD k.view) c.rest))
        c.fuel k.d;

    "KResume_KAllD_GotSndD" = c:
      let
        k = c.k;
        sndD = c.v;
        fstD = k.fstD; view = k.view;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; i = k.i;
      in
      if view.idx == 1 then
        mkApply
          (push (kAppVV fstD)
            (push (kAllD_ArgGotSubD L I K X M i sndD) c.rest))
          c.fuel view.tFn
      else if view.idx == 2 then
        mkApply
          (push (kAppVV view.j)
            (push (kAppVV fstD)
              (push (kAllD_RecCombine sndD view.sub L I K X M i) c.rest)))
          c.fuel M
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
        in c.apply (vSigma "_" piTy ihClosure);

    "KResume_KEverywhereD_GotView" = c:
      let
        k = c.k;
        view = c.v.view; D = c.v.D;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i; d = k.d;
      in
      if view == null then throw "tc: vEverywhereD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        c.apply (self.vLiftIntroF vLevelZero K vBootRefl vUnit vTt)
      else if view.idx == 1 || view.idx == 2 || view.idx == 3 then
        mkApply
          (push kFst
            (push (kResume_KEverywhereD_GotFstD L I K X M ih i d view) c.rest))
          c.fuel d
      else
        if (d.tag or "") == "VThunkTm" then
          mkApply (push (kResume_KEverywhereD_d L I K X M ih i D) c.rest) c.fuel d
        else
          mkApply
            (push kSumPayloadView
              (push (kResume_KEverywhereD_view4_GotSV L I K X M ih i view.A view.B d) c.rest))
            c.fuel d;

    "KResume_KEverywhereD_GotFstD" = c:
      let k = c.k; fstD = c.v; in
      mkApply
        (push kSnd
          (push (kResume_KEverywhereD_GotSndD k.L k.I k.K k.X k.M k.ih k.i fstD k.view) c.rest))
        c.fuel k.d;

    "KResume_KEverywhereD_GotSndD" = c:
      let
        k = c.k;
        sndD = c.v;
        fstD = k.fstD; view = k.view;
        L = k.L; I = k.I; K = k.K; X = k.X; M = k.M; ih = k.ih; i = k.i;
      in
      if view.idx == 1 then
        mkApply
          (push (kAppVV fstD)
            (push (kEverywhereD_ArgGotSubD L I K X M ih i sndD) c.rest))
          c.fuel view.tFn
      else if view.idx == 2 then
        # `ih._ihShortcut` + canonical fstD bypass the
        # `vAppF ∘ vAppF ∘ evalF` roundtrip via the reduction core's frame
        # encoding (kEverywhereD → kDescIndLayer_GotEvResult → recombine).
        if ih ? _ihShortcut && fstD.tag == "VDescCon"
        then
          let s = ih._ihShortcut; in
          mkApply
            (push (kEverywhereD vLevelZero s.I vLevelZero s.muFam s.motive ih view.j fstD.d)
              (push (kDescIndLayer_GotEvResult s.step view.j fstD.d)
                (push (kEverywhereD_RecGotIhHere L I K X M ih i sndD view.sub) c.rest)))
            c.fuel s.D
        else
          mkApply
            (push (kAppVV view.j)
              (push (kAppVV fstD)
                (push (kEverywhereD_RecGotIhHere L I K X M ih i sndD view.sub) c.rest)))
            c.fuel ih
      else
        let
          piLam = vLam "s" view.sTy (mkClosure [ ih view.fn fstD ]
            (term.mkApp
              (term.mkApp (term.mkVar 1)
                (term.mkApp (term.mkVar 2) (term.mkVar 0)))
              (term.mkApp (term.mkVar 3) (term.mkVar 0))));
        in mkApply
             (push (kEverywhereD L I K X M ih i sndD)
               (push (kEverywhereD_PiCombine piLam) c.rest))
             c.fuel view.sub;

    # Quote-side resume. mkQEvalStep pushes `kqResumeQuote d` and switches
    # to Eval when it meets a VThunkTm; once Eval reaches Apply with a forced
    # val, this handler restores Q-Eval at binder depth `d` so the original
    # quote kont resumes.
    "KQResumeQuote" = c:
      { mode = "Q-Eval"; v = c.v; d = c.k.d; fuel = c.fuel; kont = c.rest; };

    # Helper dispatchers — step-by-step replications of `desc.nix`'s
    # `descViewF` and `sumPayloadValView` bodies via machine frames. Every
    # sub-Val tag read happens on a forced Val (stepApply's top-level peek
    # force-routes any VThunkTm c.v through Eval before the dispatcher body
    # runs). Every `vLiftElimF` call goes through a `kLiftElim_X` push per
    # the public-leaf forcing rule. The helpers in `desc.nix` stay for
    # external callers but are no longer reachable from a handler.
    #
    # VRaw* sentinels (VRawView / VRawSV / VRawDecode / VRawPeel) never
    # reach the tag-dispatch fallthrough because they appear only between
    # consecutive paired frames structurally placed by the call-site push.
    "KDescView" = c:
      let D = c.v; in
      let
        isDViewTag = D.tag == "DViewRet" || D.tag == "DViewArg"
                  || D.tag == "DViewRec" || D.tag == "DViewPi"
                  || D.tag == "DViewPlus";
      in
      if isDViewTag then
        mkApply c.rest c.fuel { tag = "VRawView"; view = D; inherit D; }
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
            view = self.descDescCanonicalViewF (c.fuel - 1) iLev_arg I_arg L_arg;
          in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; inherit D; }
        else mkApply c.rest c.fuel { tag = "VRawView"; view = null; inherit D; }
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
        mkApply
          (push (kDecodeWalk 0)
            (push (kResume_KDescView_GotDecode meta) c.rest))
          c.fuel D.d
      else
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; inherit D; };

    "KDecodeWalk" = c:
      let node = c.v; depth = c.k.depth; in
      if depth >= 4 then
        mkApply c.rest c.fuel { tag = "VRawDecode"; idx = 4; payload = node; }
      else if node.tag == "VBootInl" then
        mkApply c.rest c.fuel { tag = "VRawDecode"; idx = depth; payload = node.val; }
      else if node.tag == "VBootInr" then
        mkApply (push (kDecodeWalk (depth + 1)) c.rest) c.fuel node.val
      else
        mkApply c.rest c.fuel { tag = "VRawDecode"; idx = null; payload = null; };

    "KResume_KDescView_GotDecode" = c:
      let info = c.v; meta = c.k.meta; in
      if info.idx == null then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        let
          gotPayloadFrame =
            if      info.idx == 0 then kResume_KDescView_Idx0_GotPayload meta
            else if info.idx == 1 then kResume_KDescView_Idx1_GotPayload meta
            else if info.idx == 2 then kResume_KDescView_Idx2_GotPayload meta
            else if info.idx == 3 then kResume_KDescView_Idx3_GotPayload meta
            else                       kResume_KDescView_Idx4_GotPayload meta;
        in mkApply (push gotPayloadFrame c.rest) c.fuel info.payload;

    # Idx 0: payload → (optional vLiftElim) → j → view.

    "KResume_KDescView_Idx0_GotPayload" = c:
      let payload = c.v; meta = c.k.meta; in
      if payload.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        let chainToJ = push (kResume_KDescView_Idx0_GotJ meta) c.rest;
            chainBefore =
              if meta.hasDescDescRef
              then push (kLiftElim_X meta.iLev_val meta.dDescL_val vBootRefl meta.I_val) chainToJ
              else chainToJ;
        in mkApply chainBefore c.fuel payload.fst;

    "KResume_KDescView_Idx0_GotJ" = c:
      let j = c.v; meta = c.k.meta; in
      let view = {
            idx = 0;
            inherit j;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
          };
      in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; D = meta.D; };

    # Idx 1: payload → payload.snd → sMeta (vLiftElim) → view.

    "KResume_KDescView_Idx1_GotPayload" = c:
      let payload = c.v; meta = c.k.meta; in
      if payload.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        mkApply
          (push (kResume_KDescView_Idx1_GotSnd meta payload) c.rest)
          c.fuel payload.snd;

    "KResume_KDescView_Idx1_GotSnd" = c:
      let payloadSnd = c.v; payload = c.k.payload; meta = c.k.meta; in
      if payloadSnd.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        let tPayload = payloadSnd.fst;
            chainToSMeta = push (kResume_KDescView_Idx1_GotSMeta meta tPayload) c.rest;
            chainBefore =
              if meta.hasDescDescRef
              then push (kLiftElim_X (vLevelSuc meta.k_val) meta.dDescL_val vBootRefl (vU meta.k_val)) chainToSMeta
              else chainToSMeta;
        in mkApply chainBefore c.fuel payload.fst;

    "KResume_KDescView_Idx1_GotSMeta" = c:
      let sMeta = c.v; tPayload = c.k.tPayload; meta = c.k.meta; in
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
      in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; D = meta.D; };

    # Idx 2: payload → payload.snd → (optional vLiftElim) → j → view.

    "KResume_KDescView_Idx2_GotPayload" = c:
      let payload = c.v; meta = c.k.meta; in
      if payload.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        mkApply
          (push (kResume_KDescView_Idx2_GotSnd meta payload) c.rest)
          c.fuel payload.snd;

    "KResume_KDescView_Idx2_GotSnd" = c:
      let payloadSnd = c.v; payload = c.k.payload; meta = c.k.meta; in
      if payloadSnd.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        let sub = payloadSnd.fst;
            chainToJ = push (kResume_KDescView_Idx2_GotJ meta sub) c.rest;
            chainBefore =
              if meta.hasDescDescRef
              then push (kLiftElim_X meta.iLev_val meta.dDescL_val vBootRefl meta.I_val) chainToJ
              else chainToJ;
        in mkApply chainBefore c.fuel payload.fst;

    "KResume_KDescView_Idx2_GotJ" = c:
      let j = c.v; sub = c.k.sub; meta = c.k.meta; in
      let view = {
            idx = 2;
            inherit j sub;
            iLev = meta.iLev_val;
            I = meta.I_val;
            k = meta.k_val;
            label = meta.label_val;
            conLabel = meta.conLabel_val;
          };
      in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; D = meta.D; };

    # Idx 3: payload → payload.snd → payload.snd.snd → sMeta (vLiftElim)
    #     → fn (vLiftElim) → view.

    "KResume_KDescView_Idx3_GotPayload" = c:
      let payload = c.v; meta = c.k.meta; in
      if payload.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        mkApply
          (push (kResume_KDescView_Idx3_GotSnd meta payload) c.rest)
          c.fuel payload.snd;

    "KResume_KDescView_Idx3_GotSnd" = c:
      let payloadSnd = c.v; payload = c.k.payload; meta = c.k.meta; in
      if payloadSnd.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        mkApply
          (push (kResume_KDescView_Idx3_GotSndSnd meta payload payloadSnd) c.rest)
          c.fuel payloadSnd.snd;

    "KResume_KDescView_Idx3_GotSndSnd" = c:
      let payloadSndSnd = c.v;
          payload = c.k.payload; psnd = c.k.psnd; meta = c.k.meta;
      in
      if payloadSndSnd.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        let sub = payloadSndSnd.fst;
            psndFst = psnd.fst;
            chainToSMeta = push (kResume_KDescView_Idx3_GotSMeta meta psndFst sub) c.rest;
            chainBefore =
              if meta.hasDescDescRef
              then push (kLiftElim_X (vLevelSuc meta.k_val) meta.dDescL_val vBootRefl (vU meta.k_val)) chainToSMeta
              else chainToSMeta;
        in mkApply chainBefore c.fuel payload.fst;

    "KResume_KDescView_Idx3_GotSMeta" = c:
      let sMeta = c.v; psndFst = c.k.psndFst; sub = c.k.sub; meta = c.k.meta; in
      let fTy = vPi "_" sMeta (mkClosure [ meta.I_val ] (term.mkVar 1));
          chainToFn = push (kResume_KDescView_Idx3_GotFn meta sMeta sub) c.rest;
          chainBefore =
            if meta.hasDescDescRef
            then push (kLiftElim_X (self.levelMaxOpt meta.k_val meta.iLev_val) meta.dDescL_val vBootRefl fTy) chainToFn
            else chainToFn;
      in mkApply chainBefore c.fuel psndFst;

    "KResume_KDescView_Idx3_GotFn" = c:
      let fn = c.v; sMeta = c.k.sMeta; sub = c.k.sub; meta = c.k.meta; in
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
      in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; D = meta.D; };

    # Idx 4: payload → payload.snd → view.

    "KResume_KDescView_Idx4_GotPayload" = c:
      let payload = c.v; meta = c.k.meta; in
      if payload.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
      else
        mkApply
          (push (kResume_KDescView_Idx4_GotSnd meta payload) c.rest)
          c.fuel payload.snd;

    "KResume_KDescView_Idx4_GotSnd" = c:
      let payloadSnd = c.v; payload = c.k.payload; meta = c.k.meta; in
      if payloadSnd.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawView"; view = null; D = meta.D; }
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
        in mkApply c.rest c.fuel { tag = "VRawView"; inherit view; D = meta.D; };

    # Step-by-step replication of `sumPayloadValView`.

    "KSumPayloadView" = c:
      let d = c.v; in
      if d.tag == "VBootInl" then
        let sv = {
              side = "inl";
              value = d.val;
              rebuild = payload: vBootInl d.left d.right payload;
            };
        in mkApply c.rest c.fuel { tag = "VRawSV"; inherit sv; }
      else if d.tag == "VBootInr" then
        let sv = {
              side = "inr";
              value = d.val;
              rebuild = payload: vBootInr d.left d.right payload;
            };
        in mkApply c.rest c.fuel { tag = "VRawSV"; inherit sv; }
      else if d.tag == "VDescCon" then
        mkApply (push (kResume_KSumPayloadView_GotDDesc d) c.rest) c.fuel d.D
      else
        mkApply c.rest c.fuel { tag = "VRawSV"; sv = null; };

    "KResume_KSumPayloadView_GotDDesc" = c:
      let dD = c.v; d = c.k.d; in
      if !(dD ? _descRef) then
        mkApply c.rest c.fuel { tag = "VRawSV"; sv = null; }
      else if !(self.isSumDescRef dD._descRef) then
        mkApply c.rest c.fuel { tag = "VRawSV"; sv = null; }
      else
        mkApply (push (kResume_KSumPayloadView_GotDD d) c.rest) c.fuel d.d;

    "KResume_KSumPayloadView_GotDD" = c:
      let dDInner = c.v; d = c.k.d; in
      if dDInner.tag != "VBootInl" && dDInner.tag != "VBootInr" then
        mkApply c.rest c.fuel { tag = "VRawSV"; sv = null; }
      else
        mkApply
          (push (kResume_KSumPayloadView_GotDDVal d dDInner) c.rest)
          c.fuel dDInner.val;

    "KResume_KSumPayloadView_GotDDVal" = c:
      let dDValForced = c.v; d = c.k.d; dD = c.k.dD; in
      if dDValForced.tag != "VPair" then
        mkApply c.rest c.fuel { tag = "VRawSV"; sv = null; }
      else
        let pair = dDValForced; pairSnd = pair.snd; in
        mkApply
          (push (kPeelLiftIntroVal (payload: payload))
            (push (kResume_KSumPayloadView_GotField d dD pairSnd) c.rest))
          c.fuel pair.fst;

    "KResume_KSumPayloadView_GotField" = c:
      let field = c.v; d = c.k.d; dD = c.k.dD; pairSnd = c.k.pairSnd; in
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
      in mkApply c.rest c.fuel { tag = "VRawSV"; inherit sv; };

    # Iterative walker over VLiftIntro layers, accumulating the rebuild fn
    # into the frame. Non-VLiftIntro `c.v` terminates with a VRawPeel
    # carrying `{ value, rebuild }`.
    "KPeelLiftIntroVal" = c:
      let v = c.v; rb = c.k.rebuildAcc; in
      if v.tag == "VLiftIntro" then
        let newRb = payload: rb (vLiftIntro v.l v.m v.eq v.A payload);
        in mkApply (push (kPeelLiftIntroVal newRb) c.rest) c.fuel v.a
      else
        mkApply c.rest c.fuel { tag = "VRawPeel"; value = v; rebuild = rb; };
  };

  stepApply = state:
    if state.kont == null then mkDone state.fuel state.val
    else if (state.val.tag or "") == "VThunkTm" then
      # Force a deferred Tm before letting the active frame consume it. The
      # current kont is preserved; the frame fires once Eval produces a forced
      # Val. Keeps the cascade inside the driver — no fresh runMachineF entry.
      mkEval state.kont state.fuel state.val.env state.val.tm
    else
      let
        k = state.kont.head; rest = state.kont.tail;
        v = state.val; fuel = state.fuel;
        apply = mkApply rest fuel;
        evalRest = mkEval rest fuel;
        ctx = { inherit k rest v fuel apply evalRest; };
      in applyDispatch.${k.tag} ctx;

  # Sentinel for the eval-only entry: any flow that lands a Q-Apply frame
  # with `qApplyDispatch.${tag}` invoking `fallback` is a routing bug — the
  # eval driver should never reach a Q-fallback path.
  evalDefaultFallback = _d: v:
    throw "tc.eval: Q-fallback reached from eval-only path (val.tag=${v.tag or "?"})";

  # Unified step dispatch shared between the eval driver and the quote driver.
  # Modes: Eval/Apply use the eval-side dispatchers; Q-Eval delegates to a
  # `mkQEvalStep`-built closure; Q-Apply hands the state to `qApplyDispatch`
  # or completes via `mkQDone` when the kont is empty. The `fallback`
  # parameter is the quote-side leaf fallback consumed by Q-Eval.
  mkStep = fallback:
    let qEvalStep = mkQEvalStep fallback; in
    state:
           if state.mode == "Eval"    then stepEval  state
      else if state.mode == "Apply"   then stepApply state
      else if state.mode == "Q-Eval"  then qEvalStep state
      else if state.mode == "Q-Apply" then
        if state.kont == null
        then mkQDone state.fuel state.tm
        else qApplyDispatch.${state.kont.head.tag} state
      else state;

  step = mkStep evalDefaultFallback;

  # Trace-eliding driver: a chunked `foldl'` threads only the current state,
  # so intermediate states GC immediately (the driver retains no trace).
  # `driverChunkSize` is the SEED chunk length — small enough that shallow
  # eliminator calls (`ev`'s tier-3, typically <10 steps) waste only a handful
  # of post-Done iterations per `foldl'` pass. The driver's outer iteration
  # doubles the chunk length each level (see `driver`), so its libnix-stack
  # depth is log2(totalSteps / driverChunkSize) — bounded by ~19 at the fuel
  # ceiling, i.e. O(1) regardless of user-level recursion depth N.
  driverChunkSize = 32;
  driverChunkList = builtins.genList (n: n) driverChunkSize;

  # When the driver reaches `Done` with a `VLazyDescIndAccLayer` Val, transform
  # to `Apply` with the three force-frames pushed — the cascade resolves in
  # the same driver loop (the kont stack absorbs the depth; libnix sees one
  # frame). Similarly, a `VThunkTm` at Done transitions to Eval to force the
  # deferred Tm. `Q-Done` is terminal: the quote driver consumes `state.tm`.
  # The invariant `runMachineAtF returns only forced Vals` is enforced here.
  mkStepIf = fallback:
    let unifiedStep = mkStep fallback; in
    state: _i:
      if state.mode == "Done" then
        if (state.val.tag or "") == "VLazyDescIndAccLayer" then
          let fn = state.val; in
          {
            mode = "Apply"; val = fn.step; fuel = state.fuel;
            kont = push (kAppVV fn.i)
              (push (kAppVV fn.d)
                (push (kAppVV (vPair fn.prevAcc vTt)) null));
          }
        else if (state.val.tag or "") == "VThunkTm" then
          { mode = "Eval"; env = state.val.env; tm = state.val.tm;
            fuel = state.fuel; kont = null; }
        else state
      else if state.mode == "Q-Done" then state
      else if state.fuel <= 0 then state // { mode = "__exhausted__"; }
      else unifiedStep state;

  stepIf = mkStepIf evalDefaultFallback;

  driver = initState:
    let
      # The outer iteration is iterative-in-libnix via chunk-length doubling:
      # each level runs an iterative `foldl'` chunk of length |chunkList|, then
      # doubles the chunk for the next level. Recursion depth is therefore
      # log2(totalSteps / driverChunkSize) — ~19 at the fuel ceiling — so the
      # libnix C++ stack stays O(1) in the user-level recursion depth N. A
      # fixed-size recursive loop would accrue totalSteps/driverChunkSize frames
      # (Nix has no TCO) and overflow the 8 MiB stack near N=500. The chunk list
      # carries only iteration counters (`stepIf` ignores them), so doubling by
      # `++` is sound; threading a single state keeps peak heap independent of
      # step count.
      loop = chunkList: state:
        let after = builtins.foldl' stepIf state chunkList; in
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
        else loop (chunkList ++ chunkList) after;
    in loop driverChunkList initState;

  runMachineF = fuel: env: tm:
    driver { mode = "Eval"; inherit env tm fuel; kont = null; };

  # Apply-mode entry: resume the machine with `val` ready to be consumed by
  # `kont`'s top frame. Used by `desc.nix`'s helper wrappers, which preload
  # an entry frame and deliver the description as the seed Val.
  runMachineAtF = fuel: kont: val:
    driver { mode = "Apply"; inherit val kont fuel; };

  runDescIndAtF = fuel: D: motive: step: i: scrut:
    runMachineAtF fuel (push (kDescInd D motive step i) null) scrut;

  runDescIndLayerAtF = fuel: D: motive: step: ihVal: muFam: I: i: d:
    runMachineAtF fuel
      (push (kEverywhereD vLevelZero I vLevelZero muFam motive ihVal i d)
        (push (kDescIndLayer_GotEvResult step i d) null))
      D;

  runInterpDAtF = fuel: L: I: X: i: D:
    runMachineAtF fuel (push (kInterpD L I X i) null) D;

  runAllDAtF = fuel: L: I: K: X: M: i: d: D:
    runMachineAtF fuel (push (kAllD L I K X M i d) null) D;

  runEverywhereDAtF = fuel: L: I: K: X: M: ih: i: d: D:
    runMachineAtF fuel (push (kEverywhereD L I K X M ih i d) null) D;

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

  kqApp = pending: mkTm: acc:
    { tag = "KQ_App"; inherit pending mkTm acc; };
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
  # `kqApp` quotes the 6 fixed sub-Vals (outerD + payload left/right
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

  mkQApply = kont: fuel: d: tm:
    { mode = "Q-Apply"; inherit kont fuel d tm; };
  mkQEval  = kont: fuel: d: v:
    { mode = "Q-Eval";  inherit kont fuel d v; };
  mkQDone  = fuel: tm:
    { mode = "Q-Done"; inherit fuel tm; };

  qApplyDispatch = {
    "KQ_App" = state:
      let
        k    = state.kont.head;
        rest = state.kont.tail;
        acc' = k.acc ++ [ state.tm ];
      in
      if k.pending == [ ]
      then mkQApply rest state.fuel state.d (k.mkTm acc')
      else
        let next = builtins.head k.pending; in
        mkQEval
          (push (kqApp (builtins.tail k.pending) k.mkTm acc') rest)
          state.fuel next.d next.v;

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
          env  = [ (freshVar k.outerD) ] ++ k.closure.env;
          tm   = k.closure.body;
          fuel = state.fuel - 1;
          kont = push (kqResumeQuote (k.outerD + 1))
            (push (kqBinderDone k.name domTm k.ctor k.outerD) rest); };

    "KQ_Binder_Done" = state:
      let
        k = state.kont.head; rest = state.kont.tail;
        bodyTm = state.tm;
        tm =
               if k.ctor == "pi"    then term.mkPi    k.name k.domTm bodyTm
          else if k.ctor == "lam"   then term.mkLam   k.name k.domTm bodyTm
          else if k.ctor == "sigma" then term.mkSigma k.name k.domTm bodyTm
          else throw "qmachine: bad binder ctor: ${k.ctor}";
      in mkQApply rest state.fuel k.outerD tm;

    "KQ_Spine_Step" = state:
      let
        k = state.kont.head; rest = state.kont.tail;
        headTm = state.tm;
        n = builtins.length k.spine;
      in
      if k.idx == n
      then mkQApply rest state.fuel state.d headTm
      else
        let
          e = builtins.elemAt k.spine k.idx;
          spec = quoteElimSpec state.d headTm e;
          restAfter = push (kqSpineStep k.spine (k.idx + 1)) rest;
        in
          if spec.pending == [ ]
          then mkQApply restAfter state.fuel state.d (spec.mkTm [ ])
          else
            let first = builtins.head spec.pending; in
            mkQEval
              (push (kqApp (builtins.tail spec.pending) spec.mkTm [ ]) restAfter)
              state.fuel first.d first.v;

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
      in mkQApply rest state.fuel k.d chainTm;
  };

  mkQEvalStep = fallback: state:
    let v = state.v; t = v.tag; kont = state.kont; fuel = state.fuel; d = state.d; in

    # Force a deferred Tm before quoting via a mode switch through the shared
    # driver. `kqResumeQuote d` rides on top of the Q kont; once Eval reaches
    # Apply with a forced val, the resume handler switches back to Q-Eval at
    # the captured binder depth. No fresh `runMachineF` entry.
         if t == "VThunkTm"        then
           { mode = "Eval"; env = v.env; tm = v.tm;
             fuel = fuel - 1; kont = push (kqResumeQuote d) kont; }
    else if t == "VUnit"          then mkQApply kont fuel d term.mkUnit
    else if t == "VTt"            then mkQApply kont fuel d term.mkTt
    else if t == "VEmpty"         then mkQApply kont fuel d term.mkEmpty
    else if t == "VBootRefl"      then mkQApply kont fuel d term.mkBootRefl
    else if t == "VFunext"        then mkQApply kont fuel d term.mkFunext
    else if t == "VLevel"         then mkQApply kont fuel d term.mkLevel
    else if t == "VLevelZero"     then mkQApply kont fuel d term.mkLevelZero
    else if t == "VString"        then mkQApply kont fuel d term.mkString
    else if t == "VInt"           then mkQApply kont fuel d term.mkInt
    else if t == "VFloat"         then mkQApply kont fuel d term.mkFloat
    else if t == "VAttrs"         then mkQApply kont fuel d term.mkAttrs
    else if t == "VPath"          then mkQApply kont fuel d term.mkPath
    else if t == "VDerivation"    then mkQApply kont fuel d term.mkDerivation
    else if t == "VFunction"      then mkQApply kont fuel d term.mkFunction
    else if t == "VAny"           then mkQApply kont fuel d term.mkAny
    else if t == "VStringLit"     then mkQApply kont fuel d (term.mkStringLit v.value)
    else if t == "VIntLit"        then mkQApply kont fuel d (term.mkIntLit v.value)
    else if t == "VFloatLit"      then mkQApply kont fuel d (term.mkFloatLit v.value)
    else if t == "VAttrsLit"      then mkQApply kont fuel d term.mkAttrsLit
    else if t == "VPathLit"       then mkQApply kont fuel d term.mkPathLit
    else if t == "VDerivationLit" then mkQApply kont fuel d term.mkDerivationLit
    else if t == "VFnLit"         then mkQApply kont fuel d term.mkFnLit
    else if t == "VAnyLit"        then mkQApply kont fuel d term.mkAnyLit

    else if t == "VPair" then
      let fr = kqApp
        [ { inherit d; v = v.snd; } ]
        (ts: term.mkPair (builtins.elemAt ts 0) (builtins.elemAt ts 1))
        [ ];
      in mkQEval (push fr kont) fuel d v.fst

    else if t == "VPi" then
      mkQEval (push (kqBinderDomain v.name v.closure "pi" d) kont)
        fuel d v.domain
    else if t == "VLam" then
      mkQEval (push (kqBinderDomain v.name v.closure "lam" d) kont)
        fuel d v.domain
    else if t == "VSigma" then
      mkQEval (push (kqBinderDomain v.name v.closure "sigma" d) kont)
        fuel d v.fst

    else if t == "VNe" then
      let headTm = term.mkVar (d - v.level - 1); in
      if v.spine == [ ]
      then mkQApply kont fuel d headTm
      else mkQApply (push (kqSpineStep v.spine 0) kont) fuel d headTm

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
            let fr = kqApp
              [ { inherit d; v = builtins.elemAt params 1; }
                { inherit d; v = builtins.elemAt params 2; }
              ]
              (ts: term.mkDescDescAppAt
                (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2))
              [ ];
            in mkQEval (push fr kont) fuel d (builtins.elemAt params 0)
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
              fr    = kqApp (builtins.tail allPending) mkTm [ ];
            in mkQEval (push fr kont) fuel first.d first.v

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
          let fr = kqApp
            [ { inherit d; v = base.i; }
              { inherit d; v = base.d; }
            ]
            (ts: term.mkDescCon
              (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2))
            [ ];
          in mkQEval (push fr kont) fuel d base.D
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
          in mkQApply kont fuel d outerTm
        else
          # Chain-form Val (n≥2) → `mkDescConChain` Tm. Setup `kqApp`
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
            setupApp   = kqApp (builtins.tail sixSubVals) setupMkTm [ ];
          in mkQEval
            (push setupApp (push buildFrame kont))
            fuel first.d first.v

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
          let fr = kqApp
            [ { inherit d; v = v.i; }
              { inherit d; v = v.d; }
            ]
            (ts: term.mkDescCon
              (builtins.elemAt ts 0) (builtins.elemAt ts 1) (builtins.elemAt ts 2))
            [ ];
          in mkQEval (push fr kont) fuel d v.D
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
            setupApp   = kqApp (builtins.tail sixSubVals) setupMkTm [ ];
          in mkQEval
            (push setupApp (push buildFrame kont))
            fuel first.d first.v

    else mkQApply kont fuel d (fallback d v);

  # The quote driver shares `mkStepIf` with the eval driver, parameterized by
  # the caller's `fallback` so Q-Eval's leaf dispatch routes correctly. The
  # outer `genericClosure` advances by `driverChunkSize` per operator call;
  # `[]` terminates on Q-Done or exhaustion.
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
                qStepIf item.state driverChunkList;
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

  T = fx.tc.term;
  H = fx.tc.hoas;

  encRet = H.elab (H.retI H.unit 0 H.tt);

  # Out-of-bounds var: throws if forced, harmless as a thunk.
  broken = T.mkVar 99999;

  noFallback = _d: v: throw "qmachine test: unhandled tag ${v.tag}";
in
{
  scope = {
    inherit runMachineF runMachineAtF
      runDescIndAtF runDescIndLayerAtF
      runInterpDAtF runAllDAtF runEverywhereDAtF
      runQuoteF;
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
  };
}
