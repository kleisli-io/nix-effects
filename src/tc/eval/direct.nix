# Depth-budgeted hybrid front end for the kernel evaluator.
#
# `evalHybridF` runs `mkValueF` (direct recursion — the same body the
# elaboration overlay instantiates) for structural terms, threading a
# depth budget through sub-evaluations via a memoized chain of
# self-tables. At budget exhaustion the remaining sub-problem enters
# `runMachineF`, so libnix stack depth stays O(budget) regardless of
# user-recursion depth. Precedent: `trampoline.nix` `applyQueue` /
# `effectRotate` (recursive to depth 500, iterative fallback beyond).
#
# Chain construction (`desc-con`, `desc-con-chain`) punts to the
# machine, keeping chain-form Val construction and cert handling on
# the single maintained path. Running `desc-con` direct was measured
# and rejected: payloads whose evaluation reaches punted eliminators
# fragment one machine run into per-reduction entries, and each entry
# re-derives description values the single driver loop computes once
# and threads through frames (+120…+820‰ lookups on
# conv/elaboration-heavy workloads; cert-gating the split kills the
# wins too). The exceptions live inside the driver itself: the
# dispatch arm's certified chain-prepend fast path (`evalDescConFastV`,
# machine.nix) — a single certified layer over an already-evaluated
# chain-form tail is fully determined without the peel cascade — and
# the nocert `descDesc`-headed plain build (`evalDescConPlainV`), whose
# cascade output is statically the trivial n=0 case; both resolve the
# punted entry in one Apply step.
#
# The eliminator family (`desc-ind`, `interp-d`, `all-d`,
# `everywhere-d`) rides the direct path (`descIndAt`, `interpDAt`,
# `allDAt`, `everywhereDAt`): the machine's per-transition ceremony
# (state attrset + kont cells + curried constructor envs per step)
# dominated eliminator-heavy workloads. Containment of
# `VLazyDescIndAccLayer` is unaffected — the direct path expresses
# deferred work as plain Nix thunks (the layer Val is the machine's
# defunctionalized thunk; it never escapes the driver), so no layer is
# ever constructed or observed here.
{ self, fx, ... }:

let
  val = fx.tc.value;
  inherit (val) vNeSnoc eApp envCons mkClosure freshVar
    vLam vPair vTt vBootInl vBootInr vBootRefl vDescConChain eDescInd
    vSigma vPi vUnit vBootSum vBootEq vLevelZero
    eInterpD eAllD eEverywhereD;
  T = fx.tc.term;
  H = fx.tc.hoas;

  directBudget = 512;

  # Tags that must evaluate through the machine regardless of budget.
  puntTags = {
    "desc-con" = true;
    "desc-con-chain" = true;
  };

  # Tags that ride the direct path only while budget remains. At level
  # 0 the whole subtree enters the machine in one run — dispatching the
  # mkValueF arm there would fragment it into per-subterm machine
  # entries (`ev` at level 0 is `runMachineF`).
  exhaustPuntTags = {
    "desc-ind" = true;
    "interp-d" = true;
    "all-d" = true;
    "everywhere-d" = true;
  };

  evalHybridAt = i: fuel: env: tm:
    if puntTags ? ${tm.tag} || (i == 0 && exhaustPuntTags ? ${tm.tag})
    then self.runMachineF fuel env tm
    else self.mkValueF (tableAt i) fuel env tm;

  # Direct `desc-ind` at budget level `lvl` — mirrors the machine's
  # `KDescInd` classification (cert fast path / chain-form / per-layer
  # fallback) with native recursion in place of kont frames.
  #
  # Chain path: the accumulator spine is built from plain Nix thunks —
  # `accAt l idx` stays unforced until a step body demands its IH, the
  # exact cost profile of the machine's `VLazyDescIndAccLayer` spine
  # (O(1) for steps that ignore the IH, full force for genuine
  # recursion). The ladder decrements one level per layer; at level 0
  # the remaining suffix re-enters the machine as ONE `runDescIndAtF`
  # entry (`_layersOff` slicing makes the suffix Val O(1)), so native
  # stack depth stays O(budget × step-body depth) on towers of any
  # height. `descInd` of a chain suffix IS the accumulator at that
  # layer — classification depends only on D and the layers slice.
  #
  # The base-layer witness and the non-chain fallback run one layer
  # direct (`descIndLayerAt`): everywhereD walks the payload at this
  # level, and its `_ihShortcut` dispatch descends the same ladder —
  # at level 0 the remaining subtree enters the machine as one
  # `runEverywhereDAtF` entry.
  descIndAt = lvl: fuel: D: motive: step: i: scrut0:
    let scrut = self.forceVal scrut0; in
    if scrut.tag == "VNe" then
      vNeSnoc scrut (eDescInd D motive step i)
    else if scrut.tag == "VDescCon" then
      let
        # Force the motive only at the point of demand (cert path never
        # reads the domain); mirrors the machine's lazy `I`.
        I = let m = self.forceVal motive; in
          if m.tag != "VLam"
          then throw "tc: vDescInd on VDescCon requires VLam motive (got ${m.tag})"
          else m.domain;
        ihValRaw = vLam "j" I
          (mkClosure [ step motive D I ]
            (T.mkLam "x"
              (T.mkMu (T.mkVar 4) (T.mkVar 3) (T.mkVar 0))
              (T.mkDescInd (T.mkVar 4) (T.mkVar 3) (T.mkVar 2)
                (T.mkVar 1) (T.mkVar 0))));
        muFam = vLam "j" I
          (mkClosure [ I D ]
            (T.mkMu (T.mkVar 1) (T.mkVar 2) (T.mkVar 0)));
        ihVal = ihValRaw // {
          _ihShortcut = { inherit D motive step muFam I; };
        };
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
        let ap = (tableAt lvl).vAppF fuel; in
        ap (ap (ap step scrut.i) scrut.d) vTt
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
          # O(1) chain suffix: share `fullLayers`, advance the offset
          # (cf. the machine's `chainSubVal`).
          chainSubVal = idx:
            if idx == nLay then
              (vDescConChain scrut.D chainBase.i
                scrut._payloadTag scrut._payloadLeft scrut._payloadRight
                fullLayers chainBase) // { _layersOff = layersOff + nLay; }
            else
              (vDescConChain scrut.D (layerAt idx).i
                scrut._payloadTag scrut._payloadLeft scrut._payloadRight
                fullLayers chainBase) // { _layersOff = layersOff + idx; };
          # Per-layer payload, synthesized on demand (cf. the machine's
          # `synthChainFn`): heads, then the recursive chain-sub-val,
          # terminated by the ret-leaf refl witness.
          synthD = idx:
            wrapPayload
              (buildInner (layerAt idx).heads
                (vPair (chainSubVal (idx + 1)) vBootRefl));
          baseResult =
            descIndLayerAt lvl fuel D motive step ihVal muFam I
              chainBase.i chainBase.d;
          accAt = l: idx:
            if idx == nLay then baseResult
            else if l == 0 then
              self.runDescIndAtF fuel D motive step (layerAt idx).i (chainSubVal idx)
            else
              let ap = (tableAt l).vAppF fuel; in
              ap (ap (ap step (layerAt idx).i) (synthD idx))
                (vPair (accAt (l - 1) (idx + 1)) vTt);
        in
        if nLay > fuel then throw "normalization budget exceeded"
        else accAt lvl 0
      else
        descIndLayerAt lvl fuel D motive step ihVal muFam I i scrut.d
    else throw "tc: vDescInd on non-mu (tag=${scrut.tag})";

  # One desc-ind layer, direct: run everywhereD on the payload and
  # apply `step i d` to the result (cf. `vDescIndFLayer` / the
  # machine's `KDescIndLayer_GotEvResult`). `vLevelZero` placeholders
  # for L and K are sound because the step's type was checked against
  # the proper L/K at the descInd typing site.
  descIndLayerAt = lvl: fuel: D: motive: step: ihVal: muFam: I: i: d:
    let ap = (tableAt lvl).vAppF fuel; in
    ap (ap (ap step i) d)
      ((tableAt lvl).vEverywhereDF fuel vLevelZero I D vLevelZero
        muFam motive ihVal i d);

  # Direct `interp-d` at budget level `lvl` — mirrors the machine's
  # `KInterpD` view dispatch (CDMM §4.2.3) with native recursion in
  # place of kont frames. Sub-Sigma closures emit `mkInterpD` Tms, so
  # instantiation re-enters at the instantiating table's level; only
  # the descPlus arm recurses structurally here, one level down via
  # the table rebinding (machine at level 0).
  interpDAt = lvl: fuel: L: I: D0: X: i:
    if fuel <= 0 then throw "normalization budget exceeded"
    else
      let
        D = self.forceVal D0;
        tbl = tableAt lvl;
        f = fuel - 1;
        view = self.descViewF f D;
      in
      if D.tag == "VNe" then vNeSnoc D (eInterpD L I X i)
      else if view == null then
        throw "tc: vInterpD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        let
          iLev = view.iLev or vLevelZero;
          retLevel = self.levelMaxOpt L iLev;
        in
        self.vLiftF iLev retLevel vBootRefl (vBootEq I view.j i)
      else if view.idx == 1 then
        vSigma "s" view.sTy
          (mkClosure [ view.tFn L I X i ]
            (T.mkInterpD (T.mkVar 2) (T.mkVar 3)
              (T.mkApp (T.mkVar 1) (T.mkVar 0))
              (T.mkVar 4)
              (T.mkVar 5)))
      else if view.idx == 2 then
        vSigma "_" (tbl.vAppF f X view.j)
          (mkClosure [ L I X i view.sub ]
            (T.mkInterpD (T.mkVar 1) (T.mkVar 2) (T.mkVar 5)
              (T.mkVar 3)
              (T.mkVar 4)))
      else if view.idx == 3 then
        vSigma "_"
          (vPi "s" view.sTy (mkClosure [ X view.fn ]
            (T.mkApp (T.mkVar 1)
              (T.mkApp (T.mkVar 2) (T.mkVar 0)))))
          (mkClosure [ L I X i view.sub ]
            (T.mkInterpD (T.mkVar 1) (T.mkVar 2) (T.mkVar 5)
              (T.mkVar 3)
              (T.mkVar 4)))
      else
        vBootSum (tbl.vInterpDF f L I view.A X i)
          (tbl.vInterpDF f L I view.B X i);

  # Direct `all-d` at budget level `lvl` — mirrors the machine's
  # `KAllD` view dispatch (CDMM §6.1). descArg unfolds in place;
  # descRec/descPi build Sigmas whose `mkAllD` closures re-enter at
  # the instantiating table's level; descPlus recurses one level down,
  # with the stuck-`d` case staged through `vBootSumElimF` exactly as
  # the machine's PlusStuck frames do.
  allDAt = lvl: fuel: L: I: D0: K: X: M: i: d0:
    if fuel <= 0 then throw "normalization budget exceeded"
    else
      let
        D = self.forceVal D0;
        tbl = tableAt lvl;
        f = fuel - 1;
        view = self.descViewF f D;
        d = self.forceVal d0;
      in
      if D.tag == "VNe" then vNeSnoc D (eAllD L I K X M i d0)
      else if view == null then
        throw "tc: vAllD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        self.vLiftF vLevelZero K vBootRefl vUnit
      else if view.idx == 1 then
        tbl.vAllDF f L I (tbl.vAppF f view.tFn (self.vFst d)) K X M i
          (self.vSnd d)
      else if view.idx == 2 then
        vSigma "_" (tbl.vAppF f (tbl.vAppF f M view.j) (self.vFst d))
          (mkClosure [ L I K X M i (self.vSnd d) view.sub ]
            (T.mkAllD (T.mkVar 1) (T.mkVar 2) (T.mkVar 8)
              (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
              (T.mkVar 6) (T.mkVar 7)))
      else if view.idx == 3 then
        vSigma "_"
          (vPi "s" view.sTy (mkClosure [ M view.fn (self.vFst d) ]
            (T.mkApp
              (T.mkApp (T.mkVar 1)
                (T.mkApp (T.mkVar 2) (T.mkVar 0)))
              (T.mkApp (T.mkVar 3) (T.mkVar 0)))))
          (mkClosure [ L I K X M i (self.vSnd d) view.sub ]
            (T.mkAllD (T.mkVar 1) (T.mkVar 2) (T.mkVar 8)
              (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
              (T.mkVar 6) (T.mkVar 7)))
      else
        let sv = self.sumPayloadValView d; in
        if sv != null then
          (if sv.side == "inl"
           then tbl.vAllDF f L I view.A K X M i sv.value
           else tbl.vAllDF f L I view.B K X M i sv.value)
        else if d.tag == "VNe" then
          let
            AInterp = tbl.vInterpDF f L I view.A X i;
            BInterp = tbl.vInterpDF f L I view.B X i;
            motive = vLam "_" (vBootSum AInterp BInterp)
              (mkClosure [ K ] (T.mkU (T.mkVar 1)));
            onLeftLam = vLam "a" AInterp
              (mkClosure [ L I K X M i view.A ]
                (T.mkAllD (T.mkVar 1) (T.mkVar 2) (T.mkVar 7)
                  (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
                  (T.mkVar 6) (T.mkVar 0)));
            onRightLam = vLam "b" BInterp
              (mkClosure [ L I K X M i view.B ]
                (T.mkAllD (T.mkVar 1) (T.mkVar 2) (T.mkVar 7)
                  (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
                  (T.mkVar 6) (T.mkVar 0)));
          in
          self.vBootSumElimF f AInterp BInterp motive onLeftLam onRightLam d
        else throw "tc: vAllD on plus with non-sum d (tag=${d.tag})";

  # Direct `everywhere-d` at budget level `lvl` — mirrors the
  # machine's `KEverywhereD` view dispatch (CDMM §6.1), including the
  # `_ihShortcut` fast path on descRec (the machine's KEverywhereD →
  # KDescIndLayer_GotEvResult staging, expressed as nested calls).
  # Pair components are native lazy thunks — steps that ignore the IH
  # never force it, the same cost profile as the machine's lazy layer
  # spine.
  everywhereDAt = lvl: fuel: L: I: D0: K: X: M: ih: i: d0:
    if fuel <= 0 then throw "normalization budget exceeded"
    else
      let
        D = self.forceVal D0;
        tbl = tableAt lvl;
        f = fuel - 1;
        view = self.descViewF f D;
        d = self.forceVal d0;
      in
      if D.tag == "VNe" then vNeSnoc D (eEverywhereD L I K X M ih i d0)
      else if view == null then
        throw "tc: vEverywhereD on non-desc or malformed desc (tag=${D.tag})"
      else if view.idx == 0 then
        self.vLiftIntroF vLevelZero K vBootRefl vUnit vTt
      else if view.idx == 1 then
        tbl.vEverywhereDF f L I (tbl.vAppF f view.tFn (self.vFst d)) K X M ih i
          (self.vSnd d)
      else if view.idx == 2 then
        let
          fstD = self.vFst d;
          ap = tbl.vAppF f;
          ihHere =
            if ih ? _ihShortcut && fstD.tag == "VDescCon"
            then
              let s = ih._ihShortcut; in
              ap (ap (ap s.step view.j) fstD.d)
                (tbl.vEverywhereDF f vLevelZero s.I s.D vLevelZero
                  s.muFam s.motive ih view.j fstD.d)
            else ap (ap ih view.j) fstD;
        in
        vPair ihHere
          (tbl.vEverywhereDF f L I view.sub K X M ih i (self.vSnd d))
      else if view.idx == 3 then
        let
          piLam = vLam "s" view.sTy (mkClosure [ ih view.fn (self.vFst d) ]
            (T.mkApp
              (T.mkApp (T.mkVar 1)
                (T.mkApp (T.mkVar 2) (T.mkVar 0)))
              (T.mkApp (T.mkVar 3) (T.mkVar 0))));
        in
        vPair piLam
          (tbl.vEverywhereDF f L I view.sub K X M ih i (self.vSnd d))
      else
        let sv = self.sumPayloadValView d; in
        if sv != null then
          (if sv.side == "inl"
           then tbl.vEverywhereDF f L I view.A K X M ih i sv.value
           else tbl.vEverywhereDF f L I view.B K X M ih i sv.value)
        else if d.tag == "VNe" then
          let
            AInterp = tbl.vInterpDF f L I view.A X i;
            BInterp = tbl.vInterpDF f L I view.B X i;
            motive = vLam "_" (vBootSum AInterp BInterp)
              (mkClosure [ K ] (T.mkU (T.mkVar 1)));
            onLeftLam = vLam "a" AInterp
              (mkClosure [ L I K X M ih i view.A ]
                (T.mkEverywhereD (T.mkVar 1) (T.mkVar 2) (T.mkVar 8)
                  (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
                  (T.mkVar 6) (T.mkVar 7) (T.mkVar 0)));
            onRightLam = vLam "b" BInterp
              (mkClosure [ L I K X M ih i view.B ]
                (T.mkEverywhereD (T.mkVar 1) (T.mkVar 2) (T.mkVar 8)
                  (T.mkVar 3) (T.mkVar 4) (T.mkVar 5)
                  (T.mkVar 6) (T.mkVar 7) (T.mkVar 0)));
          in
          self.vBootSumElimF f AInterp BInterp motive onLeftLam onRightLam d
        else throw "tc: vEverywhereD on plus with non-sum d (tag=${d.tag})";

  # tableAt i: dispatch table for sub-evaluations with i budget levels
  # remaining. Every level rebinds `evalF`/`instantiateF`/`vAppF` so
  # structural recursion AND beta descent decrement the budget; at
  # level 0 `evalF` is the machine, so both descent paths exhaust into
  # iterative evaluation. (`vAppF` must be rebound at level 0 too: the
  # fixpoint `vAppF` instantiates through `self.instantiateF`, which
  # re-enters at full budget — unbounded native recursion for app
  # chains deeper than the budget.) The eliminator helpers
  # (`vDescIndF`/`vInterpDF`/`vAllDF`/`vEverywhereDF`) are rebound so
  # the mkValueF arms and the eliminators' own structural recursion
  # run the direct versions at the decremented level; at level 0 they
  # are machine wrappers (term-level dispatch is already routed there
  # by the `exhaustPuntTags` entry check — rebinding covers the
  # structural-recursion path, which punts the remaining subtree as
  # one machine entry). All other helpers stay fixpoint-bound (they
  # re-enter at full budget, like any external caller).
  tableAt = i: builtins.elemAt tables i;
  tables = builtins.genList mkTable (directBudget + 1);
  mkTable = i:
    let
      s = self // {
        evalF = if i == 0 then self.runMachineF else evalHybridAt (i - 1);
        instantiateF = fuel: cl: arg:
          s.evalF fuel ({ head = arg; tail = cl.env; }) cl.body;
        vAppF = fuel: fn0: arg:
          let fn = self.forceVal fn0; in
          if fn.tag == "VDescViewFn" then self.applyDescViewFnByKindF fuel fn arg
          else if fn.tag == "VLam" then s.instantiateF fuel fn.closure arg
          else if fn.tag == "VNe" then vNeSnoc fn (eApp arg)
          else throw "tc: vApp on non-function (tag=${fn.tag})";
        vDescIndF = if i == 0 then self.vDescIndF else descIndAt (i - 1);
        vInterpDF = if i == 0 then self.vInterpDF else interpDAt (i - 1);
        vAllDF = if i == 0 then self.vAllDF else allDAt (i - 1);
        vEverywhereDF = if i == 0 then self.vEverywhereDF else everywhereDAt (i - 1);
      };
    in
    s;

  evalHybridF = evalHybridAt directBudget;

  # Fresh-budget direct `interp-d` entry. The machine's `KInterpD`
  # handler calls this for a `VDescCon` description, building the
  # interpretation by native recursion (`interpDAt`, which mirrors the
  # machine's `KInterpD`/`KResume_KInterpD_GotView` view dispatch) in
  # place of the per-step `kDescView`+decode-walk state cascade.
  interpDDirectF = interpDAt directBudget;

  encRet = H.elab (H.retI H.unit 0 H.tt);
  xUnit = T.mkLam "_" T.mkUnit T.mkUnit;

  # Elaborated `cons tt (cons tt … nil) : listOf unit` — a linear
  # desc-con chain of depth n with per-layer certs.
  consChainTm = n:
    H.elab (H.ann
      (builtins.foldl' (acc: _: H.cons H.tt acc) H.nil
        (builtins.genList (i: i) n))
      (H.listOf H.unit));

  # `decElim` sentinel over `decideLeNat n n` (cf.
  # bench/workloads/tc/decidable.nix): collapses the closure-bearing
  # dec proof to a closed nat, so the result quotes in O(1). Quoting or
  # conv-ing the raw proof is superlinear on EITHER evaluator (each
  # VLam re-instantiates a proof tower), so observable-result parity is
  # the only suite-affordable check.
  decDiagProbe = n:
    let
      nv = H.natLit n;
      P = H.le nv nv;
    in
    H.elab (H.decElim P
      (H.lam "_" (H.dec P) (_: H.nat))
      (H.lam "_" P (_: H.zero))
      (H.lam "_" (H.not P) (_: H.succ H.zero))
      (H.app (H.app H.decideLeNat nv) nv));

in
{
  scope = {
    inherit evalHybridF interpDDirectF;
  };

  tests = {
    "hybrid-eval-tt" = {
      expr = (evalHybridF self.defaultFuel [ ] T.mkTt).tag;
      expected = "VTt";
    };
    "hybrid-eval-beta" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt)).tag;
      expected = "VTt";
    };

    # Punt tag: an `interp-d` Tm routes to the machine and lands the
    # same value the machine computes (cf. `desc.nix` "vInterpD-ret").
    "hybrid-eval-punt-interp-d" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (T.mkInterpD T.mkLevelZero T.mkUnit encRet xUnit T.mkTt)).tag;
      expected = "VBootEq";
    };

    # Structural descent deeper than the budget must hand off to the
    # machine instead of growing the libnix stack.
    "hybrid-eval-let-chain-10000" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
          (T.mkVar 0)
          (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };

    # Beta descent must decrement the budget through
    # `vAppF`/`instantiateF` — re-entering at full budget would
    # overflow the stack long before depth 10000.
    "hybrid-eval-beta-chain-10000" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkApp (T.mkLam "x" T.mkUnit acc) T.mkTt)
          T.mkTt
          (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };

    # desc-con through evalHybridF dispatch lands the chain-form Val.
    "hybrid-eval-desc-con-chain-form" = {
      expr =
        let v = evalHybridF self.defaultFuel [ ] (consChainTm 5); in
        { shape = v._shape or null; layers = builtins.length (self.effLayers v); };
      expected = { shape = "linearChain"; layers = 5; };
    };

    # evalHybridF dispatch and a bare machine run must agree
    # definitionally on desc-con chains.
    "hybrid-eval-desc-con-machine-parity" = {
      expr =
        let
          tm = consChainTm 5;
          vH = evalHybridF self.defaultFuel [ ] tm;
          vM = self.runMachineF self.defaultFuel [ ] tm;
        in
        fx.tc.conv.conv 0 vH vM;
      expected = true;
    };

    # The chain peel is genericClosure-iterative — depth must not
    # consume native stack.
    "hybrid-eval-desc-con-chain-10000" = {
      expr =
        builtins.length
          (self.effLayers (evalHybridF self.defaultFuel [ ] (consChainTm 10000)));
      expected = 10000;
    };

    # Direct desc-ind: stuck scrutinee extends the spine (cf. core.nix
    # "eval-desc-ind-stuck").
    "hybrid-desc-ind-stuck" = {
      expr = (evalHybridF self.defaultFuel [ (freshVar 0) ]
        (T.mkDescInd encRet (T.mkVar 0) (T.mkVar 0) T.mkTt (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # Direct interp-d: stuck D extends the spine with an EInterpD
    # frame; canonical ret-desc reduces to the Eq type.
    "hybrid-interp-d-stuck" = {
      expr =
        let
          v = evalHybridF self.defaultFuel [ (freshVar 0) ]
            (T.mkInterpD T.mkLevelZero T.mkUnit (T.mkVar 0) xUnit T.mkTt);
        in
        { tag = v.tag; frame = (builtins.elemAt v.spine 0).tag; };
      expected = { tag = "VNe"; frame = "EInterpD"; };
    };
    "hybrid-interp-d-ret" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (T.mkInterpD T.mkLevelZero T.mkUnit encRet xUnit T.mkTt)).tag;
      expected = "VBootEq";
    };

    # Direct desc-ind, fallback path: a plain (non-cert, non-chain)
    # VDescCon routes through `runDescIndLayerAtF` (cf. core.nix
    # "eval-desc-ind-ret-con").
    "hybrid-desc-ind-ret-con" = {
      expr =
        let
          D = encRet;
          P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
          step = T.mkLam "i" T.mkUnit
            (T.mkLam "d" T.mkUnit
              (T.mkLam "ih" T.mkUnit T.mkTt));
          scrut = T.mkDescCon D T.mkTt T.mkBootRefl;
        in
        (evalHybridF self.defaultFuel [ ] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VTt";
    };

    # Direct desc-ind, chain path with genuine recursion: `decideLeNat`
    # is doubly ind-recursive over chain-form nats; hybrid and bare
    # machine runs must agree on the sentinel-collapsed result, and
    # decide yes (`zero`).
    "hybrid-desc-ind-chain-parity" = {
      expr =
        let
          tm = decDiagProbe 5;
          qH = fx.tc.quote.quote 0 (evalHybridF self.defaultFuel [ ] tm);
          qM = fx.tc.quote.quote 0 (self.runMachineF self.defaultFuel [ ] tm);
          zeroTm = fx.tc.quote.quote 0 (evalHybridF self.defaultFuel [ ] (H.elab H.zero));
        in
        { agree = qH == qM; yes = qH == zeroTm; };
      expected = { agree = true; yes = true; };
    };

    # Tower deeper than the budget: the chain ladder exhausts and the
    # remaining suffix re-enters the machine as one entry — correct at
    # any depth, no native-stack growth. Hybrid side only: a bare
    # machine run of the full tower is suite-unaffordable; machine
    # parity is covered at n=5 above.
    "hybrid-desc-ind-chain-deep" = {
      expr =
        let
          tm = decDiagProbe (directBudget + 100);
          qH = fx.tc.quote.quote 0 (evalHybridF self.defaultFuel [ ] tm);
          zeroTm = fx.tc.quote.quote 0 (evalHybridF self.defaultFuel [ ] (H.elab H.zero));
        in
        qH == zeroTm;
      expected = true;
    };
  };
}
