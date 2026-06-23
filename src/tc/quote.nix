# Type-checking kernel: Quotation (quote)
#
# quote : Depth -> Val -> Tm
# Converts a value back to a term, converting de Bruijn levels to indices.
# Pure function — zero effect system imports.
#
# Spec reference: kernel-spec.md §5
{ fx, api, ... }:
let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;

  # Cached `U(0)` term sentinel. Quoting a `VU` whose level is the
  # `VLevelZero` singleton reduces to this shared term — no per-call
  # allocation of the `{tag="U"; level={tag="level-zero"}}` pair.
  mkUZero = T.mkU T.mkLevelZero;

  # Level to index conversion: index = depth - level - 1
  lvl2Ix = depth: level: depth - level - 1;

  # Quote-machine driver bound with `quote` as the fallback. Tags whose
  # dispatch lives in `qEvalStep` (binders, VPair, leaves) route here;
  # the machine calls back into `quote` for any tag it does not handle,
  # giving an incremental migration boundary.
  runQ = E.machine.runQuoteF quote E.dispatch.defaultFuel;

  # Quote a value at binding depth d back to a term.
  # `quote` is a read-back boundary: force `v` to WHNF through the
  # iterative driver before inspecting its tag, so a deferred `VThunkTm`
  # (at the top or at any recursively-quoted sub-field) reduces to its
  # underlying Val rather than falling through to the unknown-tag throw.
  # One-step WHNF only — sub-fields stay lazy until their own `quote` call.
  quote = d: v0:
    let v = E.forceVal v0; t = v.tag; in
    if t == "VPi" then runQ d v
    else if t == "VLam" then runQ d v
    else if t == "VSigma" then runQ d v
    else if t == "VPair" then runQ d v
    else if t == "VUnit" then T.mkUnit
    else if t == "VTt" then T.mkTt
    else if t == "VEmpty" then T.mkEmpty
    else if t == "VBootSum" then T.mkBootSum (quote d v.left) (quote d v.right)
    else if t == "VBootInl" then T.mkBootInl (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VBootInr" then T.mkBootInr (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VBootEq" then T.mkBootEq (quote d v.type) (quote d v.lhs) (quote d v.rhs)
    else if t == "VBootRefl" then T.mkBootRefl
    else if t == "VFunext" then T.mkFunext
    else if t == "VSquash" then T.mkSquash (quote d v.A)
    else if t == "VSquashIntro" then T.mkSquashIntro (quote d v.a)
    # Descriptions
    else if t == "VDesc" then
    # Level-zero fast-path: prelude descriptions live at `desc^0`,
    # so emit the cached `T.mkLevelZero` sentinel directly instead
    # of recursively quoting `VLevelZero`. When `iLev` is non-zero,
    # emit `mkDescAt` to round-trip the index-universe slot; at
    # `iLev = vLevelZero` the level-zero `mkDesc` constructor is
    # the compact source form.
      let
        iLevVal = E.forceVal (v.iLev or V.vLevelZero);
        levelTm =
          if v.level.tag == "VLevelZero"
          then T.mkLevelZero
          else quote d v.level;
        iTm = quote d v.I;
      in
      if iLevVal.tag == "VLevelZero"
      then T.mkDesc levelTm iTm
      else T.mkDescAt (quote d iLevVal) levelTm iTm
    else if t == "VMu" then T.mkMu (quote d v.I) (quote d v.D) (quote d v.i)
    else if t == "VDescCon" then runQ d v
    # Lift primitive — round-trip type-former and introducer. Level-zero
    # fast-path on `v.l` / `v.m` mirrors the desc-arg / desc-pi shape.
    else if t == "VLift" then
      T.mkLift
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (if v.m.tag == "VLevelZero" then T.mkLevelZero else quote d v.m)
        (quote d v.eq)
        (quote d v.A)
    else if t == "VLiftIntro" then
      T.mkLiftIntro
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (if v.m.tag == "VLevelZero" then T.mkLevelZero else quote d v.m)
        (quote d v.eq)
        (quote d v.A)
        (quote d v.a)
    else if t == "VU" then
      if v.level.tag == "VLevelZero" then mkUZero
      else T.mkU (quote d v.level)
    else if t == "VLevel" then T.mkLevel
    else if t == "VLevelZero" then T.mkLevelZero
    else if t == "VLevelSuc" then T.mkLevelSuc (quote d v.pred)
    else if t == "VLevelMax" then T.mkLevelMax (quote d v.lhs) (quote d v.rhs)
    else if t == "VString" then T.mkString
    else if t == "VInt" then T.mkInt
    else if t == "VFloat" then T.mkFloat
    else if t == "VAttrs" then T.mkAttrs
    else if t == "VPath" then T.mkPath
    else if t == "VDerivation" then T.mkDerivation
    else if t == "VFunction" then T.mkFunction
    else if t == "VAny" then T.mkAny
    else if t == "VStringLit" then T.mkStringLit v.value
    else if t == "VIntLit" then T.mkIntLit v.value
    else if t == "VFloatLit" then T.mkFloatLit v.value
    else if t == "VAttrsLit" then T.mkAttrsLit
    else if t == "VPathLit" then T.mkPathLit
    else if t == "VDerivationLit" then T.mkDerivationLit
    else if t == "VFnLit" then T.mkFnLit
    else if t == "VAnyLit" then T.mkAnyLit
    else if t == "VOpaqueLam" then T.mkOpaqueLam v._fnBox (quote d v.piTy)
    else if t == "VNe" then runQ d v
    else throw "tc: quote unknown tag '${t}'";

  # Quote a spine of eliminators applied to a head term.
  quoteSp = d: head: spine:
    builtins.foldl' (acc: elim: quoteElim d acc elim) head spine;

  # Quote a single elimination frame applied to a head term.
  quoteElim = d: head: elim:
    let t = elim.tag; in
    if t == "EApp" then T.mkApp head (quote d elim.arg)
    else if t == "EFst" then T.mkFst head
    else if t == "ESnd" then T.mkSnd head
    else if t == "EBootSumElim" then
      T.mkBootSumElim (quote d elim.left) (quote d elim.right) (quote d elim.motive)
        (quote d elim.onLeft)
        (quote d elim.onRight)
        head
    else if t == "EBootJ" then
      T.mkBootJ (quote d elim.type) (quote d elim.lhs) (quote d elim.motive)
        (quote d elim.base)
        (quote d elim.rhs)
        head
    else if t == "EStrEq" then T.mkStrEq head (quote d elim.arg)
    else if t == "EIntEq" then T.mkIntEq head (quote d elim.arg)
    else if t == "EIntLeL" then T.mkIntLe head (quote d elim.arg)
    else if t == "EIntLeR" then T.mkIntLe (quote d elim.arg) head
    else if t == "EAbsurd" then T.mkAbsurd (quote d elim.type) head
    else if t == "EDescInd" then
      T.mkDescInd (quote d elim.D) (quote d elim.motive) (quote d elim.step) (quote d elim.i) head
    # `EInterpD` / `EAllD` / `EEverywhereD` round-trip stuck `interpD` /
    # `allD` / `everywhereD` on a neutral D scrutinee. The frame stores
    # every slot OTHER than D (the spine head). Level-zero fast-path on
    # `level` (and `K` where present) emits the cached `T.mkLevelZero`
    # sentinel.
    else if t == "EInterpD" then
      T.mkInterpD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (quote d elim.X)
        (quote d elim.i)
    else if t == "EAllD" then
      T.mkAllD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (if elim.K.tag == "VLevelZero" then T.mkLevelZero else quote d elim.K)
        (quote d elim.X)
        (quote d elim.M)
        (quote d elim.i)
        (quote d elim.d)
    else if t == "EEverywhereD" then
      T.mkEverywhereD
        (if elim.level.tag == "VLevelZero" then T.mkLevelZero else quote d elim.level)
        (quote d elim.I)
        head
        (if elim.K.tag == "VLevelZero" then T.mkLevelZero else quote d elim.K)
        (quote d elim.X)
        (quote d elim.M)
        (quote d elim.ih)
        (quote d elim.i)
        (quote d elim.d)
    # ELiftElim spine frame round-trips to `mkLiftElim l m eq A head`.
    # Level-zero fast-path on `l` / `m` mirrors the in-quote-rule shape.
    else if t == "ELiftElim" then
      T.mkLiftElim
        (if elim.l.tag == "VLevelZero" then T.mkLevelZero else quote d elim.l)
        (if elim.m.tag == "VLevelZero" then T.mkLevelZero else quote d elim.m)
        (quote d elim.eq)
        (quote d elim.A)
        head
    else if t == "ESquashElim" then
      T.mkSquashElim (quote d elim.A) (quote d elim.B) (quote d elim.f) head
    else throw "tc: quoteElim unknown tag '${t}'";

  # Normalize: eval then quote
  nf = env: tm: quote (builtins.length env) (E.eval env tm);

in
api.namespace {
  description = "fx.tc.quote: TCB read-back from values to terms, translating de Bruijn levels back to indices; pure, no type information, no effects.";
  doc = ''
    # fx.tc.quote — Quotation (Read-back)

    Converts values back to terms, translating de Bruijn levels to
    indices. Pure function — part of the TCB.

    ## Core Functions

    - `quote : Depth → Val → Tm` — read back a value at binding depth d.
      Level-to-index conversion: `index = depth - level - 1`.
    - `quoteSp : Depth → Tm → Spine → Tm` — quote a spine of eliminators
      applied to a head term (folds left over the spine).
    - `quoteElim : Depth → Tm → Elim → Tm` — quote a single elimination
      frame applied to a head term.
    - `nf : Env → Tm → Tm` — normalize: `eval` then `quote`. Useful for
      testing roundtrip idempotency (`nf env (nf env tm) == nf env tm`).
    - `lvl2Ix : Depth → Level → Index` — level-to-index helper.

    ## Trampolining

    Linear VDescCon chains are quoted iteratively via `genericClosure`
    for O(1) stack depth on deep generated data (5000+ elements).

    ## Binder Quotation

    For VPi, VLam, VSigma: instantiates the closure with a fresh
    variable at the current depth, then quotes the body at `depth + 1`.
  '';
  tests =
    let
      inherit (V) vPi vLam vSigma vPair
        vUnit vTt vBootSum vBootInl vBootInr vBootEq vBootRefl vU vNe
        mkClosure eApp eFst eSnd eBootSumElim eBootJ;
      H = fx.tc.hoas;
      HI = fx.tc.hoas._internal._indexed;
      encRet = H.elab (H.retI H.unit 0 H.tt);
      encArg = H.elab (H.descArg H.unit 0 H.nat (_: H.retI H.unit 0 H.tt));
      encRec = H.elab (HI.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
      encPi = H.elab (H.descPi 0 H.nat (H.retI H.unit 0 H.tt));
      encRetVal = E.eval [ ] encRet;
    in
    {
      # -- Level to index --
      "lvl2ix-0" = { expr = lvl2Ix 1 0; expected = 0; };
      "lvl2ix-1" = { expr = lvl2Ix 3 0; expected = 2; };
      "lvl2ix-2" = { expr = lvl2Ix 3 2; expected = 0; };

      # -- Simple values --
      "quote-unit" = { expr = (quote 0 vUnit).tag; expected = "unit"; };
      "quote-tt" = { expr = (quote 0 vTt).tag; expected = "tt"; };
      "quote-refl" = { expr = (quote 0 vBootRefl).tag; expected = "boot-refl"; };
      "quote-funext" = { expr = (quote 0 V.vFunext).tag; expected = "funext"; };
      "quote-squash" = { expr = (quote 0 (V.vSquash V.vUnit)).tag; expected = "squash"; };
      "quote-squash-A" = {
        expr = (quote 0 (V.vSquash V.vUnit)).A.tag;
        expected = "unit";
      };
      "quote-squash-intro" = {
        expr = (quote 0 (V.vSquashIntro V.vTt)).tag;
        expected = "squash-intro";
      };
      "quote-squash-intro-a" = {
        expr = (quote 0 (V.vSquashIntro V.vTt)).a.tag;
        expected = "tt";
      };
      "quote-ne-squash-elim" = {
        # Stuck `recTrunc` on a neutral round-trips to `mkSquashElim …`.
        expr =
          let
            fLam = V.vLam "_" V.vUnit (mkClosure [ ] T.mkTt);
          in
          (quote 1 (V.vNe 0
            [ (V.eSquashElim V.vUnit V.vUnit fLam) ])).tag;
        expected = "squash-elim";
      };
      "nf-squash-intro-roundtrip" = {
        expr = let tm = T.mkSquashIntro T.mkTt; in
          nf [ ] (nf [ ] tm) == nf [ ] tm;
        expected = true;
      };
      "quote-U0" = { expr = (quote 0 (vU V.vLevelZero)).tag; expected = "U"; };
      "quote-U0-level" = {
        expr = (quote 0 (vU V.vLevelZero)).level.tag;
        expected = "level-zero";
      };
      "quote-U1-level-pred" = {
        expr = (quote 0 (vU (V.vLevelSuc V.vLevelZero))).level.pred.tag;
        expected = "level-zero";
      };
      "quote-U-level-max" = {
        expr = (quote 0 (vU (V.vLevelMax V.vLevelZero V.vLevelZero))).level.tag;
        expected = "level-max";
      };
      "quote-level" = { expr = (quote 0 V.vLevel).tag; expected = "level"; };
      "quote-level-zero" = { expr = (quote 0 V.vLevelZero).tag; expected = "level-zero"; };
      "quote-level-suc" = {
        expr = (quote 0 (V.vLevelSuc V.vLevelZero)).tag;
        expected = "level-suc";
      };
      "quote-level-max" = {
        expr = (quote 0 (V.vLevelMax V.vLevelZero V.vLevelZero)).tag;
        expected = "level-max";
      };
      "quote-string" = { expr = (quote 0 V.vString).tag; expected = "string"; };
      "quote-int" = { expr = (quote 0 V.vInt).tag; expected = "int"; };
      "quote-float" = { expr = (quote 0 V.vFloat).tag; expected = "float"; };
      "quote-attrs" = { expr = (quote 0 V.vAttrs).tag; expected = "attrs"; };
      "quote-path" = { expr = (quote 0 V.vPath).tag; expected = "path"; };
      "quote-derivation" = { expr = (quote 0 V.vDerivation).tag; expected = "derivation"; };
      "quote-function" = { expr = (quote 0 V.vFunction).tag; expected = "function"; };
      "quote-any" = { expr = (quote 0 V.vAny).tag; expected = "any"; };
      "quote-string-lit" = { expr = (quote 0 (V.vStringLit "hi")).tag; expected = "string-lit"; };
      "quote-string-lit-value" = { expr = (quote 0 (V.vStringLit "hi")).value; expected = "hi"; };
      "quote-int-lit" = { expr = (quote 0 (V.vIntLit 7)).tag; expected = "int-lit"; };
      "quote-int-lit-value" = { expr = (quote 0 (V.vIntLit 7)).value; expected = 7; };
      "quote-float-lit" = { expr = (quote 0 (V.vFloatLit 1.5)).tag; expected = "float-lit"; };
      "quote-attrs-lit" = { expr = (quote 0 V.vAttrsLit).tag; expected = "attrs-lit"; };
      "quote-path-lit" = { expr = (quote 0 V.vPathLit).tag; expected = "path-lit"; };
      "quote-derivation-lit" = { expr = (quote 0 V.vDerivationLit).tag; expected = "derivation-lit"; };
      "quote-fn-lit" = { expr = (quote 0 V.vFnLit).tag; expected = "fn-lit"; };
      "quote-any-lit" = { expr = (quote 0 V.vAnyLit).tag; expected = "any-lit"; };

      # -- Compound values --
      "quote-pair" = { expr = (quote 0 (vPair vTt vTt)).tag; expected = "pair"; };
      "quote-boot-sum" = { expr = (quote 0 (vBootSum vUnit vUnit)).tag; expected = "boot-sum"; };
      "quote-boot-inl" = { expr = (quote 0 (vBootInl vUnit vUnit vTt)).tag; expected = "boot-inl"; };
      "quote-boot-inr" = { expr = (quote 0 (vBootInr vUnit vUnit vTt)).tag; expected = "boot-inr"; };
      "quote-eq" = { expr = (quote 0 (vBootEq vUnit vTt vTt)).tag; expected = "boot-eq"; };

      # -- Neutrals --
      "quote-var" = {
        # Neutral at level 0, depth 1 → index 0
        expr = (quote 1 (vNe 0 [ ])).tag;
        expected = "var";
      };
      "quote-var-idx" = {
        expr = (quote 1 (vNe 0 [ ])).idx;
        expected = 0;
      };
      "quote-var-deep" = {
        # Neutral at level 0, depth 3 → index 2
        expr = (quote 3 (vNe 0 [ ])).idx;
        expected = 2;
      };
      "quote-ne-app" = {
        # x applied to tt: VNe(0, [EApp VTt]) at depth 1 → App(Var(0), Tt)
        expr = (quote 1 (vNe 0 [ (eApp vTt) ])).tag;
        expected = "app";
      };
      "quote-ne-fst" = {
        expr = (quote 1 (vNe 0 [ eFst ])).tag;
        expected = "fst";
      };
      "quote-ne-snd" = {
        expr = (quote 1 (vNe 0 [ eSnd ])).tag;
        expected = "snd";
      };
      "quote-ne-boot-sum-elim" = {
        expr = (quote 1 (vNe 0 [ (eBootSumElim vUnit vUnit vUnit vTt vTt) ])).tag;
        expected = "boot-sum-elim";
      };
      "quote-ne-j" = {
        expr = (quote 1 (vNe 0 [ (eBootJ vUnit vTt vUnit vTt vTt) ])).tag;
        expected = "boot-j";
      };

      # -- Descriptions (indexed) --
      "quote-desc" = { expr = (quote 0 (V.vDesc V.vLevelZero V.vUnit)).tag; expected = "desc"; };
      "quote-desc-ret" = { expr = (nf [ ] encRet).tag; expected = "desc-con"; };
      "quote-desc-arg" = {
        expr = (nf [ ] encArg).tag;
        expected = "desc-con";
      };
      "quote-desc-rec" = {
        expr = (nf [ ] encRec).tag;
        expected = "desc-con";
      };
      "quote-desc-pi" = {
        expr = (nf [ ] encPi).tag;
        expected = "desc-con";
      };
      "quote-desc-pi-S" = {
        expr = (E.descView (E.eval [ ] (nf [ ] encPi))).sTy.tag;
        expected = "VMu";
      };
      "quote-desc-pi-D" = {
        expr = (E.descView (E.descView (E.eval [ ] (nf [ ] encPi))).sub).idx;
        expected = 0;
      };
      "quote-mu" = {
        expr = (quote 0 (V.vMu V.vUnit encRetVal V.vTt)).tag;
        expected = "mu";
      };
      "quote-desc-con" = {
        expr = (quote 0 (V.vDescCon encRetVal V.vTt V.vBootRefl)).tag;
        expected = "desc-con";
      };
      "quote-ne-desc-ind" = {
        expr = (quote 1 (V.vNe 0 [ (V.eDescInd encRetVal V.vUnit V.vTt V.vTt) ])).tag;
        expected = "desc-ind";
      };
      "quote-ne-interp-d" = {
        # Stuck `interpD` on a neutral D round-trips to `mkInterpD`.
        expr = (quote 1 (V.vNe 0
          [ (V.eInterpD V.vLevelZero V.vUnit V.vUnit V.vTt) ])).tag;
        expected = "interp-d";
      };
      "quote-ne-interp-d-level-zero-fastpath" = {
        expr = (quote 1 (V.vNe 0
          [ (V.eInterpD V.vLevelZero V.vUnit V.vUnit V.vTt) ])).level.tag;
        expected = "level-zero";
      };
      "quote-ne-all-d" = {
        expr = (quote 1 (V.vNe 0
          [ (V.eAllD V.vLevelZero V.vUnit V.vLevelZero V.vUnit V.vUnit V.vTt V.vBootRefl) ])).tag;
        expected = "all-d";
      };
      "quote-ne-everywhere-d" = {
        expr = (quote 1 (V.vNe 0
          [ (V.eEverywhereD V.vLevelZero V.vUnit V.vLevelZero V.vUnit V.vUnit V.vUnit V.vTt V.vBootRefl) ])).tag;
        expected = "everywhere-d";
      };
      # Round-trip via `nf` on a stuck `interpD`: the resulting term mirrors
      # the input shape after eval-then-quote.
      "nf-interp-d-stuck-roundtrip" = {
        expr =
          let
            tm = T.mkInterpD T.mkLevelZero T.mkUnit (T.mkVar 0)
              (T.mkLam "_" T.mkUnit T.mkUnit)
              T.mkTt;
            env = [ (V.freshVar 0) ];
          in
          nf env (nf env tm) == nf env tm;
        expected = true;
      };

      # Lift primitive — type-former, introducer, and stuck-eliminator
      # spine frame. Tests use level-zero throughout for the fast-path
      # singleton; `l ≠ m` cases test the non-collapsed shape.
      "quote-lift-distinct-levels" = {
        expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl
          V.vUnit)).tag;
        expected = "lift";
      };
      "quote-lift-l-zero-fastpath" = {
        expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl
          V.vUnit)).l.tag;
        expected = "level-zero";
      };
      "quote-lift-A" = {
        expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl
          V.vUnit)).A.tag;
        expected = "unit";
      };
      "quote-lift-intro-distinct-levels" = {
        expr = (quote 0 (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl
          V.vUnit
          V.vTt)).tag;
        expected = "lift-intro";
      };
      "quote-lift-intro-a" = {
        expr = (quote 0 (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl
          V.vUnit
          V.vTt)).a.tag;
        expected = "tt";
      };
      "quote-ne-lift-elim" = {
        # Stuck `lower` on a neutral: VNe(0, [ELiftElim …]) round-trips
        # to `mkLiftElim l m eq A (Var 0)`.
        expr = (quote 1 (V.vNe 0
          [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              V.vUnit)
          ])).tag;
        expected = "lift-elim";
      };
      "quote-ne-lift-elim-l-zero-fastpath" = {
        expr = (quote 1 (V.vNe 0
          [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              V.vUnit)
          ])).l.tag;
        expected = "level-zero";
      };
      # nf round-trip on a stuck lower spine — the term that goes in
      # comes back syntactically equal after eval-then-quote.
      "nf-lift-elim-stuck-roundtrip" = {
        expr =
          let
            tm = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              (T.mkVar 0);
            env = [ (V.freshVar 0) ];
          in
          nf env (nf env tm) == nf env tm;
        expected = true;
      };
      # nf collapses idempotent Lift (`Lift l l _ A` → `A`); the
      # resulting term tag is `unit`, not `lift`.
      "nf-lift-idempotent-collapse" = {
        expr = (nf [ ] (T.mkLift T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit)).tag;
        expected = "unit";
      };
      # nf round-trip on a non-collapsed Lift type — `Lift 0 1 _ Unit`
      # survives eval+quote unchanged.
      "nf-lift-distinct-roundtrip" = {
        expr =
          let
            tm = T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit;
          in
          (nf [ ] tm).tag;
        expected = "lift";
      };

      # Roundtrip: eval then quote for desc-pi
      "nf-desc-pi" = {
        expr = (nf [ ] encPi).tag;
        expected = "desc-con";
      };
      "nf-desc-pi-roundtrip" = {
        expr = nf [ ] (nf [ ] encPi) == nf [ ] encPi;
        expected = true;
      };

      # -- Binders (Pi, Lam, Sigma) --
      "quote-pi" = {
        # Π(x:Unit).Unit — closure body is just Unit (no variable reference)
        expr = (quote 0 (vPi "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
        expected = "pi";
      };
      "quote-lam-identity" = {
        # λ(x:Unit).x — closure body is Var(0)
        expr = let r = quote 0 (vLam "x" vUnit (mkClosure [ ] (T.mkVar 0))); in r.body.tag;
        expected = "var";
      };
      "quote-lam-identity-idx" = {
        # The body Var(0) should quote to index 0
        expr = let r = quote 0 (vLam "x" vUnit (mkClosure [ ] (T.mkVar 0))); in r.body.idx;
        expected = 0;
      };
      "quote-sigma" = {
        expr = (quote 0 (vSigma "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
        expected = "sigma";
      };

      # -- Roundtrip: eval then quote --
      "nf-tt" = { expr = (nf [ ] T.mkTt).tag; expected = "tt"; };
      "nf-app-id" = {
        # nf([], (λx.x) tt) = tt
        expr = (nf [ ] (T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt)).tag;
        expected = "tt";
      };
      "nf-let" = {
        # nf([], let x:Unit=tt in x) = tt
        expr = (nf [ ] (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0))).tag;
        expected = "tt";
      };
      "nf-fst-pair" = {
        expr = (nf [ ] (T.mkFst (T.mkPair T.mkTt T.mkTt))).tag;
        expected = "tt";
      };

      # -- nf as a semantic-equivalence check --
      # `nf [] a == nf [] b` (Nix structural ==) is used as an
      # α-equivalence check across let-unfolding and β-reduction. The
      # four tests below pin the properties it relies on:
      #   1. `let` bindings normalize away (value substituted into body).
      #   2. Fully-applied λs β-reduce.
      #   3. Distinct terms produce distinct nf forms.
      # Regressing any of these silently breaks every caller that uses
      # `nf []` for term equivalence, so they are exercised here at the
      # primitive level rather than being inferred from downstream tests.

      "nf-gate-equal-let-transparent" = {
        # let x:String = "a" in x  ==nf==  "a"
        expr = nf [ ] (T.mkLet "x" T.mkString (T.mkStringLit "a") (T.mkVar 0))
          == nf [ ] (T.mkStringLit "a");
        expected = true;
      };
      "nf-gate-equal-beta-matches-let" = {
        # (λx:String. λy:String. y) "a" "b"  ==nf==  let x:String="a" in let y:String="b" in y
        # Nested β-redex chain and nested let scaffold converge on the
        # same nf form. Both reduce to `"b"`.
        expr = nf [ ]
          (T.mkApp
            (T.mkApp
              (T.mkLam "x" T.mkString
                (T.mkLam "y" T.mkString (T.mkVar 0)))
              (T.mkStringLit "a"))
            (T.mkStringLit "b"))
        == nf [ ] (T.mkLet "x" T.mkString (T.mkStringLit "a")
          (T.mkLet "y" T.mkString (T.mkStringLit "b") (T.mkVar 0)));
        expected = true;
      };
      "nf-gate-unequal-different-values" = {
        # let x:String = "a" in x  -- nf = "a"
        # let x:String = "b" in x  -- nf = "b"
        # Guards against nf-equality collapsing under let-normalization.
        expr = nf [ ] (T.mkLet "x" T.mkString (T.mkStringLit "a") (T.mkVar 0))
          == nf [ ] (T.mkLet "x" T.mkString (T.mkStringLit "b") (T.mkVar 0));
        expected = false;
      };
      "nf-gate-unequal-distinct-after-beta" = {
        # (λf:String→String. f "a") (λx:String. x)   -- β → "a"
        # (λf:String→String. f "a") (λx:String. "b") -- β → "b"
        # Higher-order: two applications differing only in the function
        # argument must nf to distinct forms once β fires.
        expr =
          let
            applyAtA = g: T.mkApp
              (T.mkLam "f" (T.mkPi "_" T.mkString T.mkString)
                (T.mkApp (T.mkVar 0) (T.mkStringLit "a")))
              g;
            identityString = T.mkLam "x" T.mkString (T.mkVar 0);
            constantB = T.mkLam "x" T.mkString (T.mkStringLit "b");
          in
          nf [ ] (applyAtA identityString)
          == nf [ ] (applyAtA constantB);
        expected = false;
      };

      # Stress tests — stack safety
      # Exercises the VDescCon trampoline on a 5000-deep plus-encoded list cons
      # chain. Outer D is generated listDesc whose B summand matches linearProfile [{S=Nat}];
      # each layer's payload is VBootInr L R (VPair head (VPair rec VBootRefl)). The
      # placeholder left/right type args only need to roundtrip structurally —
      # soundness is covered by the eval/check desc-con trampoline tests.
      "quote-descCon-5000" = {
        expr =
          let
            unit = V.vUnit;
            tt = V.vTt;
            listDescVal = E.eval [ ] (H.elab (H.listDesc H.nat));
            leftTy = V.vBootEq unit tt tt;
            rightTy = V.vU V.vLevelZero;
            zeroVal = E.eval [ ] (H.elab H.zero);
            nilLayer = V.vDescCon listDescVal tt
              (V.vBootInl leftTy rightTy V.vBootRefl);
            consLayer = head_: tail_:
              V.vDescCon listDescVal tt
                (V.vBootInr leftTy rightTy
                  (V.vPair head_ (V.vPair tail_ V.vBootRefl)));
            deep = builtins.foldl'
              (acc: _: consLayer zeroVal acc)
              nilLayer
              (builtins.genList (x: x) 5000);
          in
          (quote 0 deep).tag;
        expected = "desc-con-chain";
      };

      # -- C5: Under-binder quotation --

      # Quote a neutral at depth > 0: VNe(0, []) at depth 2 → Var(1)
      "quote-under-binder-var" = {
        expr = (quote 2 (V.vNe 0 [ ])).idx;
        expected = 1;
      };

      # Roundtrip with non-empty env: eval([freshVar(0)], Var(0)) → VNe(0,[]) → Var(0)
      "nf-under-binder" = {
        expr =
          let env1 = [ (V.freshVar 0) ];
          in (nf env1 (T.mkVar 0)).tag;
        expected = "var";
      };
      "nf-under-binder-idx" = {
        expr =
          let env1 = [ (V.freshVar 0) ];
          in (nf env1 (T.mkVar 0)).idx;
        expected = 0;
      };

      # Roundtrip idempotency with non-empty env
      "nf-under-binder-roundtrip" = {
        expr =
          let env1 = [ (V.freshVar 0) ];
          in nf env1 (nf env1 (T.mkFst (T.mkPair (T.mkVar 0) T.mkTt)))
            == nf env1 (T.mkFst (T.mkPair (T.mkVar 0) T.mkTt));
        expected = true;
      };

      # `_canonRef` short-circuit: a tagged VDescCon round-trips via the
      # `mkDescDescAppAt` Tm carrying canonical `[iLev, I, L]` parameters.
      # `.D` is never forced, so deeply-nested or cyclic `.D` slots are
      # safe at quote time.
      "quote-descDescApp-tag-emits-desc-desc-app" = {
        expr = (quote 0 (V.vDescConTagged
          vTt
          vTt
          V.vBootRefl
          {
            id = "descDesc";
            params = [ V.vLevelZero V.vUnit V.vLevelZero ];
          })).tag;
        expected = "desc-desc-app";
      };
      "quote-descDescApp-tag-emits-I" = {
        expr = (quote 0 (V.vDescConTagged
          vTt
          vTt
          V.vBootRefl
          {
            id = "descDesc";
            params = [ V.vLevelZero V.vUnit V.vLevelZero ];
          })).I.tag;
        expected = "unit";
      };
      "quote-descDescApp-tag-emits-L" = {
        expr = (quote 0 (V.vDescConTagged
          vTt
          vTt
          V.vBootRefl
          {
            id = "descDesc";
            params = [ V.vLevelZero V.vUnit (V.vLevelSuc V.vLevelZero) ];
          })).L.tag;
        expected = "level-suc";
      };
      "quote-descDescApp-legacy-IL-rejects" = {
        expr = (builtins.tryEval (quote 0 (V.vDescConTagged
          vTt
          vTt
          V.vBootRefl
          { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; }))).success;
        expected = false;
      };
      "quote-descDescApp-cyclic-D-safe" = {
        # The `.D` slot points back at the value itself; the tag check
        # decides quotation without descending. A no-tag value with the
        # same shape would loop on the trampoline's `peel` walk.
        expr =
          let
            cyclic =
              let
                v = {
                  tag = "VDescCon";
                  D = v;
                  i = vTt;
                  d = vTt;
                  _canonRef = {
                    id = "descDesc";
                    params = [ V.vLevelZero V.vUnit V.vLevelZero ];
                  };
                };
              in
              v;
          in
          (quote 0 cyclic).tag;
        expected = "desc-desc-app";
      };
    };

  value = {
    quote = api.leaf {
      value = quote;
      description = "quote: read-back a value `Val` to a term `Tm` at binding `depth` — translates de Bruijn levels to indices via `index = depth - level - 1`. Pure TCB function.";
      signature = "quote : Depth -> Val -> Tm";
    };
    quoteSp = api.leaf {
      value = quoteSp;
      description = "quoteSp: quote a spine of elimination frames applied to a head term — folds left over the spine, calling `quoteElim` at each step.";
      signature = "quoteSp : Depth -> Tm -> Spine -> Tm";
    };
    quoteElim = api.leaf {
      value = quoteElim;
      description = "quoteElim: quote a single elimination frame applied to a head term — dispatches on frame tag, recursively quoting each carried argument.";
      signature = "quoteElim : Depth -> Tm -> Elim -> Tm";
    };
    nf = api.leaf {
      value = nf;
      description = "nf: normalise a term to its canonical form by `eval` then `quote` — useful for testing round-trip idempotency (`nf env (nf env tm) == nf env tm`).";
      signature = "nf : Env -> Tm -> Tm";
    };
    lvl2Ix = api.leaf {
      value = lvl2Ix;
      description = "lvl2Ix: convert a de Bruijn level to an index at binding `depth` — `index = depth - level - 1`; helper exposed for downstream tooling that interleaves with quotation.";
      signature = "lvl2Ix : Depth -> Level -> Index";
    };

  };
}
