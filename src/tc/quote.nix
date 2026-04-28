# Type-checking kernel: Quotation (quote)
#
# quote : Depth -> Val -> Tm
# Converts a value back to a term, converting de Bruijn levels to indices.
# Pure function — zero effect system imports.
#
# Spec reference: kernel-spec.md §5
{ fx, api, ... }:

let
  inherit (api) mk;
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;

  # Cached `U(0)` term sentinel. Quoting a `VU` whose level is the
  # `VLevelZero` singleton reduces to this shared term — no per-call
  # allocation of the `{tag="U"; level={tag="level-zero"}}` pair.
  mkUZero = T.mkU T.mkLevelZero;

  # Level to index conversion: index = depth - level - 1
  lvl2Ix = depth: level: depth - level - 1;

  # Quote a value at binding depth d back to a term.
  quote = d: v:
    let t = v.tag; in
    if t == "VPi" then
      T.mkPi v.name (quote d v.domain)
        (quote (d + 1) (E.instantiate v.closure (V.freshVar d)))
    else if t == "VLam" then
      T.mkLam v.name (quote d v.domain)
        (quote (d + 1) (E.instantiate v.closure (V.freshVar d)))
    else if t == "VSigma" then
      T.mkSigma v.name (quote d v.fst)
        (quote (d + 1) (E.instantiate v.closure (V.freshVar d)))
    else if t == "VPair" then T.mkPair (quote d v.fst) (quote d v.snd)
    else if t == "VNat" then T.mkNat
    else if t == "VZero" then T.mkZero
    # VSucc — trampolined for deep naturals (S^5000+)
    else if t == "VSucc" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = v; }];
          operator = item:
            if item.val.tag == "VSucc"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
      in builtins.foldl' (acc: _: T.mkSucc acc) (quote d base) (builtins.genList (x: x) n)
    else if t == "VList" then T.mkList (quote d v.elem)
    else if t == "VNil" then T.mkNil (quote d v.elem)
    # VCons — trampolined for deep lists (5000+ elements)
    # Note: elemTm is taken from the outermost node and reused for all chain
    # nodes. This is correct for well-typed values (all elem types are identical)
    # but would produce wrong type annotations for ill-typed VCons chains.
    else if t == "VCons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = v; }];
          operator = item:
            if item.val.tag == "VCons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        elemTm = quote d v.elem;
      in builtins.foldl' (acc: i:
        let node = (builtins.elemAt chain (n - 1 - i)).val; in
        T.mkCons elemTm (quote d node.head) acc
      ) (quote d base) (builtins.genList (x: x) n)
    else if t == "VUnit" then T.mkUnit
    else if t == "VTt" then T.mkTt
    else if t == "VSum" then T.mkSum (quote d v.left) (quote d v.right)
    else if t == "VInl" then T.mkInl (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VInr" then T.mkInr (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VEq" then T.mkEq (quote d v.type) (quote d v.lhs) (quote d v.rhs)
    else if t == "VRefl" then T.mkRefl
    else if t == "VFunext" then T.mkFunext
    # Descriptions
    else if t == "VDesc" then
      # Level-zero fast-path: prelude descriptions live at `desc^0`,
      # so emit the cached `T.mkLevelZero` sentinel directly instead
      # of recursively quoting `VLevelZero`.
      if v.level.tag == "VLevelZero"
      then T.mkDesc T.mkLevelZero (quote d v.I)
      else T.mkDesc (quote d v.level) (quote d v.I)
    else if t == "VDescRet" then T.mkDescRet (quote d v.j)
    # Level-zero fast-path at the new `k` slot: when `v.k` is the
    # `VLevelZero` singleton, emit the cached `T.mkLevelZero` sentinel
    # directly — skips a recursive quote descent into the level value.
    else if t == "VDescArg" then
      T.mkDescArg
        (if v.k.tag == "VLevelZero" then T.mkLevelZero else quote d v.k)
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (quote d v.S)
        (quote d v.eq)
        (quote (d + 1) (E.instantiate v.T (V.freshVar d)))
    else if t == "VDescRec" then T.mkDescRec (quote d v.j) (quote d v.D)
    else if t == "VDescPi" then
      T.mkDescPi
        (if v.k.tag == "VLevelZero" then T.mkLevelZero else quote d v.k)
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (quote d v.S) (quote d v.eq) (quote d v.f) (quote d v.D)
    else if t == "VDescPlus" then T.mkDescPlus (quote d v.A) (quote d v.B)
    else if t == "VMu" then T.mkMu (quote d v.I) (quote d v.D) (quote d v.i)
    # VDescCon — trampolined for deep recursive chains (5000+ cons/succ layers).
    # Mirrors the eval/check desc-con trampoline at the quote layer: peels a
    # linear-recursive chain whose outer D = VDescPlus A B and whose "recursive"
    # summand B has linearProfile [{S_1}..{S_n}] (n ≥ 0 data heads then rec tail).
    # Each peeled layer has payload VInr left right (VPair h_1 (...(VPair rec VRefl))).
    # Non-linear shapes (nil leaves, non-plus D, tree recursion) return null and
    # fall through to the single-layer recursive quote at baseTm below.
    else if t == "VDescCon" then
      let
        peel = node:
          if node.tag != "VDescCon" then null
          else if node.D.tag != "VDescPlus" then null
          else if node.d.tag != "VInr" then null
          else
            let
              profile = E.linearProfile node.D.B;
              nFields = if profile == null then 0 else builtins.length profile;
              collect = k: p: acc:
                if k == nFields then
                  if p.tag != "VPair" then null
                  else if p.snd.tag != "VRefl" then null
                  else if p.fst.tag != "VDescCon" then null
                  else { heads = acc; tail = p.fst; }
                else if p.tag != "VPair" then null
                else collect (k + 1) p.snd (acc ++ [ p.fst ]);
            in if profile == null then null
               else collect 0 node.d.val [];
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = v; }];
          operator = item:
            let peeled = peel item.val; in
            if peeled == null then []
            else [{ key = item.key + 1; val = peeled.tail; }];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        baseTm = T.mkDescCon (quote d base.D) (quote d base.i) (quote d base.d);
      in if n == 0 then baseTm
         else
           let
             # All layers share D and the VInr wrapper's left/right type args
             # (they are interp-of-D.{A,B} which depends only on D, shared
             # across layers). Quote once; reuse in the fold.
             outerD   = quote d v.D;
             leftTm   = quote d v.d.left;
             rightTm  = quote d v.d.right;
           in builtins.foldl' (acc: k:
                let
                  layer = (builtins.elemAt chain (n - 1 - k)).val;
                  peeled = peel layer;
                  headTms = map (h: quote d h) peeled.heads;
                  buildInner = hs: tail:
                    if hs == [] then tail
                    else T.mkPair (builtins.head hs)
                                  (buildInner (builtins.tail hs) tail);
                in T.mkDescCon outerD (quote d layer.i)
                     (T.mkInr leftTm rightTm
                       (buildInner headTms (T.mkPair acc T.mkRefl)))
              ) baseTm (builtins.genList (x: x) n)
    # Lift primitive — round-trip type-former and introducer. Level-zero
    # fast-path on `v.l` / `v.m` mirrors the desc-arg / desc-pi shape.
    else if t == "VLift" then
      T.mkLift
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (if v.m.tag == "VLevelZero" then T.mkLevelZero else quote d v.m)
        (quote d v.eq) (quote d v.A)
    else if t == "VLiftIntro" then
      T.mkLiftIntro
        (if v.l.tag == "VLevelZero" then T.mkLevelZero else quote d v.l)
        (if v.m.tag == "VLevelZero" then T.mkLevelZero else quote d v.m)
        (quote d v.eq) (quote d v.A) (quote d v.a)
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
    else if t == "VFunction" then T.mkFunction
    else if t == "VAny" then T.mkAny
    else if t == "VStringLit" then T.mkStringLit v.value
    else if t == "VIntLit" then T.mkIntLit v.value
    else if t == "VFloatLit" then T.mkFloatLit v.value
    else if t == "VAttrsLit" then T.mkAttrsLit
    else if t == "VPathLit" then T.mkPathLit
    else if t == "VFnLit" then T.mkFnLit
    else if t == "VAnyLit" then T.mkAnyLit
    else if t == "VOpaqueLam" then T.mkOpaqueLam v._fnBox (quote d v.piTy)
    else if t == "VNe" then quoteSp d (T.mkVar (lvl2Ix d v.level)) v.spine
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
    else if t == "ENatElim" then
      T.mkNatElim (quote d elim.motive) (quote d elim.base) (quote d elim.step) head
    else if t == "EListElim" then
      T.mkListElim (quote d elim.elem) (quote d elim.motive) (quote d elim.onNil) (quote d elim.onCons) head
    else if t == "ESumElim" then
      T.mkSumElim (quote d elim.left) (quote d elim.right) (quote d elim.motive)
        (quote d elim.onLeft) (quote d elim.onRight) head
    else if t == "EJ" then
      T.mkJ (quote d elim.type) (quote d elim.lhs) (quote d elim.motive)
        (quote d elim.base) (quote d elim.rhs) head
    else if t == "EStrEq" then T.mkStrEq head (quote d elim.arg)
    else if t == "EDescInd" then
      T.mkDescInd (quote d elim.D) (quote d elim.motive) (quote d elim.step) (quote d elim.i) head
    else if t == "EDescElim" then
      T.mkDescElim (quote d elim.k) (quote d elim.motive) (quote d elim.onRet)
        (quote d elim.onArg) (quote d elim.onRec) (quote d elim.onPi)
        (quote d elim.onPlus) head
    # ELiftElim spine frame round-trips to `mkLiftElim l m eq A head`.
    # Level-zero fast-path on `l` / `m` mirrors the in-quote-rule shape.
    else if t == "ELiftElim" then
      T.mkLiftElim
        (if elim.l.tag == "VLevelZero" then T.mkLevelZero else quote d elim.l)
        (if elim.m.tag == "VLevelZero" then T.mkLevelZero else quote d elim.m)
        (quote d elim.eq) (quote d elim.A) head
    else if t == "ENatToLevel" then T.mkNatToLevel head
    else throw "tc: quoteElim unknown tag '${t}'";

  # Normalize: eval then quote
  nf = env: tm: quote (builtins.length env) (E.eval env tm);

in mk {
  doc = ''
    # fx.tc.quote — Quotation (Read-back)

    Converts values back to terms, translating de Bruijn levels to
    indices. Pure function — part of the TCB.

    Spec reference: kernel-spec.md §5.

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

    VSucc and VCons chains are quoted iteratively via `genericClosure`
    for O(1) stack depth on deep values (5000+ elements).

    ## Binder Quotation

    For VPi, VLam, VSigma: instantiates the closure with a fresh
    variable at the current depth, then quotes the body at `depth + 1`.
  '';
  value = { inherit quote quoteSp quoteElim nf lvl2Ix; };
  tests = let
    inherit (V) vNat vZero vSucc vPi vLam vSigma vPair
      vList vNil vCons vUnit vTt vSum vInl vInr vEq vRefl vU vNe
      mkClosure eApp eFst eSnd eNatElim eListElim eSumElim eJ;
  in {
    # -- Level to index --
    "lvl2ix-0" = { expr = lvl2Ix 1 0; expected = 0; };
    "lvl2ix-1" = { expr = lvl2Ix 3 0; expected = 2; };
    "lvl2ix-2" = { expr = lvl2Ix 3 2; expected = 0; };

    # -- Simple values --
    "quote-nat" = { expr = (quote 0 vNat).tag; expected = "nat"; };
    "quote-zero" = { expr = (quote 0 vZero).tag; expected = "zero"; };
    "quote-succ" = { expr = (quote 0 (vSucc vZero)).tag; expected = "succ"; };
    "quote-unit" = { expr = (quote 0 vUnit).tag; expected = "unit"; };
    "quote-tt" = { expr = (quote 0 vTt).tag; expected = "tt"; };
    "quote-refl" = { expr = (quote 0 vRefl).tag; expected = "refl"; };
    "quote-funext" = { expr = (quote 0 V.vFunext).tag; expected = "funext"; };
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
    "quote-function" = { expr = (quote 0 V.vFunction).tag; expected = "function"; };
    "quote-any" = { expr = (quote 0 V.vAny).tag; expected = "any"; };
    "quote-string-lit" = { expr = (quote 0 (V.vStringLit "hi")).tag; expected = "string-lit"; };
    "quote-string-lit-value" = { expr = (quote 0 (V.vStringLit "hi")).value; expected = "hi"; };
    "quote-int-lit" = { expr = (quote 0 (V.vIntLit 7)).tag; expected = "int-lit"; };
    "quote-int-lit-value" = { expr = (quote 0 (V.vIntLit 7)).value; expected = 7; };
    "quote-float-lit" = { expr = (quote 0 (V.vFloatLit 1.5)).tag; expected = "float-lit"; };
    "quote-attrs-lit" = { expr = (quote 0 V.vAttrsLit).tag; expected = "attrs-lit"; };
    "quote-path-lit" = { expr = (quote 0 V.vPathLit).tag; expected = "path-lit"; };
    "quote-fn-lit" = { expr = (quote 0 V.vFnLit).tag; expected = "fn-lit"; };
    "quote-any-lit" = { expr = (quote 0 V.vAnyLit).tag; expected = "any-lit"; };

    # -- Compound values --
    "quote-pair" = { expr = (quote 0 (vPair vZero vTt)).tag; expected = "pair"; };
    "quote-list" = { expr = (quote 0 (vList vNat)).tag; expected = "list"; };
    "quote-nil" = { expr = (quote 0 (vNil vNat)).tag; expected = "nil"; };
    "quote-cons" = { expr = (quote 0 (vCons vNat vZero (vNil vNat))).tag; expected = "cons"; };
    "quote-sum" = { expr = (quote 0 (vSum vNat vUnit)).tag; expected = "sum"; };
    "quote-inl" = { expr = (quote 0 (vInl vNat vUnit vZero)).tag; expected = "inl"; };
    "quote-inr" = { expr = (quote 0 (vInr vNat vUnit vTt)).tag; expected = "inr"; };
    "quote-eq" = { expr = (quote 0 (vEq vNat vZero vZero)).tag; expected = "eq"; };

    # -- Neutrals --
    "quote-var" = {
      # Neutral at level 0, depth 1 → index 0
      expr = (quote 1 (vNe 0 [])).tag;
      expected = "var";
    };
    "quote-var-idx" = {
      expr = (quote 1 (vNe 0 [])).idx;
      expected = 0;
    };
    "quote-var-deep" = {
      # Neutral at level 0, depth 3 → index 2
      expr = (quote 3 (vNe 0 [])).idx;
      expected = 2;
    };
    "quote-ne-app" = {
      # x applied to 0: VNe(0, [EApp VZero]) at depth 1 → App(Var(0), Zero)
      expr = (quote 1 (vNe 0 [ (eApp vZero) ])).tag;
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
    "quote-ne-nat-elim" = {
      expr = (quote 1 (vNe 0 [ (eNatElim vNat vZero vZero) ])).tag;
      expected = "nat-elim";
    };
    "quote-ne-list-elim" = {
      expr = (quote 1 (vNe 0 [ (eListElim vNat vNat vZero vZero) ])).tag;
      expected = "list-elim";
    };
    "quote-ne-sum-elim" = {
      expr = (quote 1 (vNe 0 [ (eSumElim vNat vUnit vNat vZero vZero) ])).tag;
      expected = "sum-elim";
    };
    "quote-ne-j" = {
      expr = (quote 1 (vNe 0 [ (eJ vNat vZero vNat vZero vZero) ])).tag;
      expected = "j";
    };

    # -- Descriptions (indexed) --
    "quote-desc" = { expr = (quote 0 (V.vDesc V.vLevelZero V.vUnit)).tag; expected = "desc"; };
    "quote-desc-ret" = { expr = (quote 0 (V.vDescRet V.vTt)).tag; expected = "desc-ret"; };
    "quote-desc-arg" = {
      expr = (quote 0 (V.vDescArg V.vLevelZero V.vLevelZero V.vNat V.vRefl (V.mkClosure [] (T.mkDescRet T.mkTt)))).tag;
      expected = "desc-arg";
    };
    "quote-desc-arg-k-zero-fastpath" = {
      expr = (quote 0 (V.vDescArg V.vLevelZero V.vLevelZero V.vNat V.vRefl (V.mkClosure [] (T.mkDescRet T.mkTt)))).k.tag;
      expected = "level-zero";
    };
    "quote-desc-rec" = {
      expr = (quote 0 (V.vDescRec V.vTt (V.vDescRet V.vTt))).tag;
      expected = "desc-rec";
    };
    "quote-desc-pi" = {
      expr = let f = V.vLam "_" V.vNat (V.mkClosure [] T.mkTt); in
        (quote 0 (V.vDescPi V.vLevelZero V.vLevelZero V.vNat V.vRefl f (V.vDescRet V.vTt))).tag;
      expected = "desc-pi";
    };
    "quote-desc-pi-S" = {
      expr = let f = V.vLam "_" V.vNat (V.mkClosure [] T.mkTt); in
        (quote 0 (V.vDescPi V.vLevelZero V.vLevelZero V.vNat V.vRefl f (V.vDescRet V.vTt))).S.tag;
      expected = "nat";
    };
    "quote-desc-pi-D" = {
      expr = let f = V.vLam "_" V.vNat (V.mkClosure [] T.mkTt); in
        (quote 0 (V.vDescPi V.vLevelZero V.vLevelZero V.vNat V.vRefl f (V.vDescRet V.vTt))).D.tag;
      expected = "desc-ret";
    };
    "quote-desc-pi-k-zero-fastpath" = {
      expr = let f = V.vLam "_" V.vNat (V.mkClosure [] T.mkTt); in
        (quote 0 (V.vDescPi V.vLevelZero V.vLevelZero V.vNat V.vRefl f (V.vDescRet V.vTt))).k.tag;
      expected = "level-zero";
    };
    "quote-mu" = {
      expr = (quote 0 (V.vMu V.vUnit (V.vDescRet V.vTt) V.vTt)).tag;
      expected = "mu";
    };
    "quote-desc-con" = {
      expr = (quote 0 (V.vDescCon (V.vDescRet V.vTt) V.vTt V.vRefl)).tag;
      expected = "desc-con";
    };
    "quote-ne-desc-ind" = {
      expr = (quote 1 (V.vNe 0 [ (V.eDescInd (V.vDescRet V.vTt) V.vNat V.vZero V.vTt) ])).tag;
      expected = "desc-ind";
    };
    "quote-ne-desc-elim" = {
      expr = (quote 1 (V.vNe 0 [ (V.eDescElim V.vLevelZero V.vNat V.vZero V.vZero V.vZero V.vZero V.vZero) ])).tag;
      expected = "desc-elim";
    };

    # Lift primitive — type-former, introducer, and stuck-eliminator
    # spine frame. Tests use level-zero throughout for the fast-path
    # singleton; `l ≠ m` cases test the non-collapsed shape.
    "quote-lift-distinct-levels" = {
      expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
        V.vRefl V.vUnit)).tag;
      expected = "lift";
    };
    "quote-lift-l-zero-fastpath" = {
      expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
        V.vRefl V.vUnit)).l.tag;
      expected = "level-zero";
    };
    "quote-lift-A" = {
      expr = (quote 0 (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero)
        V.vRefl V.vUnit)).A.tag;
      expected = "unit";
    };
    "quote-lift-intro-distinct-levels" = {
      expr = (quote 0 (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
        V.vRefl V.vUnit V.vTt)).tag;
      expected = "lift-intro";
    };
    "quote-lift-intro-a" = {
      expr = (quote 0 (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
        V.vRefl V.vUnit V.vTt)).a.tag;
      expected = "tt";
    };
    "quote-ne-lift-elim" = {
      # Stuck `lower` on a neutral: VNe(0, [ELiftElim …]) round-trips
      # to `mkLiftElim l m eq A (Var 0)`.
      expr = (quote 1 (V.vNe 0
        [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
            V.vRefl V.vUnit) ])).tag;
      expected = "lift-elim";
    };
    "quote-ne-lift-elim-l-zero-fastpath" = {
      expr = (quote 1 (V.vNe 0
        [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
            V.vRefl V.vUnit) ])).l.tag;
      expected = "level-zero";
    };
    # nf round-trip on a stuck lower spine — the term that goes in
    # comes back syntactically equal after eval-then-quote.
    "nf-lift-elim-stuck-roundtrip" = {
      expr = let
        tm = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit (T.mkVar 0);
        env = [ (V.freshVar 0) ];
      in nf env (nf env tm) == nf env tm;
      expected = true;
    };
    # nf collapses idempotent Lift (`Lift l l _ A` → `A`); the
    # resulting term tag is `unit`, not `lift`.
    "nf-lift-idempotent-collapse" = {
      expr = (nf [] (T.mkLift T.mkLevelZero T.mkLevelZero T.mkRefl T.mkUnit)).tag;
      expected = "unit";
    };
    # nf round-trip on a non-collapsed Lift type — `Lift 0 1 _ Unit`
    # survives eval+quote unchanged.
    "nf-lift-distinct-roundtrip" = {
      expr = let
        tm = T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit;
      in (nf [] tm).tag;
      expected = "lift";
    };

    # natToLevel reduces structurally on closed Nats — nf produces
    # `level-zero` / chained `level-suc` (no surviving `nat-to-level`).
    "nf-nat-to-level-zero" = {
      expr = (nf [] (T.mkNatToLevel T.mkZero)).tag;
      expected = "level-zero";
    };
    "nf-nat-to-level-suc-chain" = {
      expr = (nf [] (T.mkNatToLevel
        (T.mkSucc (T.mkSucc T.mkZero)))).pred.pred.tag;
      expected = "level-zero";
    };
    "quote-ne-nat-to-level" = {
      # Stuck `natToLevel` on a Nat-typed neutral round-trips.
      expr = (quote 1 (V.vNe 0 [ V.eNatToLevel ])).tag;
      expected = "nat-to-level";
    };
    "nf-nat-to-level-stuck-roundtrip" = {
      expr = let
        tm = T.mkNatToLevel (T.mkVar 0);
        env = [ (V.freshVar 0) ];
      in nf env (nf env tm) == nf env tm;
      expected = true;
    };

    # Roundtrip: eval then quote for desc-pi
    "nf-desc-pi" = {
      expr = (nf [] (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt))).tag;
      expected = "desc-pi";
    };
    "nf-desc-pi-roundtrip" = {
      expr = let D = T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt); in
        nf [] (nf [] D) == nf [] D;
      expected = true;
    };

    # -- Binders (Pi, Lam, Sigma) --
    "quote-pi" = {
      # Π(x:Nat).Nat — closure body is just Nat (no variable reference)
      expr = (quote 0 (vPi "x" vNat (mkClosure [] T.mkNat))).tag;
      expected = "pi";
    };
    "quote-lam-identity" = {
      # λ(x:Nat).x — closure body is Var(0)
      expr = let r = quote 0 (vLam "x" vNat (mkClosure [] (T.mkVar 0))); in r.body.tag;
      expected = "var";
    };
    "quote-lam-identity-idx" = {
      # The body Var(0) should quote to index 0
      expr = let r = quote 0 (vLam "x" vNat (mkClosure [] (T.mkVar 0))); in r.body.idx;
      expected = 0;
    };
    "quote-sigma" = {
      expr = (quote 0 (vSigma "x" vNat (mkClosure [] T.mkUnit))).tag;
      expected = "sigma";
    };

    # -- Roundtrip: eval then quote --
    "nf-zero" = { expr = (nf [] T.mkZero).tag; expected = "zero"; };
    "nf-succ-zero" = { expr = (nf [] (T.mkSucc T.mkZero)).pred.tag; expected = "zero"; };
    "nf-app-id" = {
      # nf([], (λx.x) 0) = 0
      expr = (nf [] (T.mkApp (T.mkLam "x" T.mkNat (T.mkVar 0)) T.mkZero)).tag;
      expected = "zero";
    };
    "nf-let" = {
      # nf([], let x:Nat=0 in x) = 0
      expr = (nf [] (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0))).tag;
      expected = "zero";
    };
    "nf-fst-pair" = {
      expr = (nf [] (T.mkFst (T.mkPair T.mkZero T.mkTt))).tag;
      expected = "zero";
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
      # let x:Nat = zero in succ x  ==nf==  succ zero
      expr = nf [] (T.mkLet "x" T.mkNat T.mkZero (T.mkSucc (T.mkVar 0)))
          == nf [] (T.mkSucc T.mkZero);
      expected = true;
    };
    "nf-gate-equal-beta-matches-let" = {
      # (λT:U0. λn:Nat. n) Nat zero  ==nf==  let T:U0=Nat in let n:Nat=zero in n
      # Nested β-redex chain and nested let scaffold converge on the
      # same nf form. Both reduce to `zero`.
      expr = nf [] (T.mkApp
                      (T.mkApp (T.mkLam "T" (T.mkU T.mkLevelZero)
                                (T.mkLam "n" T.mkNat (T.mkVar 0)))
                               T.mkNat)
                      T.mkZero)
          == nf [] (T.mkLet "T" (T.mkU T.mkLevelZero) T.mkNat
                      (T.mkLet "n" T.mkNat T.mkZero (T.mkVar 0)));
      expected = true;
    };
    "nf-gate-unequal-different-values" = {
      # let x:Nat = zero in succ x         -- nf = succ zero
      # let x:Nat = zero in succ (succ x)  -- nf = succ (succ zero)
      # Guards against nf-equality collapsing under let-normalization.
      expr = nf [] (T.mkLet "x" T.mkNat T.mkZero (T.mkSucc (T.mkVar 0)))
          == nf [] (T.mkLet "x" T.mkNat T.mkZero
                      (T.mkSucc (T.mkSucc (T.mkVar 0))));
      expected = false;
    };
    "nf-gate-unequal-distinct-after-beta" = {
      # (λf:Nat→Nat. f zero) (λx:Nat. x)        -- β → zero
      # (λf:Nat→Nat. f zero) (λx:Nat. succ x)   -- β → succ zero
      # Higher-order: two applications differing only in the function
      # argument must nf to distinct forms once β fires.
      expr = let
        applyAtZero = g: T.mkApp
          (T.mkLam "f" (T.mkPi "_" T.mkNat T.mkNat)
            (T.mkApp (T.mkVar 0) T.mkZero))
          g;
        identityNat = T.mkLam "x" T.mkNat (T.mkVar 0);
        succFn      = T.mkLam "x" T.mkNat (T.mkSucc (T.mkVar 0));
      in nf [] (applyAtZero identityNat)
      == nf [] (applyAtZero succFn);
      expected = false;
    };

    # Stress tests — stack safety
    "quote-cons-5000" = {
      expr = let
        deep = builtins.foldl' (acc: _: V.vCons V.vNat V.vZero acc) (V.vNil V.vNat) (builtins.genList (x: x) 5000);
      in (quote 0 deep).tag;
      expected = "cons";
    };
    "quote-succ-5000" = {
      expr = let
        deep = builtins.foldl' (acc: _: V.vSucc acc) V.vZero (builtins.genList (x: x) 5000);
      in (quote 0 deep).tag;
      expected = "succ";
    };
    # Exercises the VDescCon trampoline on a 5000-deep plus-encoded list cons
    # chain. Outer D is VDescPlus whose B summand matches linearProfile [{S=Nat}];
    # each layer's payload is VInr L R (VPair head (VPair rec VRefl)). The
    # placeholder left/right type args only need to roundtrip structurally —
    # soundness is covered by the eval/check desc-con trampoline tests.
    "quote-descCon-5000" = {
      expr = let
        unit = V.vUnit;
        tt = V.vTt;
        listDescVal = V.vDescPlus
          (V.vDescRet tt)
          (V.vDescArg V.vLevelZero V.vLevelZero V.vNat V.vRefl
            (V.mkClosure [ ] (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))));
        leftTy  = V.vEq unit tt tt;
        rightTy = V.vU V.vLevelZero;
        nilLayer = V.vDescCon listDescVal tt
          (V.vInl leftTy rightTy V.vRefl);
        consLayer = head_: tail_:
          V.vDescCon listDescVal tt
            (V.vInr leftTy rightTy
              (V.vPair head_ (V.vPair tail_ V.vRefl)));
        deep = builtins.foldl'
          (acc: _: consLayer V.vZero acc)
          nilLayer
          (builtins.genList (x: x) 5000);
      in (quote 0 deep).tag;
      expected = "desc-con";
    };

    # -- C5: Under-binder quotation --

    # Quote a neutral at depth > 0: VNe(0, []) at depth 2 → Var(1)
    "quote-under-binder-var" = {
      expr = (quote 2 (V.vNe 0 [])).idx;
      expected = 1;
    };

    # Roundtrip with non-empty env: eval([freshVar(0)], Var(0)) → VNe(0,[]) → Var(0)
    "nf-under-binder" = {
      expr = let env1 = [ (V.freshVar 0) ];
      in (nf env1 (T.mkVar 0)).tag;
      expected = "var";
    };
    "nf-under-binder-idx" = {
      expr = let env1 = [ (V.freshVar 0) ];
      in (nf env1 (T.mkVar 0)).idx;
      expected = 0;
    };

    # Roundtrip idempotency with non-empty env
    "nf-under-binder-roundtrip" = {
      expr = let env1 = [ (V.freshVar 0) ];
      in nf env1 (nf env1 (T.mkSucc (T.mkVar 0))) == nf env1 (T.mkSucc (T.mkVar 0));
      expected = true;
    };
  };
}
