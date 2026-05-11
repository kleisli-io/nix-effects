# HOAS → Tm elaboration. `elaborate : Int → HoasTree → Tm` walks the
# intermediate HOAS tree built by the combinators / macro layer and emits
# de Bruijn indexed kernel terms. Binding chains (pi/sigma/lam/let), succ
# chains, and cons chains trampoline via `genericClosure` for stack safety
# to 8000+ depth. Macro-constructor applications route through
# `tryFlattenCtorChain` before the regular `app` case, collapsing
# saturated `dt-ctor-mono` / `dt-ctor-poly` spines into flat `desc-con`
# Tms.
#
# Also provides `checkHoas` / `inferHoas` wrappers around the kernel
# checker and the `natLit` helper for building S^n(zero).
{ self, fx, ... }:

let
  T = fx.tc.term;
  E = fx.tc.eval;
  CH = fx.tc.check;
  CHD = fx.tc.check.diag;

  # List helpers — inline `take`/`drop` so this module does not need to
  # pull in nixpkgs `lib`.
  _listTake = n: xs:
    builtins.genList (i: builtins.elemAt xs i)
      (if n > builtins.length xs then builtins.length xs else n);
  _listDrop = n: xs:
    let len = builtins.length xs; in
    if n >= len then []
    else builtins.genList (i: builtins.elemAt xs (n + i)) (len - n);

  # Peel an app-spine: walk outward while the node is an HOAS `app`,
  # returning `{ head; args = [arg_inner, ..., arg_outer]; }`. Bounded by
  # the ctor's nParams + nFields per call site (3 for ListDT.cons) — no
  # long recursion.
  peelAppSpine = node: args:
    if builtins.isAttrs node && node ? _htag && node._htag == "app"
    then peelAppSpine node.fn ([ node.arg ] ++ args)
    else { head = node; inherit args; };

  # Tm-level tag encoding via the first-class plus coproduct. Wraps
  # `payloadTm` with (n-1)-deep nested `mkInl L R …` / `mkInr L R …`
  # committing at position i out of n total. Mirrors the HOAS
  # `encodeTag` but operates on elaborated terms. `lTms`/`rTms` are
  # parallel lists of layer-k L/R type Tms — `lTms[k]` = interp of
  # summand k, `rTms[k]` = interp of the plus-tree of summands
  # k+1..n-1. For n=1 there is no prefix. Both lists must have length
  # >= 1 (caller guarantees via `n >= 2`).
  encodeTagTm = lTms: rTms: i: n: payloadTm:
    if n == 1 then payloadTm
    else
      let lTm = builtins.elemAt lTms 0;
          rTm = builtins.elemAt rTms 0;
      in
      if i == 0 then T.mkInl lTm rTm payloadTm
      else T.mkInr lTm rTm
             (encodeTagTm
                (_listDrop 1 lTms) (_listDrop 1 rTms)
                (i - 1) (n - 1) payloadTm);

  # Build per-layer L/R interp Tm lists for a plus-spine of n summands
  # over index type `I`. Given the outer mu's description HOAS
  # `dHoasOuter`, the target index HOAS `targetIdxVal`, and the
  # per-summand HOAS descriptions `descsHoas`, emits
  #   lTms[k] = mkInterpD 0 I (descsHoas[k]) muFam targetIdxVal
  #   rTms[k] = mkInterpD 0 I (spineAfter (k+1)) muFam targetIdxVal  (k in 0..n-2)
  # where `muFam = λi:I. μ I dHoasOuter i`. Used by the datatype-macro
  # flatten path (with `I`/`targetIdxVal` read off the ctor spec) and by
  # the direct scalar paths (zero/succ/nil/cons/inl/inr) which pass
  # `self.unitPrim` / `self.ttPrim` since all kernel scalars are
  # ⊤-indexed. n must be >= 1.
  buildTagInterpTms = depth: I: dHoasOuter: targetIdxVal: descsHoas:
    let
      n = builtins.length descsHoas;
      muFam = self.lam "_i" I (iArg:
        self.muI I dHoasOuter iArg);
      # Plus-spine of summands k..n-1. Requires remaining >= 1.
      spineAfter = k:
        let remaining = n - k; in
        if remaining == 1 then builtins.elemAt descsHoas k
        else self.plusI I 0 (builtins.elemAt descsHoas k) (spineAfter (k + 1));
      interpTm = dHoas:
        elaborate depth
          (self.interpD 0 I dHoas muFam targetIdxVal);
    in {
      lTms = builtins.genList (k: interpTm (builtins.elemAt descsHoas k)) n;
      rTms = builtins.genList (k: interpTm (spineAfter (k + 1)))
               (if n >= 2 then n - 1 else 0);
    };

  # Syntactic retarget of a primitive desc-* Tm tree to the encoded
  # `μ⊤(descDesc I 0) tt` form. Mirrors what the desc-* CHECK rules in
  # `check.nix:241-462` produce per node, but precomputed once at the
  # elaboration of `annTrustedRetargetedDesc` (the kernel-internal
  # annotation used for the macro datatype's `D` at
  # `hoas/datatype.nix:190`).
  #
  # Homogeneous-zero specialisation: every desc-arg / desc-pi inside
  # `spineDesc conDescs` carries `k = l = 0`, `eq = refl` by
  # construction (conDesc emits `descArg 0` / `descPi 0`), so we always
  # emit the homogeneous encoders (`encodeDescArgTm` /
  # `encodeDescPiTm`). `I_q` is the elaborated index Tm, threaded
  # unchanged through every layer because the macro `I` is closed (no
  # `mkVar` references).
  #
  # `desc-arg`'s body Tm arrives at depth + 1 (elaborate's desc-arg
  # branch elaborates `h.body marker` under the marker binder). The
  # encoded encoder takes the body as a `T : S → muTt` lambda, so we
  # wrap the recursively-retargeted body in `mkLam "_" sTm bodyR` —
  # binder count is preserved, mkVar references inside resolve to the
  # same encoded-lam binder as they did to the implicit `desc-arg`
  # binder.
  #
  # Non-canonical Tm tags pass through unchanged. In the
  # `annTrustedRetargetedDesc` use case the walker only sees the five
  # canonical desc-* shapes (conDesc / spineDesc construct nothing
  # else); the fallback is defensive rather than load-bearing.
  retargetSpineDescTm = I_q: tm:
    let t = tm.tag or null; in
    if t == "desc-ret" then
      T.mkApp (T.mkApp (T.mkApp self.encodeDescRetTm I_q) T.mkLevelZero) tm.j
    else if t == "desc-arg" then
      let bodyR = retargetSpineDescTm I_q tm.T;
          tLam = T.mkLam "_" tm.S bodyR;
      in T.mkApp
           (T.mkApp
             (T.mkApp
               (T.mkApp self.encodeDescArgTm I_q)
               T.mkLevelZero)
             tm.S)
           tLam
    else if t == "desc-rec" then
      let dR = retargetSpineDescTm I_q tm.D; in
      T.mkApp
        (T.mkApp
          (T.mkApp
            (T.mkApp self.encodeDescRecTm I_q)
            T.mkLevelZero)
          tm.j)
        dR
    else if t == "desc-pi" then
      let dR = retargetSpineDescTm I_q tm.D; in
      T.mkApp
        (T.mkApp
          (T.mkApp
            (T.mkApp
              (T.mkApp self.encodeDescPiTm I_q)
              T.mkLevelZero)
            tm.S)
          tm.f)
        dR
    else if t == "desc-plus" then
      let aR = retargetSpineDescTm I_q tm.A;
          bR = retargetSpineDescTm I_q tm.B;
      in T.mkApp
           (T.mkApp
             (T.mkApp
               (T.mkApp self.encodeDescPlusTm I_q)
               T.mkLevelZero)
             aR)
           bR
    else tm;

  # Classify a field list into a chain-flatten profile, or null if
  # neither shape applies.
  #   - "saturated": all fields are plain data (no rec). Emits a single
  #     flat `desc-con` whose payload is the right-nested pair of the
  #     data field Tms terminated with `tt`. No chain-walking.
  #   - "recursive": exactly one rec at the tail, every other field data.
  #     Walks a chain along the rec arg via `genericClosure` and emits a
  #     layered `desc-con` pyramid with a shared dTm across layers.
  # A trailing-rec ctor with zero data fields (e.g. `succ`, whose single
  # field is `rec`) is classified as "recursive" with `nData = 0`. A ctor
  # with zero fields is handled separately at the `tryFlattenCtorChain`
  # poly-branch via the `mono._htag == "desc-con"` short-circuit; both
  # profiles require `n >= 1` here.
  ctorShape = fields:
    let
      n = builtins.length fields;
      initsAllData = nInits:
        builtins.foldl'
          (ok: j: ok && (builtins.elemAt fields j).kind == "data")
          true
          (builtins.genList (x: x) nInits);
      allData = n >= 1 && initsAllData n;
      lastRec =
        n >= 1
        && (builtins.elemAt fields (n - 1)).kind == "recAt"
        && initsAllData (n - 1);
    in
      if lastRec then { kind = "recursive"; }
      else if allData then { kind = "saturated"; }
      else null;

  # Macro-constructor chain flattening.
  #
  # The datatype macro emits fielded constructor terms as curried
  # λ-cascades wrapped in `ann`. A deeply-applied chain (e.g. a
  # 5000-element cons list) would elaborate to a 5000-deep `app`-tree Tm,
  # which blows the C++ stack on `infer`'s linear recursion.
  # `tryFlattenCtorChain` peels spines whose head is tagged
  # `dt-ctor-mono` or `dt-ctor-poly` and emits a flat `desc-con` Tm — a
  # single layer for non-recursive ctors (sum's `inl`/`inr`), a
  # `genericClosure`-walked pyramid for the list/nat-style `recursive`
  # shape.
  #
  # Chain-flatten precondition: one of two shapes per `ctorShape`:
  #   - "saturated": every field is `data`. Emits one flat `desc-con`.
  #   - "recursive": exactly one `rec` at the tail, every other field
  #     `data`. Aligns with the kernel's desc-con trampoline acceptance
  #     condition via `linearProfile`. Walks the chain along the rec tail.
  # Zero-field constructors never produce a `dt-ctor-mono` node — mkCtor
  # returns a plain `desc-con` HOAS with the tag-encoded payload baked
  # in. The poly-branch of `tryFlattenCtorChain` elaborates that mono
  # directly. Ctors outside either shape (tree's `node` with two recs,
  # dataD/piD-dependent fields) decline and the fallback
  # `ann (lam-cascade)` path handles the application normally.
  tryFlattenCtorChain = depth: h:
    let
      outer = peelAppSpine h [];
      head = outer.head;
      args = outer.args;
    in
      if !(builtins.isAttrs head && head ? _htag) then null
      else if head._htag == "dt-ctor-mono" then
        flattenCtor depth head null [] args
      else if head._htag == "dt-ctor-poly" then
        let nP = head.nParams; in
        if builtins.length args < nP then null
        else
          let
            paramArgs = _listTake nP args;
            fieldArgs = _listDrop nP args;
            mono = head.monoAt paramArgs;
          in
            if !(builtins.isAttrs mono) || !(mono ? _htag) then null
            # Fielded ctors: mono is a `dt-ctor-mono` node; pass to the
            # shape-classified flattener.
            else if mono._htag == "dt-ctor-mono"
            then flattenCtor depth mono head paramArgs fieldArgs
            # Zero-field ctors: `mkCtor` returns a plain `desc-con` HOAS
            # (no lam cascade, no tag). Elaborating it directly yields a
            # flat `desc-con` Tm with the parameter-instantiated D baked
            # in.
            else if mono._htag == "desc-con"
                 && builtins.length fieldArgs == 0
            then elaborate depth mono
            else null
      else null;

  # Chain-flatten dispatcher. `polyHead` is non-null for poly chains
  # (used in the recursive branch to verify each successor layer uses
  # the *same* poly ctor with the *same* param args; structural `==` on
  # HOAS param args suffices because the test site passes the same
  # references at every layer).
  flattenCtor = depth: mono: polyHead: paramArgs: fieldArgs:
    let
      nFields = mono.nFields;
      shape = ctorShape mono.fields;
    in
    if builtins.length fieldArgs != nFields || shape == null then null
    else let
      dTm = elaborate depth mono.dHoas;
      ctorIdx = mono.ctorIndex;
      nCtors = mono.nCtors;
      I = mono.I;
      # Rebuild the `prev` attrset required by `mono.targetIdx` from an
      # ordered list of HOAS field-arg nodes. Positions line up with
      # `mono.fields`; only data/dataD entries contribute. Under the
      # ctorShape precondition, `data` fields populate every position
      # used to compute targetIdx (the ⊤-sugar and `datatypeI`'s
      # targetIdx function close only over data-level markers).
      prevOfArgs = args:
        builtins.foldl' (acc: idx:
          let f = builtins.elemAt mono.fields idx; in
          if f.kind == "data" || f.kind == "dataD"
          then acc // { ${f.name} = builtins.elemAt args idx; }
          else acc) {} (builtins.genList (x: x) (builtins.length args));
      # Under the ⊤-sugar path (`datatype` / `datatypeP`), every
      # `targetIdx` is `_: ttPrim` regardless of `prev`, so the tags
      # are invariant across chain layers and can be shared. Detect
      # that case via `I`'s HOAS tag and precompute once; at I ≠ ⊤,
      # tags depend on each layer's `targetIdx prev` and are
      # recomputed per layer.
      isUnitI = (I._htag or null) == "unit";
      sharedTags =
        if isUnitI && nCtors >= 2
        then buildTagInterpTms depth I mono.dHoas self.ttPrim mono.conDescs
        else null;
      mkTags = targetIdxHoas:
        if sharedTags != null then sharedTags
        else if nCtors >= 2
        then buildTagInterpTms depth I mono.dHoas targetIdxHoas mono.conDescs
        else { lTms = []; rTms = []; };
    in
    if shape.kind == "saturated" then
      # No recursion: build one payload from the data field Tms.
      #   descCon dTm tIdx (encodeTag i n (pair d_0 (pair d_1 (… (pair d_{n-1} refl) …))))
      # The innermost payload component inhabits `Eq I j i` at the
      # ret-leaf with `j = targetIdx prev`; refl witnesses it.
      let
        dataTms = map (a: elaborate depth a) fieldArgs;
        prev = prevOfArgs fieldArgs;
        targetIdxHoas = mono.targetIdx prev;
        targetIdxTm = elaborate depth targetIdxHoas;
        tags = mkTags targetIdxHoas;
        payload = builtins.foldl'
          (acc: j:
            let d = builtins.elemAt dataTms (nFields - 1 - j);
            in T.mkPair d acc)
          T.mkRefl
          (builtins.genList (x: x) nFields);
      in T.mkDescCon dTm targetIdxTm
           (encodeTagTm tags.lTms tags.rTms ctorIdx nCtors payload)
    else
      let
        recArg = builtins.elemAt fieldArgs (nFields - 1);
        nonRecArgs = _listTake (nFields - 1) fieldArgs;
        # Try to recognise a successor layer: peel an app spine and
        # require the head to be the same `mono` (mono chains) or the
        # same `polyHead` with matching paramArgs (poly chains).
        tryNext = node:
          let sp = peelAppSpine node []; in
          if !(builtins.isAttrs sp.head && sp.head ? _htag) then null
          else if polyHead == null then
            if sp.head != mono then null
            else if builtins.length sp.args != nFields then null
            else {
              nonRec = _listTake (nFields - 1) sp.args;
              recArg = builtins.elemAt sp.args (nFields - 1);
            }
          else
            if sp.head != polyHead then null
            else if builtins.length sp.args != polyHead.nParams + nFields then null
            else
              let pa = _listTake polyHead.nParams sp.args;
                  fa = _listDrop polyHead.nParams sp.args; in
              if pa != paramArgs then null
              else {
                nonRec = _listTake (nFields - 1) fa;
                recArg = builtins.elemAt fa (nFields - 1);
              };
        # Start the chain at the given layer. `genericClosure` walks
        # along `recArg` as long as each tail peels to a matching
        # successor.
        startLayer = { inherit nonRecArgs recArg; };
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = startLayer; }];
          operator = item:
            let nxt = tryNext item.val.recArg; in
            if nxt == null then []
            else [{ key = item.key + 1;
                    val = { nonRecArgs = nxt.nonRec; recArg = nxt.recArg; }; }];
        };
        nLayers = builtins.length chain;
        innermost = (builtins.elemAt chain (nLayers - 1)).val;
        # Base: whatever the innermost layer's `recArg` points to (the
        # first non-chain-successor tail). Elaborated normally — may be
        # a zero-field ctor application, a neutral, or anything else.
        baseTm = elaborate depth innermost.recArg;
        # Build one layer's payload from its non-rec HOAS field args and
        # a tail accumulator. Field args line up positionally with
        # `mono.fields[0..nFields-2]` (the rec field is at the end);
        # `prevOfArgs` extracts the data markers needed by `targetIdx`.
        # The innermost pair terminator is `Refl : Eq I j j` where
        # `j = targetIdx prev` for this layer.
        buildLayer = nonRecHoasArgs: accTm:
          let
            nonRecTms = map (a: elaborate depth a) nonRecHoasArgs;
            prev = prevOfArgs nonRecHoasArgs;
            targetIdxHoas = mono.targetIdx prev;
            targetIdxTm = elaborate depth targetIdxHoas;
            tags = mkTags targetIdxHoas;
            innerMost = T.mkPair accTm T.mkRefl;
            payloadInner = builtins.foldl'
              (acc: j:
                let f = builtins.elemAt nonRecTms (builtins.length nonRecTms - 1 - j);
                in T.mkPair f acc)
              innerMost
              (builtins.genList (x: x) (builtins.length nonRecTms));
          in T.mkDescCon dTm targetIdxTm
               (encodeTagTm tags.lTms tags.rTms ctorIdx nCtors payloadInner);
      in
      # Fold inward-to-outward: step idx=0 wraps baseTm with the
      # innermost layer's non-rec args, step idx=1 with the next layer
      # out, etc.
      builtins.foldl' (acc: idx:
        let
          layer = (builtins.elemAt chain (nLayers - 1 - idx)).val;
        in buildLayer layer.nonRecArgs acc
      ) baseTm (builtins.genList (x: x) nLayers);

  # Universe-level coercion. The HOAS surface accepts a level slot in
  # one of two encodings:
  #   - a Nix-meta `Int` (concrete level, shimmed via `T.mkLevelLit`);
  #   - a HOAS Level term — either an `_htag`-tagged construct
  #     (`level`/`levelZero`/`levelSuc`/`levelMax`) or a `_hoas`-tagged
  #     marker for a bound `forall "k" level …` variable. Both route
  #     through `elaborate`, whose first dispatch already handles
  #     markers (→ `T.mkVar`) and `_htag` nodes uniformly.
  # Anything else is a typed error at this boundary so a leaked marker
  # or random attrset fails loudly here rather than corrupting the
  # kernel tree downstream.
  elaborateLevel = depth: lvl:
    if builtins.isInt lvl then T.mkLevelLit lvl
    else if self.isMarker lvl || (builtins.isAttrs lvl && lvl ? _htag)
    then elaborate depth lvl
    else throw "hoas.elaborateLevel: expected Int or HOAS Level; got ${
      if builtins.isAttrs lvl
      then "attrset with keys: ${builtins.concatStringsSep ", " (builtins.attrNames lvl)}"
      else builtins.typeOf lvl
    }";

  # Inverse of `elaborateLevel`: a kernel Level Value back to a HOAS
  # Level node. Concrete chains map to the `levelZero`/`levelSuc`
  # combinators; `vLevelMax` reifies recursively; a neutral `vNe`
  # (a bound Level variable in the surrounding context) reifies to a
  # marker at the same de Bruijn level so that re-elaborating the
  # produced HOAS under a context that re-introduces the binder yields
  # back the same kernel Var. Levels are not function-typed, so any
  # `vNe` with a non-empty spine is a kernel invariant violation.
  reifyLevel = lv:
    if lv.tag == "VLevelZero" then self.levelZero
    else if lv.tag == "VLevelSuc" then self.levelSuc (self.reifyLevel lv.pred)
    else if lv.tag == "VLevelMax" then
      self.levelMax (self.reifyLevel lv.lhs) (self.reifyLevel lv.rhs)
    else if lv.tag == "VNe" then
      if lv.spine == [ ] then self.mkMarker lv.level
      else throw "hoas.reifyLevel: VNe Level with non-empty spine — Levels are not function-typed"
    else throw "hoas.reifyLevel: unsupported Level value tag '${lv.tag or "?"}'";

  # Elaboration: HOAS tree → de Bruijn Tm.
  #
  # elaborate : Int → HoasTree → Tm
  # depth tracks the current binding depth. When we encounter a binding
  # combinator (pi, lam, sigma, let), we:
  #   1. Apply the stored Nix lambda to mkMarker(depth)
  #   2. Recursively elaborate the resulting body at depth+1
  #   3. Markers with level L become T.mkVar(depth - L - 1)
  elaborate = depth: h:
    # Marker → variable
    if self.isMarker h then
      T.mkVar (depth - h.level - 1)

    else if !(builtins.isAttrs h) || !(h ? _htag) then
      let
        desc =
          if builtins.isAttrs h
          then "attrset with keys: ${builtins.concatStringsSep ", " (builtins.attrNames h)}"
          else builtins.typeOf h;
      in throw "hoas.elaborate: not an HOAS node (${desc})"

    else let t = h._htag; in

    # -- Types --
    # `nat` is the description-based fixpoint `mu natDesc`. natDescTm is
    # pre-elaborated at module scope to avoid re-elaborating on every use.
    if t == "nat" then T.mkMu T.mkUnit self.natDescTm T.mkTt
    # Reserved identifier `__descDesc` resolves to the pre-elaborated
    # description-of-descriptions Tm. Same pre-elaboration shortcut as
    # `nat` → `natDescTm`; consumers emit a single `desc-desc` node
    # instead of the full descDesc HOAS tree.
    else if t == "desc-desc" then self.descDescTm
    else if t == "desc-desc-app" then
      T.mkDescDescApp (elaborate depth h.I) (elaborateLevel depth h.L)
    else if t == "unit" then T.mkUnit
    else if t == "string" then T.mkString
    else if t == "int" then T.mkInt
    else if t == "float" then T.mkFloat
    else if t == "attrs" then T.mkAttrs
    else if t == "path" then T.mkPath
    else if t == "function" then T.mkFunction
    else if t == "any" then T.mkAny
    else if t == "U" then T.mkU (elaborateLevel depth h.level)
    # Level sort and its three constructors. `level` is a type former
    # (`U(0)`-inhabiting); the constructors build a Level Tm that
    # ultimately lands in a `U`/`desc-arg`/`desc-pi` level slot.
    else if t == "level" then T.mkLevel
    else if t == "level-zero" then T.mkLevelZero
    else if t == "level-suc" then T.mkLevelSuc (elaborateLevel depth h.pred)
    else if t == "level-max" then
      T.mkLevelMax (elaborateLevel depth h.lhs) (elaborateLevel depth h.rhs)
    # Asymmetric Nat→Level bridge. `n` accepts either a Nix-meta `Int`
    # (built into a primitive `suc^n zero` Nat term) or a HOAS term that
    # already elaborates to a primitive `Nat`. The kernel primitive
    # `Nat`/`zero`/`succ` is required here because `natToLevel`'s eval
    # rule dispatches on `VZero`/`VSucc` directly; the HOAS surface
    # `nat`/`zero`/`succ` produce μ-encoded Naturals and are not
    # accepted by the bridge.
    else if t == "nat-to-level" then
      T.mkNatToLevel (
        if builtins.isInt h.n
        then builtins.foldl' (acc: _: T.mkSucc acc)
               T.mkZero (builtins.genList (x: x) (if h.n < 0 then 0 else h.n))
        else elaborate depth h.n)
    # `listOf elem` is the description-based fixpoint `mu (listDesc elem) tt`.
    else if t == "list" then T.mkMu T.mkUnit (elaborate depth (self.listDesc h.elem)) T.mkTt
    # `sum l r` is the description-based fixpoint `mu (sumDesc l r) tt`.
    else if t == "sum" then T.mkMu T.mkUnit (elaborate depth (self.sumDesc h.left h.right)) T.mkTt
    # Kernel-primitive `sum-prim`/`inl-prim`/`inr-prim` — used by
    # `interpHoasAt`/`allHoasAt` for `plus`'s interpretation, matching
    # `eval/desc.nix`'s kernel `Sum` output token-for-token so conv between
    # HOAS-side and value-side `interp` values succeeds on plus descriptions.
    else if t == "sum-prim" then T.mkSum (elaborate depth h.L) (elaborate depth h.R)
    else if t == "inl-prim" then
      T.mkInl (elaborate depth h.L) (elaborate depth h.R) (elaborate depth h.term)
    else if t == "inr-prim" then
      T.mkInr (elaborate depth h.L) (elaborate depth h.R) (elaborate depth h.term)
    else if t == "sum-elim-prim" then
      T.mkSumElim (elaborate depth h.left) (elaborate depth h.right)
        (elaborate depth h.motive) (elaborate depth h.onLeft)
        (elaborate depth h.onRight) (elaborate depth h.scrut)
    else if t == "eq" then
      T.mkEq (elaborate depth h.type) (elaborate depth h.lhs) (elaborate depth h.rhs)

    # -- Compound types (sugar for nested sigma/sum) --
    else if t == "record" then
      let
        fields = h.fields;
        n = builtins.length fields;
      in if n == 0 then T.mkUnit
         else if n == 1 then elaborate depth (builtins.head fields).type
         else
           # Build nested Sigma right-to-left: Σ(f1:T1).Σ(f2:T2)...Tn
           let lastType = elaborate depth (builtins.elemAt fields (n - 1)).type;
           in builtins.foldl' (acc: i:
             let field = builtins.elemAt fields (n - 2 - i); in
             T.mkSigma field.name (elaborate depth field.type) acc
           ) lastType (builtins.genList (x: x) (n - 1))

    else if t == "maybe" then
      # Sum(inner, Unit) — Left = value present, Right = null.
      # Delegates to the `sum` branch so the description-based
      # representation (μ(sumDesc l r)) is used uniformly with
      # `inl`/`inr` values.
      elaborate depth (self.sum h.inner self.unit)

    else if t == "variant" then
      let
        branches = h.branches;
        n = builtins.length branches;
      in if n == 0 then elaborate depth self.void
         else if n == 1 then elaborate depth (builtins.head branches).type
         else
           # Build nested Sum right-to-left: Sum(T1, Sum(T2, ...Tn)).
           # Delegates to the `sum` branch so the nesting is in the
           # description representation, matching the inl/inr injection
           # shape.
           let lastType = (builtins.elemAt branches (n - 1)).type;
           in elaborate depth (builtins.foldl' (acc: i:
             let branch = builtins.elemAt branches (n - 2 - i); in
             self.sum branch.type acc
           ) lastType (builtins.genList (x: x) (n - 1)))

    # -- Binding types and terms (trampolined for deep nesting) --
    else if t == "pi" || t == "sigma" || t == "lam" || t == "let" then
      let
        # Peel nested binding forms iteratively via genericClosure
        chain = builtins.genericClosure {
          startSet = [{ key = depth; val = h; }];
          operator = item:
            let node = item.val; in
            if builtins.isAttrs node && node ? _htag &&
               (let nt = node._htag; in nt == "pi" || nt == "sigma" || nt == "lam" || nt == "let")
            then
              let marker = self.mkMarker item.key; in
              [{ key = item.key + 1; val = node.body marker; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        baseElab = elaborate (depth + n) base;
      in
      builtins.foldl' (acc: i:
        let
          item = builtins.elemAt chain (n - 1 - i);
          node = item.val;
          d = item.key;
          nt = node._htag;
        in
        if nt == "pi" then T.mkPi node.name (elaborate d node.domain) acc
        else if nt == "sigma" then T.mkSigma node.name (elaborate d node.fst) acc
        else if nt == "lam" then T.mkLam node.name (elaborate d node.domain) acc
        else T.mkLet node.name (elaborate d node.type) (elaborate d node.val) acc
      ) baseElab (builtins.genList (x: x) n)

    # -- Non-binding terms --
    # `zero` = `descCon natDesc tt (inlPrim L R refl)` — the plus-based
    # natDesc's `inl` summand is `descRet`, whose interp at I=⊤ is the
    # leaf-equality `Eq ⊤ tt tt`. L/R are closed interps: L = Eq ⊤ tt tt,
    # R = Σ (μnat tt) (_: Eq ⊤ tt tt).
    else if t == "zero" then
      let
        tags = buildTagInterpTms depth self.unitPrim self.natDesc self.ttPrim
                 [ self.descRet (self.descRec self.descRet) ];
      in
      T.mkDescCon self.natDescTm T.mkTt
        (encodeTagTm tags.lTms tags.rTms 0 2 T.mkRefl)
    # `succ n` = `descCon natDesc tt (inrPrim L R (pair n refl))` —
    # the plus-based natDesc's `inr` summand is `descRec descRet`,
    # whose interp is `Σ (μnat tt) (_: Eq ⊤ tt tt)`.
    # Trampolined for deep naturals (5000+) with shared lTms/rTms
    # across layers.
    else if t == "succ" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = h; }];
          operator = item:
            if builtins.isAttrs item.val && item.val ? _htag && item.val._htag == "succ"
            then [{ key = item.key + 1; val = item.val.pred; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        tags = buildTagInterpTms depth self.unitPrim self.natDesc self.ttPrim
                 [ self.descRet (self.descRec self.descRet) ];
      in builtins.foldl' (acc: _:
        T.mkDescCon self.natDescTm T.mkTt
          (encodeTagTm tags.lTms tags.rTms 1 2
             (T.mkPair acc T.mkRefl))
      ) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "tt" then T.mkTt
    else if t == "refl" then T.mkRefl
    else if t == "funext" then T.mkFunext
    else if t == "string-lit" then T.mkStringLit h.value
    else if t == "int-lit" then T.mkIntLit h.value
    else if t == "float-lit" then T.mkFloatLit h.value
    else if t == "attrs-lit" then T.mkAttrsLit
    else if t == "path-lit" then T.mkPathLit
    else if t == "fn-lit" then T.mkFnLit
    else if t == "any-lit" then T.mkAnyLit
    # `nil elem` = `descCon (listDesc elem) tt (inlPrim L R refl)` —
    # the plus-based `listDesc elem`'s `inl` summand is `descRet`;
    # L = Eq ⊤ tt tt,
    # R = Σ elem (_: Σ (μlist tt) (_: Eq ⊤ tt tt)).
    else if t == "nil" then
      let
        dHoas = self.listDesc h.elem;
        tags = buildTagInterpTms depth self.unitPrim dHoas self.ttPrim
                 [ self.descRet
                   (self.descArg self.unitPrim 0 h.elem (_: self.descRec self.descRet)) ];
      in
      T.mkDescCon (elaborate depth dHoas) T.mkTt
        (encodeTagTm tags.lTms tags.rTms 0 2 T.mkRefl)
    # `cons elem head tail` = `descCon (listDesc elem) tt
    #   (inrPrim L R (pair head (pair tail refl)))`.
    # Trampolined for deep lists (5000+ elements). The outer
    # `listDesc elem` is elaborated ONCE for the chain; lTms/rTms are
    # computed ONCE and shared across all emitted desc-cons. The
    # check/eval desc-con trampolines use reference identity on D to
    # peel homogeneous chains.
    else if t == "cons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; val = h; }];
          operator = item:
            if builtins.isAttrs item.val && item.val ? _htag && item.val._htag == "cons"
            then [{ key = item.key + 1; val = item.val.tail; }]
            else [];
        };
        n = builtins.length chain - 1;
        base = (builtins.elemAt chain n).val;
        dHoas = self.listDesc h.elem;
        dTm = elaborate depth dHoas;
        tags = buildTagInterpTms depth self.unitPrim dHoas self.ttPrim
                 [ self.descRet
                   (self.descArg self.unitPrim 0 h.elem (_: self.descRec self.descRet)) ];
      in builtins.foldl' (acc: i:
        let node = (builtins.elemAt chain (n - 1 - i)).val; in
        T.mkDescCon dTm T.mkTt
          (encodeTagTm tags.lTms tags.rTms 1 2
             (T.mkPair (elaborate depth node.head)
               (T.mkPair acc T.mkRefl)))
      ) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "pair" then
      T.mkPair (elaborate depth h.fst) (elaborate depth h.snd)
    # `inl l r a` = `descCon (sumDesc l r) tt (inlPrim L R (pair a refl))` —
    # the plus-based `sumDesc l r`'s summands are both
    # `descArg _ (_: descRet)`, so each summand's interp is
    # `Σ arm (_: Eq ⊤ tt tt)`.
    else if t == "inl" then
      let
        dHoas = self.sumDesc h.left h.right;
        tags = buildTagInterpTms depth self.unitPrim dHoas self.ttPrim
                 [ (self.descArg self.unitPrim 0 h.left  (_: self.descRet))
                   (self.descArg self.unitPrim 0 h.right (_: self.descRet)) ];
      in
      T.mkDescCon (elaborate depth dHoas) T.mkTt
        (encodeTagTm tags.lTms tags.rTms 0 2
           (T.mkPair (elaborate depth h.term) T.mkRefl))
    # `inr l r b` = `descCon (sumDesc l r) tt (inrPrim L R (pair b refl))` —
    # mirror of `inl`.
    else if t == "inr" then
      let
        dHoas = self.sumDesc h.left h.right;
        tags = buildTagInterpTms depth self.unitPrim dHoas self.ttPrim
                 [ (self.descArg self.unitPrim 0 h.left  (_: self.descRet))
                   (self.descArg self.unitPrim 0 h.right (_: self.descRet)) ];
      in
      T.mkDescCon (elaborate depth dHoas) T.mkTt
        (encodeTagTm tags.lTms tags.rTms 1 2
           (T.mkPair (elaborate depth h.term) T.mkRefl))
    else if t == "opaque-lam" then
      T.mkOpaqueLam h._fnBox (elaborate depth h.piHoas)
    else if t == "str-eq" then
      T.mkStrEq (elaborate depth h.lhs) (elaborate depth h.rhs)
    else if t == "ann" then
      if h.trusted or false
      then T.mkAnnTrusted (elaborate depth h.term) (elaborate depth h.type)
      else T.mkAnn (elaborate depth h.term) (elaborate depth h.type)
    else if t == "ann-trusted-retargeted-desc" then
      let bodyTm = elaborate depth h.body;
          iTm = elaborate depth h.I;
          retargeted = retargetSpineDescTm iTm bodyTm;
          typeTm = T.mkDesc T.mkLevelZero iTm;
      in T.mkAnnTrusted retargeted typeTm
    # Macro constructor fallback: elaborate as the annotated lam cascade.
    # Saturated chain applications are recognised in the `app` branch
    # below and emit flat `desc-con` Tms without touching this branch.
    else if t == "dt-ctor-mono" then elaborate depth h.fallback
    else if t == "dt-ctor-poly" then elaborate depth h.fallback
    # `app` tries flat-chain flattening for saturated macro-constructor
    # applications first. Non-chain applications fall through to the
    # regular `mkApp (elab fn) (elab arg)`.
    else if t == "app" then
      let flat = tryFlattenCtorChain depth h; in
      if flat != null then flat
      else T.mkApp (elaborate depth h.fn) (elaborate depth h.arg)
    else if t == "fst" then T.mkFst (elaborate depth h.pair)
    else if t == "snd" then T.mkSnd (elaborate depth h.pair)

    # -- Descriptions --
    else if t == "desc" then
      T.mkDesc (if h ? k then elaborateLevel depth h.k else T.mkLevelZero)
        (elaborate depth h.I)
    else if t == "desc-ret" then T.mkDescRet (elaborate depth h.j)
    else if t == "desc-arg" then
      let marker = self.mkMarker depth;
          kTm = elaborateLevel depth h.k;
          lTm = if h ? l then elaborateLevel depth h.l else kTm;
          eqTm = if h ? eq then elaborate depth h.eq else T.mkRefl;
      in T.mkDescArg kTm lTm (elaborate depth h.S) eqTm
           (elaborate (depth + 1) (h.body marker))
    else if t == "desc-rec" then
      T.mkDescRec (elaborate depth h.j) (elaborate depth h.D)
    else if t == "desc-pi" then
      let kTm = elaborateLevel depth h.k;
          lTm = if h ? l then elaborateLevel depth h.l else kTm;
          eqTm = if h ? eq then elaborate depth h.eq else T.mkRefl;
      in T.mkDescPi kTm lTm (elaborate depth h.S) eqTm (elaborate depth h.f)
        (elaborate depth h.D)
    else if t == "desc-plus" then
      T.mkDescPlus (elaborate depth h.A) (elaborate depth h.B)
    else if t == "mu" then
      T.mkMu (elaborate depth h.I) (elaborate depth h.D) (elaborate depth h.i)
    else if t == "desc-con" then
      T.mkDescCon (elaborate depth h.D) (elaborate depth h.i) (elaborate depth h.d)
    else if t == "desc-ind" then
      T.mkDescInd (elaborate depth h.D) (elaborate depth h.motive)
        (elaborate depth h.step) (elaborate depth h.i) (elaborate depth h.scrut)
    else if t == "desc-elim" then
      T.mkDescElim (elaborateLevel depth h.k)
        (elaborate depth h.motive) (elaborate depth h.onRet)
        (elaborate depth h.onArg) (elaborate depth h.onRec)
        (elaborate depth h.onPi) (elaborate depth h.onPlus) (elaborate depth h.scrut)

    # Kernel-primitive `interpD` / `allD` / `everywhereD` Tms (CDMM
    # §4.2.3 + §6.1). The `level` / `K` slots accept any Level encoding
    # (Nix-int, HOAS Level term, or kernel Tm) via `elaborateLevel`.
    else if t == "interp-d" then
      T.mkInterpD (elaborateLevel depth h.level)
        (elaborate depth h.I) (elaborate depth h.D)
        (elaborate depth h.X) (elaborate depth h.i)
    else if t == "all-d" then
      T.mkAllD (elaborateLevel depth h.level)
        (elaborate depth h.I) (elaborate depth h.D)
        (elaborateLevel depth h.K)
        (elaborate depth h.X) (elaborate depth h.M)
        (elaborate depth h.i) (elaborate depth h.d)
    else if t == "everywhere-d" then
      T.mkEverywhereD (elaborateLevel depth h.level)
        (elaborate depth h.I) (elaborate depth h.D)
        (elaborateLevel depth h.K)
        (elaborate depth h.X) (elaborate depth h.M)
        (elaborate depth h.ih) (elaborate depth h.i) (elaborate depth h.d)

    # Encoded desc constructors. Each `desc-*-enc` HOAS node carries
    # the index type `I` and the relevant kernel arguments; elaborate
    # to a `mkApp` chain over the kernel-internal `encodeDescX_Tm`
    # closed lambdas. The result evaluates to a `VDescCon` value of
    # type `μ⊤(descDesc I k) tt` — the encoded form of the source
    # description. Homogeneous-l (no explicit `l`/`eq`) routes through
    # `encodeDescArgTm`/`encodeDescPiTm`; heterogeneous-l (caller
    # supplied `l` and `eq`) routes through `encodeDescArgAtTm`/
    # `encodeDescPiAtTm`.
    else if t == "desc-ret-enc" then
      let iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          jTm = elaborate depth h.j;
      in T.mkApp (T.mkApp (T.mkApp self.encodeDescRetTm iTm) kTm) jTm
    else if t == "desc-arg-enc" then
      let marker = self.mkMarker depth;
          iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          sTm = elaborate depth h.S;
          bodyTm = elaborate (depth + 1) (h.body marker);
          tLam  = T.mkLam "_" sTm bodyTm;
      in
        if h ? l && h ? eq
        then
          let lTm  = elaborateLevel depth h.l;
              eqTm = elaborate depth h.eq;
          in T.mkApp
               (T.mkApp
                 (T.mkApp
                   (T.mkApp
                     (T.mkApp
                       (T.mkApp self.encodeDescArgAtTm iTm)
                       kTm)
                     lTm)
                   eqTm)
                 sTm)
               tLam
        else if h ? l
        then
          let lTm = elaborateLevel depth h.l; in
          T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp self.encodeDescArgAtTm iTm)
                    kTm)
                  lTm)
                T.mkRefl)
              sTm)
            tLam
        else
          T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp self.encodeDescArgTm iTm)
                kTm)
              sTm)
            tLam
    else if t == "desc-rec-enc" then
      let iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          jTm = elaborate depth h.j;
          dTm = elaborate depth h.D;
      in T.mkApp
           (T.mkApp
             (T.mkApp
               (T.mkApp self.encodeDescRecTm iTm)
               kTm)
             jTm)
           dTm
    else if t == "desc-pi-enc" then
      let iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          sTm = elaborate depth h.S;
          fTm = elaborate depth h.f;
          dTm = elaborate depth h.D;
      in
        if h ? l && h ? eq
        then
          let lTm  = elaborateLevel depth h.l;
              eqTm = elaborate depth h.eq;
          in T.mkApp
               (T.mkApp
                 (T.mkApp
                   (T.mkApp
                     (T.mkApp
                       (T.mkApp
                         (T.mkApp self.encodeDescPiAtTm iTm)
                         kTm)
                       lTm)
                     eqTm)
                   sTm)
                 fTm)
               dTm
        else if h ? l
        then
          let lTm = elaborateLevel depth h.l; in
          T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp self.encodeDescPiAtTm iTm)
                      kTm)
                    lTm)
                  T.mkRefl)
                sTm)
              fTm)
            dTm
        else
          T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp self.encodeDescPiTm iTm)
                  kTm)
                sTm)
              fTm)
            dTm
    else if t == "desc-plus-enc" then
      let iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          aTm = elaborate depth h.A;
          bTm = elaborate depth h.B;
      in T.mkApp
           (T.mkApp
             (T.mkApp
               (T.mkApp self.encodeDescPlusTm iTm)
               kTm)
             aTm)
           bTm
    else if t == "desc-elim-enc" then
      let iTm = elaborate depth h.I;
          kTm = elaborateLevel depth h.k;
          lTm = elaborateLevel depth h.L;
          mTm = elaborate depth h.motive;
          rTm = elaborate depth h.onRet;
          aTm = elaborate depth h.onArg;
          ecTm = elaborate depth h.onRec;
          pTm = elaborate depth h.onPi;
          plTm = elaborate depth h.onPlus;
          sTm = elaborate depth h.scrut;
      in T.mkApp
           (T.mkApp
             (T.mkApp
               (T.mkApp
                 (T.mkApp
                   (T.mkApp
                     (T.mkApp
                       (T.mkApp
                         (T.mkApp
                           (T.mkApp self.encodeDescElimTm iTm)
                           kTm)
                         lTm)
                       mTm)
                     rTm)
                   aTm)
                 ecTm)
               pTm)
             plTm)
           sTm

    # -- Lift primitive --
    # The bound witness `eq : Eq Level (max l m) m` is auto-emitted as
    # `T.mkRefl` when absent; the kernel CHECK rule decides `convLevel
    # (max l m) m` via the semilattice quotient. The HOAS `*WithEq`
    # variants pass an explicit eq term (used when `l`/`m` are level-
    # polymorphic binders and `convLevel` cannot decide `refl`). Same
    # bound-witness shape as desc-arg.
    else if t == "lift" then
      T.mkLift (elaborateLevel depth h.l) (elaborateLevel depth h.m)
        (if h ? eq then elaborate depth h.eq else T.mkRefl)
        (elaborate depth h.A)
    else if t == "lift-intro" then
      T.mkLiftIntro (elaborateLevel depth h.l) (elaborateLevel depth h.m)
        (if h ? eq then elaborate depth h.eq else T.mkRefl)
        (elaborate depth h.A) (elaborate depth h.a)
    else if t == "lift-elim" then
      T.mkLiftElim (elaborateLevel depth h.l) (elaborateLevel depth h.m)
        (if h ? eq then elaborate depth h.eq else T.mkRefl)
        (elaborate depth h.A) (elaborate depth h.x)

    # -- Eliminators --
    # Nat/List/Sum eliminators route through the macro-generated
    # `NatDT.elim` / `ListDT.elim` / `SumDT.elim` (see hoas/datatype.nix's
    # dispatchStep), which produce `descInd` spines directly; no dedicated
    # `nat-elim` / `list-elim` / `sum-elim` HOAS tag is emitted. The
    # kernel `nat-elim` primitive type-checks its scrutinee against
    # `V.vNat`, which HOAS `nat = NatDT.T = μ NatDT.D tt` never produces —
    # a bridging HOAS tag would be structurally unusable. User-level
    # motive-universe escape hatches (e.g. `natCaseU`'s `Nat → U(0)`
    # requiring motive at universe 1) go via `descInd` directly on the
    # macro's `D` (see combinators.nix:natCaseU). The Bool eliminator is
    # derived as `descInd boolDesc` with a `sumElimPrim`-dispatching step
    # (combinators.nix:boolElim) — no dedicated HOAS tag.
    else if t == "j" then
      T.mkJ (elaborate depth h.type) (elaborate depth h.lhs)
        (elaborate depth h.motive) (elaborate depth h.base)
        (elaborate depth h.rhs) (elaborate depth h.eq)

    else if t == "squash" then
      T.mkSquash (elaborate depth h.A)
    else if t == "squash-intro" then
      T.mkSquashIntro (elaborate depth h.a)
    else if t == "squash-elim" then
      T.mkSquashElim (elaborate depth h.A) (elaborate depth h.B)
        (elaborate depth h.f) (elaborate depth h.x)

    else throw "hoas.elaborate: unknown tag: ${t}";
in {
  scope = {
    inherit elaborate reifyLevel;

    # Elaborate from depth 0.
    elab = elaborate 0;

    # Elaborate type + term, then run the kernel checker. On success the
    # elaborated Tm is returned unchanged; on failure the result is
    # decorated with `hint` (from `fx.diag.hints`) and `surface` (back-map
    # through the term's SourceMap).
    #
    # Inlined rather than routed through `CHD.runCheckDLazy` to avoid a
    # per-call function layer + closure allocation on the hot success
    # path. The SourceMap reference sits inside the failure branch, so
    # `self.sourceMapOf hoasTm` is only forced when a type error fires.
    # `CHD.runCheckDLazy` / `elab2` remain available for library callers
    # that prefer the shell wrapper or an eager (Tm, SourceMap) pair.
    checkHoas = hoasTy: hoasTm:
      let
        # Type-check the type Tm first so that desc-* CHECK rules
        # retarget any inner descriptions to encoded form. The eval'd
        # type Val then has the same shape as the values produced by
        # desc-con's internal `checkDescAtAnyLevel` retarget — without
        # this pass the type's `.D` stays primitive while the term's
        # checked payload becomes encoded, causing a structural mismatch
        # at conv time.
        tyRaw = self.elab hoasTy;
        tyResult = CH.runCheck (CH.checkTypeLevel CH.emptyCtx tyRaw);
        ty = if builtins.isAttrs tyResult && tyResult ? error
             then tyRaw
             else tyResult.term;
        tm  = self.elab hoasTm;
        vTy = E.eval [] ty;
        r   = if builtins.isAttrs tyResult && tyResult ? error
              then tyResult
              else CH.runCheck (CH.check CH.emptyCtx tm vTy);
      in
        if builtins.isAttrs r && r ? error
        then
          let
            hint = fx.diag.hints.resolve r.error;
            # Embed the hint into the leaf so Pr.multiLine renders it
            # inline. When resolution misses, the error tree is
            # unchanged.
            errorTree =
              if hint == null then r.error
              else fx.diag.error.setLeafHint hint r.error;
          in r // {
            error   = errorTree;
            inherit hint;
            surface = CHD.sourceMap.hoasAtError r.error (self.sourceMapOf hoasTm);
          }
        else r;

    inferHoas = hoasTm:
      let
        tm = self.elab hoasTm;
        r  = CH.runCheck (CH.infer CH.emptyCtx tm);
      in
        if builtins.isAttrs r && r ? error
        then
          let
            hint = fx.diag.hints.resolve r.error;
            errorTree =
              if hint == null then r.error
              else fx.diag.error.setLeafHint hint r.error;
          in r // {
            error   = errorTree;
            inherit hint;
            surface = CHD.sourceMap.hoasAtError r.error (self.sourceMapOf hoasTm);
          }
        else r;

    # Natural number literal helper — build S^n(zero).
    natLit = n:
      builtins.foldl' (acc: _: self.succ acc) self.zero (builtins.genList (x: x) n);
  };
  tests = {};
}
