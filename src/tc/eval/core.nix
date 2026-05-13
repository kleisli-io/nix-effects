# Evaluator core: value operations, eliminators, and the main `evalF`.
#
# Pure evaluator interpreting kernel terms in an environment of values
# (§4, §9). Zero effect-system imports — part of the trusted computing
# base.
#
# Fuel-threaded: each `evalF` call decrements a counter; exhaustion
# throws "normalization budget exceeded". Default budget is 10M steps
# (§9). Trampolines the `desc-con` chain via `builtins.genericClosure`
# to bound stack depth on deep generated recursive data (§11.3).
#
# Description operations (`vDescIndF`, `linearProfileF`)
# live in the sibling `desc.nix`; `evalF` dispatches to them through
# `self`.
{ self, fx, ... }:

let
  val = fx.tc.value;
  inherit (val) mkClosure
    vLam vPi vSigma vPair
    vUnit vTt vBootSum vBootInl vBootInr vBootEq vBootRefl vFunext vU vNe
    vSquash vSquashIntro
    vLevel vLevelZero vLevelSuc vLevelMax
    vLift vLiftIntro
    vDesc vMu vDescCon
    vString vInt vFloat vAttrs vPath vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit
    eApp eFst eSnd eBootSumElim eBootJ eStrEq eLiftElim
    eSquashElim;
  H = fx.tc.hoas;
  boolDescTm = H.elab H.boolDesc;

  # Cached `U(0)` value. `mkU mkLevelZero` produces a term whose `level` is the
  # `level-zero` singleton; evaluating under the U-case returns this
  # sentinel directly — no fuel decrement, no dispatch, no allocation.
  vUZero = vU vLevelZero;

  evalDescRef = eval: ref:
    ref // {
      I = eval ref.I;
      level = eval ref.level;
      params = map eval (ref.params or []);
    };
in {
  scope = {
    defaultFuel = 10000000;

    instantiateF = fuel: cl: arg: self.evalF fuel ([ arg ] ++ cl.env) cl.body;

    vAppF = fuel: fn: arg:
      if fn.tag == "VDescViewFn" then fn.apply arg
      else if fn.tag == "VLam" then self.instantiateF fuel fn.closure arg
      else if fn.tag == "VNe" then vNe fn.level (fn.spine ++ [ (eApp arg) ])
      else throw "tc: vApp on non-function (tag=${fn.tag})";

    vFst = p:
      if p.tag == "VPair" then p.fst
      else if p.tag == "VNe" then vNe p.level (p.spine ++ [ eFst ])
      else throw "tc: vFst on non-pair (tag=${p.tag})";

    vSnd = p:
      if p.tag == "VPair" then p.snd
      else if p.tag == "VNe" then vNe p.level (p.spine ++ [ eSnd ])
      else throw "tc: vSnd on non-pair (tag=${p.tag})";

    # vStrEq — string equality primitive.
    # Both VStringLit → plus-encoded VDescCon true/false. Neutral → spine.
    # StrEq is symmetric, so we canonicalize neutral-first for the spine.
    vStrEq = lhs: rhs:
      let
        boolDescV = self.eval [] boolDescTm;
        eqTtV = vBootEq vUnit vTt vTt;
        vBoolTrue = vDescCon boolDescV vTt (vBootInl eqTtV eqTtV vBootRefl);
        vBoolFalse = vDescCon boolDescV vTt (vBootInr eqTtV eqTtV vBootRefl);
      in
      if lhs.tag == "VStringLit" && rhs.tag == "VStringLit" then
        if lhs.value == rhs.value then vBoolTrue else vBoolFalse
      else if lhs.tag == "VNe" then
        vNe lhs.level (lhs.spine ++ [ (eStrEq rhs) ])
      else if rhs.tag == "VNe" then
        vNe rhs.level (rhs.spine ++ [ (eStrEq lhs) ])
      else throw "tc: vStrEq on non-string (tags=${lhs.tag}, ${rhs.tag})";

    vBootSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
      if scrut.tag == "VBootInl" then self.vAppF fuel onLeft scrut.val
      else if scrut.tag == "VBootInr" then self.vAppF fuel onRight scrut.val
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eBootSumElim left right motive onLeft onRight) ])
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${scrut.tag})";

    # J computation: J(A, a, P, pr, b, refl) = pr.
    # When eq=VBootRefl, the checker has verified b≡a, so `rhs` is unused.
    # When eq is neutral, `rhs` is preserved in the EBootJ spine frame for quotation.
    vBootJ = type: lhs: motive: base: rhs: eq:
      if eq.tag == "VBootRefl" then base
      else if eq.tag == "VNe" then
        vNe eq.level (eq.spine ++ [ (eBootJ type lhs motive base rhs) ])
      else throw "tc: vBootJ on non-eq (tag=${eq.tag})";

    # `recTrunc A B f x` for `x : Squash A` returning `Squash B`.
    # β-reduces on canonical `VSquashIntro a` to `f a`; on stuck `VNe`
    # appends an `ESquashElim` frame. Throws on any other shape — INFER
    # rejects `recTrunc` of a non-Squash value before evaluation.
    vSquashElimF = fuel: A: B: f: x:
      if x.tag == "VSquashIntro" then self.vAppF fuel f x.a
      else if x.tag == "VNe"
      then vNe x.level (x.spine ++ [ (eSquashElim A B f) ])
      else throw "tc: vSquashElim on non-Squash (tag=${x.tag})";

    # Lift type-former. `Lift l m eq A : U(m)` is the type of values of
    # `A : U(l)` transported up to `U(m)`. Conv collapses idempotently
    # when `convLevel l m` (the load-bearing backward-compat rule for
    # homogeneous code: `Lift l l _ A ≡ A`) and composes nested Lifts
    # (`Lift l m _ (Lift l' l _ A') ≡ Lift l' m _ A'`). The witness slot
    # is irrelevant — emit `vBootRefl` on collapse since both bound
    # conditions hold by transitivity.
    vLiftF = l: m: eq: A:
      if fx.tc.conv.convLevel l m then A
      else if A.tag == "VLift"
      then vLift A.l m vBootRefl A.A
      else vLift l m eq A;

    # Lift introducer. Idempotent at `convLevel l m` (returns `a`); η on
    # a stuck `lower`-spine drops the trailing `ELiftElim` frame
    # (`lift _ (lower _ x) ≡ x`). Witness-irrelevance is enforced by
    # `convLevel`-comparing levels and structural equality on the
    # carried `A` — the spine's `eq` is not consulted.
    vLiftIntroF = l: m: eq: A: a:
      if fx.tc.conv.convLevel l m then a
      else if a.tag == "VNe" && a.spine != []
        && (let last = builtins.elemAt a.spine (builtins.length a.spine - 1);
            in last.tag == "ELiftElim"
               && fx.tc.conv.convLevel last.l l
               && fx.tc.conv.convLevel last.m m
               && last.A == A)
      then let n = builtins.length a.spine; in
        vNe a.level (builtins.genList (i: builtins.elemAt a.spine i) (n - 1))
      else vLiftIntro l m eq A a;

    # Lift eliminator (`lower`). Idempotent at `convLevel l m`;
    # β-reduces `lower _ (lift _ a) → a`; appends `ELiftElim` to the
    # spine of a stuck neutral. Throws on any other shape — the type
    # checker rejects ill-typed `lower` before evaluation.
    vLiftElimF = l: m: eq: A: x:
      if fx.tc.conv.convLevel l m then x
      else if x.tag == "VLiftIntro" then x.a
      else if x.tag == "VNe"
      then vNe x.level (x.spine ++ [ (eLiftElim l m eq A) ])
      else throw "tc: vLiftElim on non-Lift (tag=${x.tag})";

    # Main evaluator with fuel (§9)
    evalF = fuel: env: tm:
      if fuel <= 0 then throw "normalization budget exceeded"
      else let t = tm.tag; f = fuel - 1; ev = self.evalF f env; in
      if t == "var" then builtins.elemAt env tm.idx
      else if t == "let" then self.evalF f ([ (ev tm.val) ] ++ env) tm.body
      else if t == "ann" then
        let v = ev tm.term; in
        if tm ? _descRef
        then v // { _descRef = evalDescRef ev tm._descRef; }
        else v

      else if t == "pi" then vPi tm.name (ev tm.domain) (mkClosure env tm.codomain)
      else if t == "lam" then vLam tm.name (ev tm.domain) (mkClosure env tm.body)
      else if t == "app" then self.vAppF f (ev tm.fn) (ev tm.arg)

      else if t == "sigma" then vSigma tm.name (ev tm.fst) (mkClosure env tm.snd)
      else if t == "pair" then vPair (ev tm.fst) (ev tm.snd)
      else if t == "fst" then self.vFst (ev tm.pair)
      else if t == "snd" then self.vSnd (ev tm.pair)

      else if t == "unit" then vUnit
      else if t == "tt" then vTt

      else if t == "boot-sum" then vBootSum (ev tm.left) (ev tm.right)
      else if t == "boot-inl" then vBootInl (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "boot-inr" then vBootInr (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "boot-sum-elim" then
        self.vBootSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
          (ev tm.onLeft) (ev tm.onRight) (ev tm.scrut)

      else if t == "boot-eq" then vBootEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
      else if t == "boot-refl" then vBootRefl
      else if t == "funext" then vFunext
      else if t == "boot-j" then
        self.vBootJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
          (ev tm.base) (ev tm.rhs) (ev tm.eq)

      else if t == "squash"       then vSquash (ev tm.A)
      else if t == "squash-intro" then vSquashIntro (ev tm.a)
      else if t == "squash-elim"  then
        self.vSquashElimF f (ev tm.A) (ev tm.B) (ev tm.f) (ev tm.x)

      # Descriptions
      else if t == "desc" then
        # Level-zero fast-path: the prelude `desc I` (= desc^0 I) is
        # the overwhelmingly common shape. Reuse the `vLevelZero`
        # singleton and skip the eval/int-shim pipeline on `tm.k`.
        if tm.k.tag == "level-zero"
        then vDesc vLevelZero (ev tm.I)
        else vDesc (ev tm.k) (ev tm.I)
      else if t == "mu" then vMu (ev tm.I) (ev tm.D) (ev tm.i)
      # desc-con — trampolined for deep recursive chains (5000+).
      # Peels a homogeneous desc-con chain along its single recursive
      # position when D = plus A B with exactly one of A, B linear-
      # recursive (a descArg-chain ending in `descRec descRet`). The
      # recursive summand drives the chain; its injection side picks
      # the payload tag (`boot-inl` when A is recursive, `boot-inr` when B is).
      #
      # Payload at each layer is `boot-inl/boot-inr lTy rTy (pair f_0 … (pair REC refl))`
      # — n data fields, the recursive tail, and a refl witness for
      # the ret-leaf equality. lTy/rTy are invariant across layers (D
      # is shared) and reused from the first peel.
      #
      # Non-linear shapes (tree, mutual recursion, multi-recursive
      # ctors, non-plus D) fall through to per-layer evaluation.
      #
      # D-sharing across layers: fast path is structural equality of
      # the D subterm (holds when elaborate emits a shared dTm per
      # chain, and when β-reducing macro-generated constructors under
      # a shared param env); fallback is conv-equality of the evaluated
      # D against the outer dVal.
      else if t == "desc-con" then
        let
          dVal = ev tm.D;
          # Classify plus D. null declines the trampoline; otherwise
          # returns the linear profile and which side (`inl`/`inr`)
          # carries the recursive summand.
          plusSides =
            let view = self.descViewF f dVal; in
            if view != null && view.idx == 4
            then { A = view.A; B = view.B; }
            else null;
          classify =
            if plusSides == null then null
            else
              let pA = self.linearProfileF f plusSides.A;
                  pB = self.linearProfileF f plusSides.B;
              in if pA != null && pB == null then { profile = pA; side = "inl"; }
                 else if pB != null && pA == null then { profile = pB; side = "inr"; }
                 else null;
          profile = if classify == null then [] else classify.profile;
          nFields = builtins.length profile;
          depth = builtins.length env;
          sameD = d2Tm:
            if d2Tm == tm.D then true
            else fx.tc.conv.conv depth (self.evalF f env d2Tm) dVal;
          # Walk n data-field pairs terminated by `pair REC refl`.
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
                  else collect (i + 1) p.snd (acc ++ [p.fst]);
            in collect 0 inner [];
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
            else if !(sameD node.D) then null
            else walkPayload node.d;
          # Integer key is sufficient for dedup. `peel` is O(1) field
          # inspection into the already-concrete `tm`; no deferred work
          # accumulates on `val`, so the trampoline.nix deepSeq defense
          # is unnecessary and would add O(N²) cost through repeated
          # traversal.
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; peeled = peel tm; }];
            operator = item:
              if item.peeled == null then []
              else
                let val = item.peeled.tail; in
                [{ key = item.key + 1; inherit val; peeled = peel val; }];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
          topPeel = if n >= 1 then (builtins.elemAt chain 0).peeled else null;
        in if n > f then throw "normalization budget exceeded"
        else let
          baseVal = vDescCon dVal
            (if base.i.tag == "tt" then vTt else self.evalF (f - n) env base.i)
            (self.evalF (f - n) env base.d);
          buildInner = hs: innerTail:
            if hs == [] then innerTail
            else vPair (builtins.head hs) (buildInner (builtins.tail hs) innerTail);
          wrapPayload = innerVal:
            topPeel.rebuildVal (tm': self.evalF (f - n) env tm') innerVal;
        in builtins.foldl' (acc: i:
          let
            layerItem = builtins.elemAt chain (n - 1 - i);
            layer = layerItem.val;
            peeled = layerItem.peeled;
            heads = peeled.heads;
            headVals = map (h: self.evalF (f - n + i) env h) heads;
            iLayerVal =
              if layer.i.tag == "tt" then vTt else self.evalF (f - n + i) env layer.i;
          in vDescCon dVal iLayerVal
               (wrapPayload (buildInner headVals (vPair acc vBootRefl)))
        ) baseVal (builtins.genList (x: x) n)
      else if t == "desc-ind" then
        self.vDescIndF f (ev tm.D) (ev tm.motive) (ev tm.step) (ev tm.i) (ev tm.scrut)

      else if t == "desc-desc-app" then
        self.mkDescDescAppVF f (ev tm.I) (ev tm.L)

      # Kernel-primitive `interpD` / `allD` / `everywhereD`. Level-zero
      # fast-path on `tm.level` (and `tm.K` where present) mirrors the
      # `desc-arg` shape — the prelude's homogeneous-at-zero call sites
      # bypass the eval pipeline on a `mkLevelZero` literal.
      else if t == "interp-d" then
        self.vInterpDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I) (ev tm.D) (ev tm.X) (ev tm.i)
      else if t == "all-d" then
        self.vAllDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I) (ev tm.D)
          (if tm.K.tag == "level-zero" then vLevelZero else ev tm.K)
          (ev tm.X) (ev tm.M) (ev tm.i) (ev tm.d)
      else if t == "everywhere-d" then
        self.vEverywhereDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I) (ev tm.D)
          (if tm.K.tag == "level-zero" then vLevelZero else ev tm.K)
          (ev tm.X) (ev tm.M) (ev tm.ih) (ev tm.i) (ev tm.d)

      # Lift primitive. Level-zero fast-path on `tm.l` / `tm.m` mirrors
      # the `desc-arg` / `desc-pi` shape — both slots are most often
      # `mkLevelZero` for the prelude's homogeneous-at-zero call sites,
      # and the smart constructor's `convLevel l m` idempotent collapse
      # then fires immediately on the cached `vLevelZero` singleton.
      else if t == "lift" then
        self.vLiftF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq) (ev tm.A)
      else if t == "lift-intro" then
        self.vLiftIntroF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq) (ev tm.A) (ev tm.a)
      else if t == "lift-elim" then
        self.vLiftElimF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq) (ev tm.A) (ev tm.x)

      else if t == "U" then
        if tm.level.tag == "level-zero" then vUZero
        else vU (ev tm.level)

      # Level expressions are preserved structurally. Normalisation
      # (`max a a = a`, `suc (max a b) = max (suc a) (suc b)`, zero
      # absorption, sorted spine) happens at conv time, not eval.
      else if t == "level" then vLevel
      else if t == "level-zero" then vLevelZero
      else if t == "level-suc" then vLevelSuc (ev tm.pred)
      else if t == "level-max" then vLevelMax (ev tm.lhs) (ev tm.rhs)
      # Axiomatized primitives
      else if t == "string" then vString
      else if t == "int" then vInt
      else if t == "float" then vFloat
      else if t == "attrs" then vAttrs
      else if t == "path" then vPath
      else if t == "function" then vFunction
      else if t == "any" then vAny

      else if t == "str-eq" then self.vStrEq (ev tm.lhs) (ev tm.rhs)

      else if t == "string-lit" then vStringLit tm.value
      else if t == "int-lit" then vIntLit tm.value
      else if t == "float-lit" then vFloatLit tm.value
      else if t == "attrs-lit" then vAttrsLit
      else if t == "path-lit" then vPathLit
      else if t == "fn-lit" then vFnLit
      else if t == "any-lit" then vAnyLit

      # Opaque lambda: axiomatized value — not callable in kernel
      else if t == "opaque-lam" then val.vOpaqueLam tm._fnBox (ev tm.piTy)

      else throw "tc: eval unknown tag '${t}'";

    # Default-fuel wrappers for core-owned bindings.
    eval = self.evalF self.defaultFuel;
    instantiate = self.instantiateF self.defaultFuel;
    vApp = self.vAppF self.defaultFuel;
    mkDescDescAppV = self.mkDescDescAppVF self.defaultFuel;
    vBootSumElim = self.vBootSumElimF self.defaultFuel;
    vSquashElim = self.vSquashElimF self.defaultFuel;
  };

  tests = let
    T = fx.tc.term;
    H = fx.tc.hoas;
    inherit (val) freshVar;
    inherit (self) eval evalF instantiate;

    idTm = T.mkLam "x" T.mkUnit (T.mkVar 0);
    appIdTt = T.mkApp idTm T.mkTt;
    encRet = H.elab (H.retI H.unit 0 H.tt);
    encArg = H.elab (H.descArg H.unit 0 H.nat (_: H.retI H.unit 0 H.tt));
    encArg1 = H.elab (H.descArg H.unit 1 (H.u 0) (_: H.retI H.unit 1 H.tt));
    encRec = H.elab (H.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
    encPi = H.elab (H.descPi 0 H.nat (H.retI H.unit 0 H.tt));
    descViewOf = tm: self.descView (eval [] tm);
  in {
    "eval-var-0" = { expr = (eval [ vTt vUnit ] (T.mkVar 0)).tag; expected = "VTt"; };
    "eval-var-1" = { expr = (eval [ vTt vUnit ] (T.mkVar 1)).tag; expected = "VUnit"; };

    "eval-let" = {
      expr = (eval [] (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0))).tag;
      expected = "VTt";
    };

    "eval-ann" = {
      expr = (eval [] (T.mkAnn T.mkTt T.mkUnit)).tag;
      expected = "VTt";
    };

    "eval-lam" = { expr = (eval [] idTm).tag; expected = "VLam"; };
    "eval-pi" = { expr = (eval [] (T.mkPi "x" T.mkUnit T.mkUnit)).tag; expected = "VPi"; };
    "eval-app-beta" = {
      expr = (eval [] appIdTt).tag;
      expected = "VTt";
    };
    "eval-app-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkApp (T.mkVar 0) T.mkTt)).tag;
      expected = "VNe";
    };

    "eval-sigma" = { expr = (eval [] (T.mkSigma "x" T.mkUnit T.mkUnit)).tag; expected = "VSigma"; };
    "eval-pair" = { expr = (eval [] (T.mkPair T.mkTt T.mkTt)).tag; expected = "VPair"; };
    "eval-fst" = {
      expr = (eval [] (T.mkFst (T.mkPair T.mkTt T.mkTt))).tag;
      expected = "VTt";
    };
    "eval-snd" = {
      expr = (eval [] (T.mkSnd (T.mkPair T.mkTt T.mkTt))).tag;
      expected = "VTt";
    };
    "eval-fst-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkFst (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-unit" = { expr = (eval [] T.mkUnit).tag; expected = "VUnit"; };
    "eval-tt" = { expr = (eval [] T.mkTt).tag; expected = "VTt"; };

    "eval-boot-sum" = { expr = (eval [] (T.mkBootSum T.mkUnit T.mkUnit)).tag; expected = "VBootSum"; };
    "eval-boot-inl" = { expr = (eval [] (T.mkBootInl T.mkUnit T.mkUnit T.mkTt)).tag; expected = "VBootInl"; };
    "eval-boot-inr" = { expr = (eval [] (T.mkBootInr T.mkUnit T.mkUnit T.mkTt)).tag; expected = "VBootInr"; };
    "eval-boot-sum-elim-inl" = {
      expr = (eval [] (T.mkBootSumElim T.mkUnit T.mkUnit
        (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
        (T.mkLam "x" T.mkUnit T.mkTt)
        (T.mkLam "y" T.mkUnit T.mkTt)
        (T.mkBootInl T.mkUnit T.mkUnit T.mkTt))).tag;
      expected = "VTt";
    };
    "eval-boot-sum-elim-inr" = {
      expr = (eval [] (T.mkBootSumElim T.mkUnit T.mkUnit
        (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
        (T.mkLam "x" T.mkUnit T.mkTt)
        (T.mkLam "y" T.mkUnit T.mkTt)
        (T.mkBootInr T.mkUnit T.mkUnit T.mkTt))).tag;
      expected = "VTt";
    };

    "eval-eq" = { expr = (eval [] (T.mkBootEq T.mkUnit T.mkTt T.mkTt)).tag; expected = "VBootEq"; };
    "eval-refl" = { expr = (eval [] T.mkBootRefl).tag; expected = "VBootRefl"; };
    "eval-funext" = { expr = (eval [] T.mkFunext).tag; expected = "VFunext"; };
    "eval-squash" = { expr = (eval [] (T.mkSquash T.mkUnit)).tag; expected = "VSquash"; };
    "eval-squash-A" = { expr = (eval [] (T.mkSquash T.mkUnit)).A.tag; expected = "VUnit"; };
    "eval-squash-intro" = {
      expr = (eval [] (T.mkSquashIntro T.mkTt)).tag;
      expected = "VSquashIntro";
    };
    "eval-squash-intro-a" = {
      expr = (eval [] (T.mkSquashIntro T.mkTt)).a.tag;
      expected = "VTt";
    };
    "eval-squash-elim-beta" = {
      # recTrunc Unit Unit (λ_:Unit. squashIntro tt) (squashIntro tt) → squashIntro tt
      expr = let
        f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
        e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkSquashIntro T.mkTt);
      in (eval [] e).tag;
      expected = "VSquashIntro";
    };
    "eval-squash-elim-stuck" = {
      # recTrunc on a stuck VNe leaves an ESquashElim spine frame.
      expr = let
        f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
        e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkVar 0);
      in (eval [ (freshVar 0) ] e).tag;
      expected = "VNe";
    };
    "eval-squash-elim-stuck-spine-tag" = {
      expr = let
        f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
        e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkVar 0);
        r = eval [ (freshVar 0) ] e;
      in (builtins.head r.spine).tag;
      expected = "ESquashElim";
    };
    "eval-j-refl" = {
      expr = (eval [] (T.mkBootJ T.mkUnit T.mkTt
        (T.mkLam "y" T.mkUnit (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) T.mkUnit))
        T.mkTt T.mkTt T.mkBootRefl)).tag;
      expected = "VTt";
    };
    "eval-j-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkBootJ T.mkUnit T.mkTt
        (T.mkLam "y" T.mkUnit (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) (T.mkU T.mkLevelZero)))
        (T.mkU T.mkLevelZero) T.mkTt (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-U0" = { expr = (eval [] (T.mkU T.mkLevelZero)).tag; expected = "VU"; };
    "eval-U0-level" = {
      expr = (eval [] (T.mkU T.mkLevelZero)).level.tag;
      expected = "VLevelZero";
    };
    "eval-U1-level" = {
      expr = (eval [] (T.mkU (T.mkLevelSuc T.mkLevelZero))).level.tag;
      expected = "VLevelSuc";
    };
    "eval-U-level-max" = {
      expr = (eval [] (T.mkU (T.mkLevelMax T.mkLevelZero
        (T.mkLevelSuc T.mkLevelZero)))).level.tag;
      expected = "VLevelMax";
    };

    "eval-string" = { expr = (eval [] T.mkString).tag; expected = "VString"; };
    "eval-int" = { expr = (eval [] T.mkInt).tag; expected = "VInt"; };
    "eval-float" = { expr = (eval [] T.mkFloat).tag; expected = "VFloat"; };
    "eval-attrs" = { expr = (eval [] T.mkAttrs).tag; expected = "VAttrs"; };
    "eval-path" = { expr = (eval [] T.mkPath).tag; expected = "VPath"; };
    "eval-function" = { expr = (eval [] T.mkFunction).tag; expected = "VFunction"; };
    "eval-any" = { expr = (eval [] T.mkAny).tag; expected = "VAny"; };
    "eval-string-lit" = { expr = (eval [] (T.mkStringLit "hello")).tag; expected = "VStringLit"; };
    "eval-string-lit-value" = { expr = (eval [] (T.mkStringLit "hello")).value; expected = "hello"; };
    "eval-int-lit" = { expr = (eval [] (T.mkIntLit 42)).tag; expected = "VIntLit"; };
    "eval-int-lit-value" = { expr = (eval [] (T.mkIntLit 42)).value; expected = 42; };
    "eval-float-lit" = { expr = (eval [] (T.mkFloatLit 3.14)).tag; expected = "VFloatLit"; };
    "eval-float-lit-value" = { expr = (eval [] (T.mkFloatLit 3.14)).value; expected = 3.14; };
    "eval-attrs-lit" = { expr = (eval [] T.mkAttrsLit).tag; expected = "VAttrsLit"; };
    "eval-path-lit" = { expr = (eval [] T.mkPathLit).tag; expected = "VPathLit"; };
    "eval-fn-lit" = { expr = (eval [] T.mkFnLit).tag; expected = "VFnLit"; };
    "eval-any-lit" = { expr = (eval [] T.mkAnyLit).tag; expected = "VAnyLit"; };

    "instantiate-identity" = {
      expr = (instantiate (mkClosure [] (T.mkVar 0)) vTt).tag;
      expected = "VTt";
    };
    "instantiate-const" = {
      expr = (instantiate (mkClosure [ vTt ] (T.mkVar 1)) vUnit).tag;
      expected = "VTt";
    };

    "eval-desc" = { expr = (eval [] (T.mkDesc T.mkLevelZero T.mkUnit)).tag; expected = "VDesc"; };
    "eval-desc-ret" = { expr = (descViewOf encRet).idx; expected = 0; };
    "eval-desc-arg" = {
      expr = (descViewOf encArg).idx;
      expected = 1;
    };
    "eval-desc-arg-sort" = {
      expr = (descViewOf encArg).sTy.tag;
      expected = "VMu";
    };
    "eval-desc-arg-level-one-sort" = {
      expr = (descViewOf encArg1).sTy.tag;
      expected = "VU";
    };
    "eval-desc-rec" = {
      expr = (descViewOf encRec).idx;
      expected = 2;
    };
    "eval-desc-pi" = {
      expr = (descViewOf encPi).idx;
      expected = 3;
    };
    "eval-desc-pi-S" = {
      expr = (descViewOf encPi).sTy.tag;
      expected = "VMu";
    };
    "eval-desc-pi-D" = {
      expr = (self.descView (descViewOf encPi).sub).idx;
      expected = 0;
    };
    "eval-mu" = {
      expr = (eval [] (T.mkMu T.mkUnit encRet T.mkTt)).tag;
      expected = "VMu";
    };
    "eval-desc-con" = {
      expr = (eval [] (T.mkDescCon encRet T.mkTt T.mkBootRefl)).tag;
      expected = "VDescCon";
    };
    "eval-generated-list-5000" = {
      expr = let
        bigList = builtins.foldl' (acc: _:
          H.cons H.nat H.zero acc
        ) (H.nil H.nat) (builtins.genList (x: x) 5000);
      in (eval [] (H.elab bigList)).tag;
      expected = "VDescCon";
    };
    "eval-desc-ind-stuck" = {
      # desc-ind on a neutral scrutinee produces VNe
      expr = (eval [ (freshVar 0) ] (T.mkDescInd encRet
        (T.mkVar 0) (T.mkVar 0) T.mkTt (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # interp-d / all-d / everywhere-d Tm dispatch.
    "eval-interp-d-ret" = {
      # interpD 0 Unit (descRet tt) (λ_:Unit. Unit) tt = Lift 0 0 _ (Eq Unit tt tt) ≡ Eq Unit tt tt.
      expr = (eval [] (T.mkInterpD T.mkLevelZero T.mkUnit
        encRet
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).tag;
      expected = "VBootEq";
    };
    "eval-interp-d-stuck" = {
      # interpD on a stuck D produces VNe with EInterpD frame.
      expr = (eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkVar 0) (T.mkLam "_" T.mkUnit T.mkUnit) T.mkTt)).tag;
      expected = "VNe";
    };
    "eval-interp-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
          (T.mkVar 0) (T.mkLam "_" T.mkUnit T.mkUnit) T.mkTt);
      in (builtins.head r.spine).tag;
      expected = "EInterpD";
    };
    "eval-all-d-ret" = {
      # allD 0 Unit (descRet tt) 0 X M tt refl = Lift 0 0 _ Unit ≡ Unit.
      expr = (eval [] (T.mkAllD T.mkLevelZero T.mkUnit
        encRet T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
        T.mkTt T.mkBootRefl)).tag;
      expected = "VUnit";
    };
    "eval-all-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkAllD T.mkLevelZero T.mkUnit
          (T.mkVar 0) T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkUnit)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
          T.mkTt T.mkBootRefl);
      in (builtins.head r.spine).tag;
      expected = "EAllD";
    };
    "eval-everywhere-d-ret" = {
      # everywhereD 0 Unit (descRet tt) 0 X M ih tt refl
      #   = liftIntro 0 0 refl Unit tt ≡ tt.
      expr = (eval [] (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encRet T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit (T.mkU T.mkLevelZero)))
        T.mkTt T.mkBootRefl)).tag;
      expected = "VTt";
    };
    "eval-everywhere-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkEverywhereD T.mkLevelZero T.mkUnit
          (T.mkVar 0) T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkUnit)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
          (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit (T.mkU T.mkLevelZero)))
          T.mkTt T.mkBootRefl);
      in (builtins.head r.spine).tag;
      expected = "EEverywhereD";
    };

    "eval-desc-ind-ret-con" = {
      # ind (ret tt) P (λi d ih. tt) tt (con tt refl) = tt
      expr = let
        D = encRet;
        P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
        step = T.mkLam "i" T.mkUnit
          (T.mkLam "d" T.mkUnit
            (T.mkLam "ih" T.mkUnit T.mkTt));
        scrut = T.mkDescCon D T.mkTt T.mkBootRefl;
      in (eval [] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VTt";
    };
    "eval-desc-ind-arg-con" = {
      # D = arg Nat (λ_. ret tt), ind D P step tt (con tt (zero, refl)) = tt
      expr = let
        D = encArg;
        P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
        step = T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkU T.mkLevelZero)
            (T.mkLam "ih" T.mkUnit T.mkTt));
        scrut = T.mkDescCon D T.mkTt (T.mkPair (H.elab H.zero) T.mkBootRefl);
      in (eval [] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VTt";
    };

    # Lift primitive — type-former, introducer, eliminator.
    "eval-lift-idempotent" = {
      # Lift l l _ A ≡ A — load-bearing backward-compat at homogeneous
      # levels. Both levels mkLevelZero, so convLevel fires and the
      # smart constructor returns A directly.
      expr = (eval [] (T.mkLift T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit)).tag;
      expected = "VUnit";
    };
    "eval-lift-distinct-levels" = {
      # 0 < 1: convLevel rejects, vLiftF falls through to constructor.
      expr = (eval [] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkBootRefl T.mkUnit)).tag;
      expected = "VLift";
    };
    "eval-lift-distinct-levels-A" = {
      expr = (eval [] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkBootRefl T.mkUnit)).A.tag;
      expected = "VUnit";
    };
    "eval-lift-composition" = {
      # Lift 0 2 _ (Lift 0 1 _ Unit) collapses to Lift 0 2 _ Unit by
      # the inner-Lift composition rule (witness combined into vBootRefl).
      expr = let
        inner = T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit;
        outer = T.mkLift T.mkLevelZero
          (T.mkLevelSuc (T.mkLevelSuc T.mkLevelZero))
          T.mkBootRefl inner;
      in (eval [] outer).A.tag;
      # Composition collapses A to the deepest underlying type (Unit).
      expected = "VUnit";
    };

    "eval-lift-intro-idempotent" = {
      # lift l l _ A a ≡ a (η-collapse on idempotent Lift)
      expr = (eval [] (T.mkLiftIntro T.mkLevelZero T.mkLevelZero T.mkBootRefl
        T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };
    "eval-lift-intro-distinct-levels" = {
      # 0 < 1: builds a VLiftIntro cell.
      expr = (eval [] (T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkBootRefl T.mkUnit T.mkTt)).tag;
      expected = "VLiftIntro";
    };

    "eval-lift-elim-idempotent" = {
      # lower l l _ A x ≡ x (idempotent at l=m)
      expr = (eval [] (T.mkLiftElim T.mkLevelZero T.mkLevelZero T.mkBootRefl
        T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };
    "eval-lift-elim-beta" = {
      # lower (lift a) → a
      expr = let
        inner = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit T.mkTt;
        outer = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit inner;
      in (eval [] outer).tag;
      expected = "VTt";
    };
    "eval-lift-elim-stuck" = {
      # lower on a neutral produces VNe with ELiftElim spine entry.
      expr = (eval [ (freshVar 0) ]
        (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit (T.mkVar 0))).tag;
      expected = "VNe";
    };
    "eval-lift-elim-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ]
          (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
            T.mkBootRefl T.mkUnit (T.mkVar 0));
      in (builtins.elemAt r.spine 0).tag;
      expected = "ELiftElim";
    };

    "eval-lift-intro-eta-stuck" = {
      # lift (lower x) on a stuck `x` η-reduces by dropping the
      # trailing ELiftElim from the spine.
      expr = let
        lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit (T.mkVar 0);
        wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit lowerd;
      in (eval [ (freshVar 0) ] wrapped).tag;
      expected = "VNe";
    };
    "eval-lift-intro-eta-spine-empty" = {
      # After η, the only spine entry (the ELiftElim) is gone.
      expr = let
        lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit (T.mkVar 0);
        wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl T.mkUnit lowerd;
      in (eval [ (freshVar 0) ] wrapped).spine;
      expected = [];
    };

    # `desc-desc-app` eval rule stamps `_canonRef = { id; I; L; }` on
    # the outer Val produced by applying `descDescVal` at `(I, L)`.
    "eval-descDescApp-has-canonRef" = {
      expr = (eval [] (T.mkDescDescApp T.mkUnit T.mkLevelZero)) ? _canonRef;
      expected = true;
    };
    "eval-descDescApp-canonRef-id" = {
      expr = (eval [] (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.id;
      expected = "descDesc";
    };
    "eval-descDescApp-canonRef-I" = {
      expr = (eval [] (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.I.tag;
      expected = "VUnit";
    };
    "eval-descDescApp-canonRef-L" = {
      expr = (eval [] (T.mkDescDescApp T.mkUnit (T.mkLevelSuc T.mkLevelZero)))._canonRef.L.tag;
      expected = "VLevelSuc";
    };
  };
}
