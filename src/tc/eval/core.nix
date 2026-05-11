# Evaluator core: value operations, eliminators, and the main `evalF`.
#
# Pure evaluator interpreting kernel terms in an environment of values
# (§4, §9). Zero effect-system imports — part of the trusted computing
# base.
#
# Fuel-threaded: each `evalF` call decrements a counter; exhaustion
# throws "normalization budget exceeded". Default budget is 10M steps
# (§9). Trampolines `vNatElim`, `vListElim`, `succ`, `cons`, and the
# `desc-con` chain via `builtins.genericClosure` to bound stack depth
# on deep structures (§11.3).
#
# Description operations (`vDescIndF`, `vDescElimF`, `linearProfileF`)
# live in the sibling `desc.nix`; `evalF` dispatches to them through
# `self`.
{ self, fx, ... }:

let
  val = fx.tc.value;
  inherit (val) mkClosure
    vLam vPi vSigma vPair vNat vZero vSucc
    vList vNil vCons
    vUnit vTt vSum vInl vInr vEq vRefl vFunext vU vNe
    vSquash vSquashIntro
    vLevel vLevelZero vLevelSuc vLevelMax
    vLift vLiftIntro
    vDesc vDescRet vDescArg vDescRec vDescPi vDescPlus vMu vDescCon
    vString vInt vFloat vAttrs vPath vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit
    eApp eFst eSnd eNatElim eListElim eSumElim eJ eStrEq eLiftElim eNatToLevel
    eSquashElim;

  # Cached `U(0)` value. `mkU mkLevelZero` produces a term whose `level` is the
  # `level-zero` singleton; evaluating under the U-case returns this
  # sentinel directly — no fuel decrement, no dispatch, no allocation.
  vUZero = vU vLevelZero;
in {
  scope = {
    defaultFuel = 10000000;

    instantiateF = fuel: cl: arg: self.evalF fuel ([ arg ] ++ cl.env) cl.body;

    vAppF = fuel: fn: arg:
      if fn.tag == "VLam" then self.instantiateF fuel fn.closure arg
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

    # vNatElim — trampolined via genericClosure for large naturals.
    vNatElimF = fuel: motive: base: step: scrut:
      if scrut.tag == "VZero" then base
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eNatElim motive base step) ])
      else if scrut.tag == "VSucc" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = scrut; }];
            operator = item:
              if item.val.tag == "VSucc"
              then [{ key = item.key + 1; val = item.val.pred; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
          baseResult = self.vNatElimF fuel motive base step last.val;
          n = builtins.length chain - 1;
          # Thread fuel through fold: each step application decrements fuel
          result = builtins.foldl' (state: i:
            if state.fuel <= 0 then throw "normalization budget exceeded"
            else let
              item = builtins.elemAt chain (n - i);
              predVal = item.val.pred;
              f = state.fuel;
              applied = self.vAppF f (self.vAppF f step predVal) state.acc;
            in { acc = applied; fuel = f - 1; }
          ) { acc = baseResult; inherit fuel; } (builtins.genList (i: i + 1) n);
        in result.acc
      else throw "tc: vNatElim on non-nat (tag=${scrut.tag})";

    # vNatToLevelF — asymmetric Nat→Level bridge. Reduces structurally
    # on closed Nats (`zero → vLevelZero`, `suc^n zero → vLevelSuc^n
    # vLevelZero`); records `eNatToLevel` on a stuck Nat-typed neutral.
    # Trampolined via genericClosure for deep Nats, mirroring vNatElimF.
    vNatToLevelF = fuel: scrut:
      if scrut.tag == "VZero" then vLevelZero
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ eNatToLevel ])
      else if scrut.tag == "VSucc" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = scrut; }];
            operator = item:
              if item.val.tag == "VSucc"
              then [{ key = item.key + 1; val = item.val.pred; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
          baseResult = self.vNatToLevelF fuel last.val;
          n = builtins.length chain - 1;
        in if n > fuel then throw "normalization budget exceeded"
        else builtins.foldl' (acc: _: vLevelSuc acc)
          baseResult (builtins.genList (x: x) n)
      else throw "tc: vNatToLevel on non-nat (tag=${scrut.tag})";

    # vStrEq — string equality primitive.
    # Both VStringLit → plus-encoded VDescCon true/false. Neutral → spine.
    # StrEq is symmetric, so we canonicalize neutral-first for the spine.
    vStrEq = lhs: rhs:
      let
        boolDescV = vDescPlus (vDescRet vTt) (vDescRet vTt);
        eqTtV = vEq vUnit vTt vTt;
        vBoolTrue = vDescCon boolDescV vTt (vInl eqTtV eqTtV vRefl);
        vBoolFalse = vDescCon boolDescV vTt (vInr eqTtV eqTtV vRefl);
      in
      if lhs.tag == "VStringLit" && rhs.tag == "VStringLit" then
        if lhs.value == rhs.value then vBoolTrue else vBoolFalse
      else if lhs.tag == "VNe" then
        vNe lhs.level (lhs.spine ++ [ (eStrEq rhs) ])
      else if rhs.tag == "VNe" then
        vNe rhs.level (rhs.spine ++ [ (eStrEq lhs) ])
      else throw "tc: vStrEq on non-string (tags=${lhs.tag}, ${rhs.tag})";

    # vListElim — trampolined like vNatElim for large lists.
    vListElimF = fuel: elemTy: motive: onNil: onCons: scrut:
      if scrut.tag == "VNil" then onNil
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eListElim elemTy motive onNil onCons) ])
      else if scrut.tag == "VCons" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = scrut; }];
            operator = item:
              if item.val.tag == "VCons"
              then [{ key = item.key + 1; val = item.val.tail; }]
              else [];
          };
          last = builtins.elemAt chain (builtins.length chain - 1);
          baseResult = self.vListElimF fuel elemTy motive onNil onCons last.val;
          n = builtins.length chain - 1;
          # Thread fuel through fold: each step application decrements fuel
          result = builtins.foldl' (state: i:
            if state.fuel <= 0 then throw "normalization budget exceeded"
            else let
              item = builtins.elemAt chain (n - i);
              h = item.val.head;
              t = item.val.tail;
              f = state.fuel;
              applied = self.vAppF f (self.vAppF f (self.vAppF f onCons h) t) state.acc;
            in { acc = applied; fuel = f - 1; }
          ) { acc = baseResult; inherit fuel; } (builtins.genList (i: i + 1) n);
        in result.acc
      else throw "tc: vListElim on non-list (tag=${scrut.tag})";

    vSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
      if scrut.tag == "VInl" then self.vAppF fuel onLeft scrut.val
      else if scrut.tag == "VInr" then self.vAppF fuel onRight scrut.val
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eSumElim left right motive onLeft onRight) ])
      else throw "tc: vSumElim on non-sum (tag=${scrut.tag})";

    # J computation: J(A, a, P, pr, b, refl) = pr.
    # When eq=VRefl, the checker has verified b≡a, so `rhs` is unused.
    # When eq is neutral, `rhs` is preserved in the EJ spine frame for quotation.
    vJ = type: lhs: motive: base: rhs: eq:
      if eq.tag == "VRefl" then base
      else if eq.tag == "VNe" then
        vNe eq.level (eq.spine ++ [ (eJ type lhs motive base rhs) ])
      else throw "tc: vJ on non-eq (tag=${eq.tag})";

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
    # is irrelevant — emit `vRefl` on collapse since both bound
    # conditions hold by transitivity.
    vLiftF = l: m: eq: A:
      if fx.tc.conv.convLevel l m then A
      else if A.tag == "VLift"
      then vLift A.l m vRefl A.A
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
      else if t == "ann" then ev tm.term

      else if t == "pi" then vPi tm.name (ev tm.domain) (mkClosure env tm.codomain)
      else if t == "lam" then vLam tm.name (ev tm.domain) (mkClosure env tm.body)
      else if t == "app" then self.vAppF f (ev tm.fn) (ev tm.arg)

      else if t == "sigma" then vSigma tm.name (ev tm.fst) (mkClosure env tm.snd)
      else if t == "pair" then vPair (ev tm.fst) (ev tm.snd)
      else if t == "fst" then self.vFst (ev tm.pair)
      else if t == "snd" then self.vSnd (ev tm.pair)

      else if t == "nat" then vNat
      else if t == "zero" then vZero
      # succ — trampolined for deep naturals (S^5000+)
      else if t == "succ" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "succ"
              then [{ key = item.key + 1; val = item.val.pred; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in if n > f then throw "normalization budget exceeded"
        else builtins.foldl' (acc: _: vSucc acc)
          (self.evalF (f - n) env base)
          (builtins.genList (x: x) n)
      else if t == "nat-elim" then
        self.vNatElimF f (ev tm.motive) (ev tm.base) (ev tm.step) (ev tm.scrut)

      else if t == "list" then vList (ev tm.elem)
      else if t == "nil" then vNil (ev tm.elem)
      # cons — trampolined for deep lists (5000+ elements).
      # Fuel: deduct n for chain length, thread remaining through fold (§9.5)
      else if t == "cons" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "cons"
              then [{ key = item.key + 1; val = item.val.tail; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in if n > f then throw "normalization budget exceeded"
        else let
          result = builtins.foldl' (state: i:
            if state.fuel <= 0 then throw "normalization budget exceeded"
            else let
              node = (builtins.elemAt chain (n - 1 - i)).val;
              ef = self.evalF state.fuel env;
            in { acc = vCons (ef node.elem) (ef node.head) state.acc; fuel = state.fuel - 1; }
          ) { acc = self.evalF (f - n) env base; fuel = f - n; } (builtins.genList (x: x) n);
        in result.acc
      else if t == "list-elim" then
        self.vListElimF f (ev tm.elem) (ev tm.motive) (ev tm.nil) (ev tm.cons) (ev tm.scrut)

      else if t == "unit" then vUnit
      else if t == "tt" then vTt

      else if t == "sum" then vSum (ev tm.left) (ev tm.right)
      else if t == "inl" then vInl (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "inr" then vInr (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "sum-elim" then
        self.vSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
          (ev tm.onLeft) (ev tm.onRight) (ev tm.scrut)

      else if t == "eq" then vEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
      else if t == "refl" then vRefl
      else if t == "funext" then vFunext
      else if t == "j" then
        self.vJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
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
      else if t == "desc-ret" then vDescRet (ev tm.j)
      # Level-zero fast-path at the new `k` slot: when `tm.k` is the
      # `level-zero` singleton (the overwhelmingly common shape for
      # prelude descriptions), skip eval and pass `vLevelZero` directly.
      else if t == "desc-arg" then
        vDescArg
          (if tm.k.tag == "level-zero" then vLevelZero else ev tm.k)
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (ev tm.S) (ev tm.eq) (mkClosure env tm.T)
      else if t == "desc-rec" then vDescRec (ev tm.j) (ev tm.D)
      else if t == "desc-pi" then
        vDescPi
          (if tm.k.tag == "level-zero" then vLevelZero else ev tm.k)
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (ev tm.S) (ev tm.eq) (ev tm.f) (ev tm.D)
      else if t == "desc-plus" then vDescPlus (ev tm.A) (ev tm.B)
      else if t == "mu" then vMu (ev tm.I) (ev tm.D) (ev tm.i)
      # desc-con — trampolined for deep recursive chains (5000+).
      # Peels a homogeneous desc-con chain along its single recursive
      # position when D = plus A B with exactly one of A, B linear-
      # recursive (a descArg-chain ending in `descRec descRet`). The
      # recursive summand drives the chain; its injection side picks
      # the payload tag (`inl` when A is recursive, `inr` when B is).
      #
      # Payload at each layer is `inl/inr lTy rTy (pair f_0 … (pair REC refl))`
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
          # carries the recursive summand. Handles both primitive
          # `VDescPlus` and encoded `VDescCon` (idx=4 plus summand of
          # descDesc); for the encoded case the payload's `(A_enc,
          # (B_enc, refl))` triple supplies the two sub-descriptions.
          plusSides =
            if dVal.tag == "VDescPlus" then { A = dVal.A; B = dVal.B; }
            else if dVal.tag == "VDescCon" then
              let info = self.decodeDescCaseF dVal; in
              if info == null || info.idx != 4 then null
              else { A = info.payload.fst; B = info.payload.snd.fst; }
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
              collect = i: p: acc:
                if i == nFields then
                  if p.tag != "pair" then null
                  else if p.snd.tag != "refl" then null
                  else if p.fst.tag != "desc-con" then null
                  else { heads = acc; tail = p.fst; }
                else
                  if p.tag != "pair" then null
                  else collect (i + 1) p.snd (acc ++ [p.fst]);
            in collect 0 inner [];
          walkPayload = payload:
            if classify == null then null
            else if payload.tag != classify.side then null
            else
              let inner = collectPairs payload.term; in
              if inner == null then null
              else inner // { lTm = payload.left; rTm = payload.right; };
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
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              let peeled = peel item.val; in
              if peeled == null then []
              else [{ key = item.key + 1; val = peeled.tail; }];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
          topPeel = if n >= 1 then peel tm else null;
          lVal = if topPeel == null then null else self.evalF (f - n) env topPeel.lTm;
          rVal = if topPeel == null then null else self.evalF (f - n) env topPeel.rTm;
        in if n > f then throw "normalization budget exceeded"
        else let
          baseVal = vDescCon dVal
            (self.evalF (f - n) env base.i)
            (self.evalF (f - n) env base.d);
          buildInner = hs: innerTail:
            if hs == [] then innerTail
            else vPair (builtins.head hs) (buildInner (builtins.tail hs) innerTail);
          wrapPayload = innerVal:
            if classify.side == "inl" then vInl lVal rVal innerVal
            else vInr lVal rVal innerVal;
        in builtins.foldl' (acc: i:
          let
            layer = (builtins.elemAt chain (n - 1 - i)).val;
            peeled = peel layer;
            heads = peeled.heads;
            headVals = map (h: self.evalF (f - n + i) env h) heads;
            iLayerVal = self.evalF (f - n + i) env layer.i;
          in vDescCon dVal iLayerVal
               (wrapPayload (buildInner headVals (vPair acc vRefl)))
        ) baseVal (builtins.genList (x: x) n)
      else if t == "desc-ind" then
        self.vDescIndF f (ev tm.D) (ev tm.motive) (ev tm.step) (ev tm.i) (ev tm.scrut)
      else if t == "desc-elim" then
        self.vDescElimF f (ev tm.k) (ev tm.motive) (ev tm.onRet) (ev tm.onArg)
          (ev tm.onRec) (ev tm.onPi) (ev tm.onPlus) (ev tm.scrut)

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
      else if t == "nat-to-level" then self.vNatToLevelF f (ev tm.n)

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
    vNatElim = self.vNatElimF self.defaultFuel;
    vListElim = self.vListElimF self.defaultFuel;
    vSumElim = self.vSumElimF self.defaultFuel;
    vNatToLevel = self.vNatToLevelF self.defaultFuel;
    vSquashElim = self.vSquashElimF self.defaultFuel;
  };

  tests = let
    T = fx.tc.term;
    inherit (val) freshVar;
    inherit (self) eval evalF instantiate;

    succN = n: if n == 0 then T.mkZero else T.mkSucc (succN (n - 1));
    idTm = T.mkLam "x" T.mkNat (T.mkVar 0);
    appIdZero = T.mkApp idTm T.mkZero;
  in {
    "eval-var-0" = { expr = (eval [ vZero vTt ] (T.mkVar 0)).tag; expected = "VZero"; };
    "eval-var-1" = { expr = (eval [ vZero vTt ] (T.mkVar 1)).tag; expected = "VTt"; };

    "eval-let" = {
      expr = (eval [] (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0))).tag;
      expected = "VZero";
    };

    "eval-ann" = {
      expr = (eval [] (T.mkAnn T.mkZero T.mkNat)).tag;
      expected = "VZero";
    };

    "eval-lam" = { expr = (eval [] idTm).tag; expected = "VLam"; };
    "eval-pi" = { expr = (eval [] (T.mkPi "x" T.mkNat T.mkNat)).tag; expected = "VPi"; };
    "eval-app-beta" = {
      # (λx.x) 0 = 0
      expr = (eval [] appIdZero).tag;
      expected = "VZero";
    };
    "eval-app-stuck" = {
      # x 0 where x is a neutral at level 0
      expr = (eval [ (freshVar 0) ] (T.mkApp (T.mkVar 0) T.mkZero)).tag;
      expected = "VNe";
    };

    "eval-sigma" = { expr = (eval [] (T.mkSigma "x" T.mkNat T.mkUnit)).tag; expected = "VSigma"; };
    "eval-pair" = { expr = (eval [] (T.mkPair T.mkZero T.mkTt)).tag; expected = "VPair"; };
    "eval-fst" = {
      expr = (eval [] (T.mkFst (T.mkPair T.mkZero T.mkTt))).tag;
      expected = "VZero";
    };
    "eval-snd" = {
      expr = (eval [] (T.mkSnd (T.mkPair T.mkZero T.mkTt))).tag;
      expected = "VTt";
    };
    "eval-fst-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkFst (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-nat" = { expr = (eval [] T.mkNat).tag; expected = "VNat"; };
    "eval-zero" = { expr = (eval [] T.mkZero).tag; expected = "VZero"; };
    "eval-succ" = { expr = (eval [] (T.mkSucc T.mkZero)).tag; expected = "VSucc"; };
    "eval-succ-3" = {
      expr = (eval [] (succN 3)).pred.pred.pred.tag;
      expected = "VZero";
    };

    "eval-nat-elim-zero" = {
      expr = (eval [ vNat vZero (freshVar 2) ]
        (T.mkNatElim (T.mkVar 0) (T.mkVar 1) (T.mkVar 2) T.mkZero)).tag;
      expected = "VZero";
    };

    "eval-nat-elim-succ1" = {
      expr =
        let
          stepTm = T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)));
          r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat (T.mkU T.mkLevelZero)) T.mkZero stepTm (T.mkSucc T.mkZero));
        in r.tag;
      expected = "VSucc";
    };

    "eval-nat-elim-stuck" = {
      expr = (eval [ (freshVar 0) vNat vZero (freshVar 3) ]
        (T.mkNatElim (T.mkVar 1) (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-list" = { expr = (eval [] (T.mkList T.mkNat)).tag; expected = "VList"; };
    "eval-nil" = { expr = (eval [] (T.mkNil T.mkNat)).tag; expected = "VNil"; };
    "eval-cons" = { expr = (eval [] (T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat))).tag; expected = "VCons"; };
    "eval-list-elim-nil" = {
      expr = (eval [] (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
        T.mkZero
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat) (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
        (T.mkNil T.mkNat))).tag;
      expected = "VZero";
    };

    "eval-unit" = { expr = (eval [] T.mkUnit).tag; expected = "VUnit"; };
    "eval-tt" = { expr = (eval [] T.mkTt).tag; expected = "VTt"; };

    "eval-sum" = { expr = (eval [] (T.mkSum T.mkNat T.mkUnit)).tag; expected = "VSum"; };
    "eval-inl" = { expr = (eval [] (T.mkInl T.mkNat T.mkUnit T.mkZero)).tag; expected = "VInl"; };
    "eval-inr" = { expr = (eval [] (T.mkInr T.mkNat T.mkUnit T.mkTt)).tag; expected = "VInr"; };
    "eval-sum-elim-inl" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkUnit
        (T.mkLam "s" (T.mkSum T.mkNat T.mkUnit) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkUnit T.mkZero)
        (T.mkInl T.mkNat T.mkUnit (T.mkSucc T.mkZero)))).tag;
      expected = "VSucc";
    };
    "eval-sum-elim-inr" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkUnit
        (T.mkLam "s" (T.mkSum T.mkNat T.mkUnit) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkUnit T.mkZero)
        (T.mkInr T.mkNat T.mkUnit T.mkTt))).tag;
      expected = "VZero";
    };

    "eval-eq" = { expr = (eval [] (T.mkEq T.mkNat T.mkZero T.mkZero)).tag; expected = "VEq"; };
    "eval-refl" = { expr = (eval [] T.mkRefl).tag; expected = "VRefl"; };
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
      # J(Nat, 0, P, base, 0, refl) = base
      expr = (eval [ vNat vZero (freshVar 2) vZero vZero ]
        (T.mkJ T.mkNat T.mkZero (T.mkVar 2) (T.mkVar 3) T.mkZero T.mkRefl)).tag;
      expected = "VZero";
    };
    "eval-j-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 0)) (T.mkU T.mkLevelZero)))
        (T.mkU T.mkLevelZero) T.mkZero (T.mkVar 0))).tag;
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
      expr = (instantiate (mkClosure [] (T.mkVar 0)) vZero).tag;
      expected = "VZero";
    };
    "instantiate-const" = {
      expr = (instantiate (mkClosure [ vTt ] (T.mkVar 1)) vZero).tag;
      expected = "VTt";
    };

    "fuel-exhaustion" = {
      # Low fuel on a term requiring many eval steps → throws
      expr = (builtins.tryEval (builtins.deepSeq
        (evalF 10 [] (T.mkNatElim
          (T.mkLam "n" T.mkNat T.mkNat)
          T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          (succN 100)))
        true)).success;
      expected = false;
    };
    "fuel-sufficient" = {
      # Default fuel handles moderate terms fine
      expr = (eval [] (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        (succN 100))).tag;
      expected = "VSucc";
    };

    "fuel-threading-nat-elim" = {
      expr = (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (T.mkNatElim
          (T.mkLam "n" T.mkNat T.mkNat)
          T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          (succN 200)))
        true)).success;
      expected = false;
    };
    "fuel-threading-list-elim" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (T.mkListElim T.mkNat
          (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
          T.mkZero
          (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
            (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
          (mkList 200)))
        true)).success;
      expected = false;
    };

    "fuel-threading-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (mkList 200))
        true)).success;
      expected = false;
    };
    "fuel-sufficient-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (eval [] (mkList 50)).tag;
      expected = "VCons";
    };

    "eval-desc" = { expr = (eval [] (T.mkDesc T.mkLevelZero T.mkUnit)).tag; expected = "VDesc"; };
    "eval-desc-ret" = { expr = (eval [] (T.mkDescRet T.mkTt)).tag; expected = "VDescRet"; };
    "eval-desc-arg" = {
      expr = (eval [] (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat (T.mkDescRet T.mkTt)))).tag;
      expected = "VDescArg";
    };
    "eval-desc-arg-k-zero" = {
      expr = (eval [] (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat (T.mkDescRet T.mkTt)))).k.tag;
      expected = "VLevelZero";
    };
    "eval-desc-arg-k-one" = {
      expr = (eval [] (T.mkDescArg (T.mkLevelSuc T.mkLevelZero) (T.mkLevelSuc T.mkLevelZero) T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat (T.mkDescRet T.mkTt)))).k.tag;
      expected = "VLevelSuc";
    };
    "eval-desc-rec" = {
      expr = (eval [] (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))).tag;
      expected = "VDescRec";
    };
    "eval-desc-pi" = {
      expr = (eval [] (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt))).tag;
      expected = "VDescPi";
    };
    "eval-desc-pi-S" = {
      expr = (eval [] (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt))).S.tag;
      expected = "VNat";
    };
    "eval-desc-pi-D" = {
      expr = (eval [] (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt))).D.tag;
      expected = "VDescRet";
    };
    "eval-desc-pi-k-zero" = {
      expr = (eval [] (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
        (T.mkLam "_" T.mkNat T.mkTt) (T.mkDescRet T.mkTt))).k.tag;
      expected = "VLevelZero";
    };
    "eval-mu" = {
      expr = (eval [] (T.mkMu T.mkUnit (T.mkDescRet T.mkTt) T.mkTt)).tag;
      expected = "VMu";
    };
    "eval-desc-con" = {
      expr = (eval [] (T.mkDescCon (T.mkDescRet T.mkTt) T.mkTt T.mkRefl)).tag;
      expected = "VDescCon";
    };
    "eval-desc-ind-stuck" = {
      # desc-ind on a neutral scrutinee produces VNe
      expr = (eval [ (freshVar 0) ] (T.mkDescInd (T.mkDescRet T.mkTt)
        (T.mkVar 0) (T.mkVar 0) T.mkTt (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-desc-elim-ret" = {
      # descElim on VDescRet applies onRet to j. With onRet = λ_:Unit. Unit and j=vTt, result is VUnit.
      expr = (eval [] (T.mkDescElim T.mkLevelZero
        (T.mkLam "_" (T.mkDesc T.mkLevelZero T.mkUnit) (T.mkU T.mkLevelZero))
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit
        (T.mkDescRet T.mkTt))).tag;
      expected = "VUnit";
    };
    "eval-desc-elim-stuck" = {
      # descElim on a neutral scrutinee produces VNe with EDescElim frame
      expr = (eval [ (freshVar 0) ] (T.mkDescElim T.mkLevelZero
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkUnit (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # interp-d / all-d / everywhere-d Tm dispatch.
    "eval-interp-d-ret" = {
      # interpD 0 Unit (descRet tt) (λ_:Unit. Nat) tt = Lift 0 0 _ (Eq Unit tt tt) ≡ Eq Unit tt tt.
      expr = (eval [] (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        (T.mkLam "_" T.mkUnit T.mkNat)
        T.mkTt)).tag;
      expected = "VEq";
    };
    "eval-interp-d-stuck" = {
      # interpD on a stuck D produces VNe with EInterpD frame.
      expr = (eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkVar 0) (T.mkLam "_" T.mkUnit T.mkNat) T.mkTt)).tag;
      expected = "VNe";
    };
    "eval-interp-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
          (T.mkVar 0) (T.mkLam "_" T.mkUnit T.mkNat) T.mkTt);
      in (builtins.head r.spine).tag;
      expected = "EInterpD";
    };
    "eval-all-d-ret" = {
      # allD 0 Unit (descRet tt) 0 X M tt refl = Lift 0 0 _ Unit ≡ Unit.
      expr = (eval [] (T.mkAllD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt) T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkNat)
        (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkNat (T.mkU T.mkLevelZero)))
        T.mkTt T.mkRefl)).tag;
      expected = "VUnit";
    };
    "eval-all-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkAllD T.mkLevelZero T.mkUnit
          (T.mkVar 0) T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkNat)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkNat (T.mkU T.mkLevelZero)))
          T.mkTt T.mkRefl);
      in (builtins.head r.spine).tag;
      expected = "EAllD";
    };
    "eval-everywhere-d-ret" = {
      # everywhereD 0 Unit (descRet tt) 0 X M ih tt refl
      #   = liftIntro 0 0 refl Unit tt ≡ tt.
      expr = (eval [] (T.mkEverywhereD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt) T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkNat)
        (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkNat (T.mkU T.mkLevelZero)))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkNat (T.mkU T.mkLevelZero)))
        T.mkTt T.mkRefl)).tag;
      expected = "VTt";
    };
    "eval-everywhere-d-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ] (T.mkEverywhereD T.mkLevelZero T.mkUnit
          (T.mkVar 0) T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkNat)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkNat (T.mkU T.mkLevelZero)))
          (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkNat (T.mkU T.mkLevelZero)))
          T.mkTt T.mkRefl);
      in (builtins.head r.spine).tag;
      expected = "EEverywhereD";
    };

    "eval-desc-ind-ret-con" = {
      # ind (ret tt) P (λi d ih. 0) tt (con tt refl) = 0
      expr = let
        D = T.mkDescRet T.mkTt;
        P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkNat);
        step = T.mkLam "i" T.mkUnit
          (T.mkLam "d" T.mkUnit
            (T.mkLam "ih" T.mkUnit T.mkZero));
        scrut = T.mkDescCon D T.mkTt T.mkRefl;
      in (eval [] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VZero";
    };
    "eval-desc-ind-arg-con" = {
      # D = arg Nat (λ_. ret tt), ind D P step tt (con tt (zero, refl)) = 0
      expr = let
        D = T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
          (T.mkLam "_" T.mkNat (T.mkDescRet T.mkTt));
        P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkNat);
        step = T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkU T.mkLevelZero)
            (T.mkLam "ih" T.mkUnit T.mkZero));
        scrut = T.mkDescCon D T.mkTt (T.mkPair T.mkZero T.mkRefl);
      in (eval [] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VZero";
    };

    # Lift primitive — type-former, introducer, eliminator.
    "eval-lift-idempotent" = {
      # Lift l l _ A ≡ A — load-bearing backward-compat at homogeneous
      # levels. Both levels mkLevelZero, so convLevel fires and the
      # smart constructor returns A directly.
      expr = (eval [] (T.mkLift T.mkLevelZero T.mkLevelZero T.mkRefl T.mkUnit)).tag;
      expected = "VUnit";
    };
    "eval-lift-distinct-levels" = {
      # 0 < 1: convLevel rejects, vLiftF falls through to constructor.
      expr = (eval [] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkRefl T.mkUnit)).tag;
      expected = "VLift";
    };
    "eval-lift-distinct-levels-A" = {
      expr = (eval [] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkRefl T.mkUnit)).A.tag;
      expected = "VUnit";
    };
    "eval-lift-composition" = {
      # Lift 0 2 _ (Lift 0 1 _ Unit) collapses to Lift 0 2 _ Unit by
      # the inner-Lift composition rule (witness combined into vRefl).
      expr = let
        inner = T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit;
        outer = T.mkLift T.mkLevelZero
          (T.mkLevelSuc (T.mkLevelSuc T.mkLevelZero))
          T.mkRefl inner;
      in (eval [] outer).A.tag;
      # Composition collapses A to the deepest underlying type (Unit).
      expected = "VUnit";
    };

    "eval-lift-intro-idempotent" = {
      # lift l l _ A a ≡ a (η-collapse on idempotent Lift)
      expr = (eval [] (T.mkLiftIntro T.mkLevelZero T.mkLevelZero T.mkRefl
        T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };
    "eval-lift-intro-distinct-levels" = {
      # 0 < 1: builds a VLiftIntro cell.
      expr = (eval [] (T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
        T.mkRefl T.mkUnit T.mkTt)).tag;
      expected = "VLiftIntro";
    };

    "eval-lift-elim-idempotent" = {
      # lower l l _ A x ≡ x (idempotent at l=m)
      expr = (eval [] (T.mkLiftElim T.mkLevelZero T.mkLevelZero T.mkRefl
        T.mkUnit T.mkTt)).tag;
      expected = "VTt";
    };
    "eval-lift-elim-beta" = {
      # lower (lift a) → a
      expr = let
        inner = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit T.mkTt;
        outer = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit inner;
      in (eval [] outer).tag;
      expected = "VTt";
    };
    "eval-lift-elim-stuck" = {
      # lower on a neutral produces VNe with ELiftElim spine entry.
      expr = (eval [ (freshVar 0) ]
        (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit (T.mkVar 0))).tag;
      expected = "VNe";
    };
    "eval-lift-elim-stuck-spine-tag" = {
      expr = let
        r = eval [ (freshVar 0) ]
          (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
            T.mkRefl T.mkUnit (T.mkVar 0));
      in (builtins.elemAt r.spine 0).tag;
      expected = "ELiftElim";
    };

    "eval-lift-intro-eta-stuck" = {
      # lift (lower x) on a stuck `x` η-reduces by dropping the
      # trailing ELiftElim from the spine.
      expr = let
        lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit (T.mkVar 0);
        wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit lowerd;
      in (eval [ (freshVar 0) ] wrapped).tag;
      expected = "VNe";
    };
    "eval-lift-intro-eta-spine-empty" = {
      # After η, the only spine entry (the ELiftElim) is gone.
      expr = let
        lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit (T.mkVar 0);
        wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkRefl T.mkUnit lowerd;
      in (eval [ (freshVar 0) ] wrapped).spine;
      expected = [];
    };

    "eval-nat-to-level-zero" = {
      expr = (eval [] (T.mkNatToLevel T.mkZero)).tag;
      expected = "VLevelZero";
    };
    "eval-nat-to-level-suc-zero" = {
      expr = (eval [] (T.mkNatToLevel (T.mkSucc T.mkZero))).tag;
      expected = "VLevelSuc";
    };
    "eval-nat-to-level-3-shape" = {
      # natToLevel 3 ≡ suc (suc (suc zero)) definitionally.
      expr = let
        n3 = T.mkSucc (T.mkSucc (T.mkSucc T.mkZero));
        v = eval [] (T.mkNatToLevel n3);
      in v.pred.pred.pred.tag;
      expected = "VLevelZero";
    };
    "eval-nat-to-level-stuck" = {
      # natToLevel (Var 0) leaves an ENatToLevel frame on a Nat-typed neutral.
      expr = (eval [ (freshVar 0) ] (T.mkNatToLevel (T.mkVar 0))).tag;
      expected = "VNe";
    };
    "eval-nat-to-level-stuck-spine-tag" = {
      expr = let
        v = eval [ (freshVar 0) ] (T.mkNatToLevel (T.mkVar 0));
      in (builtins.head v.spine).tag;
      expected = "ENatToLevel";
    };

    # §11.3 Stress tests (eval level)

    "stress-eval-10000" = {
      expr = let
        bigNat = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 10000);
      in (eval [] bigNat).tag;
      expected = "VSucc";
    };

    "stress-nat-elim-1000" = {
      expr = let
        nat1000 = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 1000);
        step = T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)));
        r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat T.mkNat) T.mkZero step nat1000);
      in r.tag;
      expected = "VSucc";
    };
  };
}
