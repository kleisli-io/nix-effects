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
    vBool vTrue vFalse vList vNil vCons
    vUnit vTt vVoid vSum vInl vInr vEq vRefl vU vNe
    vDesc vDescRet vDescArg vDescRec vDescPi vDescPlus vMu vDescCon
    vString vInt vFloat vAttrs vPath vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit
    eApp eFst eSnd eNatElim eBoolElim eListElim eAbsurd eSumElim eJ eStrEq;
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

    vBoolElim = motive: onTrue: onFalse: scrut:
      if scrut.tag == "VTrue" then onTrue
      else if scrut.tag == "VFalse" then onFalse
      else if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eBoolElim motive onTrue onFalse) ])
      else throw "tc: vBoolElim on non-bool (tag=${scrut.tag})";

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

    vAbsurd = type: scrut:
      if scrut.tag == "VNe" then
        vNe scrut.level (scrut.spine ++ [ (eAbsurd type) ])
      else throw "tc: vAbsurd on non-neutral (tag=${scrut.tag})";

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

      else if t == "bool" then vBool
      else if t == "true" then vTrue
      else if t == "false" then vFalse
      else if t == "bool-elim" then
        self.vBoolElim (ev tm.motive) (ev tm.onTrue) (ev tm.onFalse) (ev tm.scrut)

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

      else if t == "void" then vVoid
      else if t == "absurd" then self.vAbsurd (ev tm.type) (ev tm.term)

      else if t == "sum" then vSum (ev tm.left) (ev tm.right)
      else if t == "inl" then vInl (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "inr" then vInr (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "sum-elim" then
        self.vSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
          (ev tm.onLeft) (ev tm.onRight) (ev tm.scrut)

      else if t == "eq" then vEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
      else if t == "refl" then vRefl
      else if t == "j" then
        self.vJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
          (ev tm.base) (ev tm.rhs) (ev tm.eq)

      # Descriptions
      else if t == "desc" then vDesc (ev tm.I)
      else if t == "desc-ret" then vDescRet (ev tm.j)
      else if t == "desc-arg" then vDescArg (ev tm.S) (mkClosure env tm.T)
      else if t == "desc-rec" then vDescRec (ev tm.j) (ev tm.D)
      else if t == "desc-pi" then vDescPi (ev tm.S) (ev tm.f) (ev tm.D)
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
          # carries the recursive summand.
          classify =
            if dVal.tag != "VDescPlus" then null
            else
              let pA = self.linearProfileF f dVal.A;
                  pB = self.linearProfileF f dVal.B;
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
        self.vDescElimF f (ev tm.motive) (ev tm.onRet) (ev tm.onArg)
          (ev tm.onRec) (ev tm.onPi) (ev tm.onPlus) (ev tm.scrut)

      else if t == "U" then vU tm.level

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
  };

  tests = let
    T = fx.tc.term;
    inherit (val) freshVar;
    inherit (self) eval evalF instantiate;

    succN = n: if n == 0 then T.mkZero else T.mkSucc (succN (n - 1));
    idTm = T.mkLam "x" T.mkNat (T.mkVar 0);
    appIdZero = T.mkApp idTm T.mkZero;
  in {
    "eval-var-0" = { expr = (eval [ vZero vTrue ] (T.mkVar 0)).tag; expected = "VZero"; };
    "eval-var-1" = { expr = (eval [ vZero vTrue ] (T.mkVar 1)).tag; expected = "VTrue"; };

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

    "eval-sigma" = { expr = (eval [] (T.mkSigma "x" T.mkNat T.mkBool)).tag; expected = "VSigma"; };
    "eval-pair" = { expr = (eval [] (T.mkPair T.mkZero T.mkTrue)).tag; expected = "VPair"; };
    "eval-fst" = {
      expr = (eval [] (T.mkFst (T.mkPair T.mkZero T.mkTrue))).tag;
      expected = "VZero";
    };
    "eval-snd" = {
      expr = (eval [] (T.mkSnd (T.mkPair T.mkZero T.mkTrue))).tag;
      expected = "VTrue";
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
          r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat (T.mkU 0)) T.mkZero stepTm (T.mkSucc T.mkZero));
        in r.tag;
      expected = "VSucc";
    };

    "eval-nat-elim-stuck" = {
      expr = (eval [ (freshVar 0) vNat vZero (freshVar 3) ]
        (T.mkNatElim (T.mkVar 1) (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-bool" = { expr = (eval [] T.mkBool).tag; expected = "VBool"; };
    "eval-true" = { expr = (eval [] T.mkTrue).tag; expected = "VTrue"; };
    "eval-false" = { expr = (eval [] T.mkFalse).tag; expected = "VFalse"; };
    "eval-bool-elim-true" = {
      expr = (eval [] (T.mkBoolElim (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkTrue)).tag;
      expected = "VZero";
    };
    "eval-bool-elim-false" = {
      expr = (eval [] (T.mkBoolElim (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkFalse)).tag;
      expected = "VSucc";
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

    "eval-void" = { expr = (eval [] T.mkVoid).tag; expected = "VVoid"; };
    "eval-absurd-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkAbsurd T.mkNat (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-sum" = { expr = (eval [] (T.mkSum T.mkNat T.mkBool)).tag; expected = "VSum"; };
    "eval-inl" = { expr = (eval [] (T.mkInl T.mkNat T.mkBool T.mkZero)).tag; expected = "VInl"; };
    "eval-inr" = { expr = (eval [] (T.mkInr T.mkNat T.mkBool T.mkTrue)).tag; expected = "VInr"; };
    "eval-sum-elim-inl" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkBool T.mkZero)
        (T.mkInl T.mkNat T.mkBool (T.mkSucc T.mkZero)))).tag;
      expected = "VSucc";
    };
    "eval-sum-elim-inr" = {
      expr = (eval [] (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "y" T.mkBool T.mkZero)
        (T.mkInr T.mkNat T.mkBool T.mkTrue))).tag;
      expected = "VZero";
    };

    "eval-eq" = { expr = (eval [] (T.mkEq T.mkNat T.mkZero T.mkZero)).tag; expected = "VEq"; };
    "eval-refl" = { expr = (eval [] T.mkRefl).tag; expected = "VRefl"; };
    "eval-j-refl" = {
      # J(Nat, 0, P, base, 0, refl) = base
      expr = (eval [ vNat vZero (freshVar 2) vZero vZero ]
        (T.mkJ T.mkNat T.mkZero (T.mkVar 2) (T.mkVar 3) T.mkZero T.mkRefl)).tag;
      expected = "VZero";
    };
    "eval-j-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 0)) (T.mkU 0)))
        (T.mkU 0) T.mkZero (T.mkVar 0))).tag;
      expected = "VNe";
    };

    "eval-U0" = { expr = (eval [] (T.mkU 0)).tag; expected = "VU"; };
    "eval-U0-level" = { expr = (eval [] (T.mkU 0)).level; expected = 0; };
    "eval-U1-level" = { expr = (eval [] (T.mkU 1)).level; expected = 1; };

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
      expr = (instantiate (mkClosure [ vTrue ] (T.mkVar 1)) vZero).tag;
      expected = "VTrue";
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

    "eval-desc" = { expr = (eval [] (T.mkDesc T.mkUnit)).tag; expected = "VDesc"; };
    "eval-desc-ret" = { expr = (eval [] (T.mkDescRet T.mkTt)).tag; expected = "VDescRet"; };
    "eval-desc-arg" = {
      expr = (eval [] (T.mkDescArg T.mkBool
        (T.mkLam "_" T.mkBool (T.mkDescRet T.mkTt)))).tag;
      expected = "VDescArg";
    };
    "eval-desc-rec" = {
      expr = (eval [] (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))).tag;
      expected = "VDescRec";
    };
    "eval-desc-pi" = {
      expr = (eval [] (T.mkDescPi T.mkBool
        (T.mkLam "_" T.mkBool T.mkTt) (T.mkDescRet T.mkTt))).tag;
      expected = "VDescPi";
    };
    "eval-desc-pi-S" = {
      expr = (eval [] (T.mkDescPi T.mkBool
        (T.mkLam "_" T.mkBool T.mkTt) (T.mkDescRet T.mkTt))).S.tag;
      expected = "VBool";
    };
    "eval-desc-pi-D" = {
      expr = (eval [] (T.mkDescPi T.mkBool
        (T.mkLam "_" T.mkBool T.mkTt) (T.mkDescRet T.mkTt))).D.tag;
      expected = "VDescRet";
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
      expr = (eval [] (T.mkDescElim
        (T.mkLam "_" (T.mkDesc T.mkUnit) (T.mkU 0))
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit
        (T.mkDescRet T.mkTt))).tag;
      expected = "VUnit";
    };
    "eval-desc-elim-stuck" = {
      # descElim on a neutral scrutinee produces VNe with EDescElim frame
      expr = (eval [ (freshVar 0) ] (T.mkDescElim
        T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkUnit T.mkUnit (T.mkVar 0))).tag;
      expected = "VNe";
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
      # D = arg Bool (λ_. ret tt), ind D P step tt (con tt (false, refl)) = 0
      expr = let
        D = T.mkDescArg T.mkBool
          (T.mkLam "_" T.mkBool (T.mkDescRet T.mkTt));
        P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkNat);
        step = T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkU 0)
            (T.mkLam "ih" T.mkUnit T.mkZero));
        scrut = T.mkDescCon D T.mkTt (T.mkPair T.mkFalse T.mkRefl);
      in (eval [] (T.mkDescInd D P step T.mkTt scrut)).tag;
      expected = "VZero";
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
