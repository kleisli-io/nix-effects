# Type-checking kernel: Evaluator (eval)
#
# eval : Env -> Tm -> Val
# Interprets a term in an environment of values, producing a value.
# Pure function — zero effect system imports.
#
# Trampolines vNatElim and vListElim via builtins.genericClosure
# to guarantee O(1) stack depth on large inductive values.
#
# Fuel mechanism (§9): each eval call decrements fuel. Throws
# "normalization budget exceeded" on exhaustion. Default 10M.
#
# Spec reference: kernel-spec.md §4, §9
{ fx, api, ... }:

let
  inherit (api) mk;
  val = fx.tc.value;
  inherit (val) mkClosure freshVar
    vLam vPi vSigma vPair vNat vZero vSucc
    vBool vTrue vFalse vList vNil vCons
    vUnit vTt vVoid vSum vInl vInr vEq vRefl vU vNe
    vString vInt vFloat vAttrs vPath vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit
    eApp eFst eSnd eNatElim eBoolElim eListElim eAbsurd eSumElim eJ;

  defaultFuel = 10000000;

  # -- Fuel-threaded internals --

  instantiateF = fuel: cl: arg: evalF fuel ([ arg ] ++ cl.env) cl.body;

  vAppF = fuel: fn: arg:
    if fn.tag == "VLam" then instantiateF fuel fn.closure arg
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
        baseResult = vNatElimF fuel motive base step last.val;
        n = builtins.length chain - 1;
        # Thread fuel through fold: each step application decrements fuel
        result = builtins.foldl' (state: i:
          if state.fuel <= 0 then throw "normalization budget exceeded"
          else let
            item = builtins.elemAt chain (n - i);
            predVal = item.val.pred;
            f = state.fuel;
            applied = vAppF f (vAppF f step predVal) state.acc;
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
        baseResult = vListElimF fuel elemTy motive onNil onCons last.val;
        n = builtins.length chain - 1;
        # Thread fuel through fold: each step application decrements fuel
        result = builtins.foldl' (state: i:
          if state.fuel <= 0 then throw "normalization budget exceeded"
          else let
            item = builtins.elemAt chain (n - i);
            h = item.val.head;
            t = item.val.tail;
            f = state.fuel;
            applied = vAppF f (vAppF f (vAppF f onCons h) t) state.acc;
          in { acc = applied; fuel = f - 1; }
        ) { acc = baseResult; inherit fuel; } (builtins.genList (i: i + 1) n);
      in result.acc
    else throw "tc: vListElim on non-list (tag=${scrut.tag})";

  vAbsurd = type: scrut:
    if scrut.tag == "VNe" then
      vNe scrut.level (scrut.spine ++ [ (eAbsurd type) ])
    else throw "tc: vAbsurd on non-neutral (tag=${scrut.tag})";

  vSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
    if scrut.tag == "VInl" then vAppF fuel onLeft scrut.val
    else if scrut.tag == "VInr" then vAppF fuel onRight scrut.val
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

  # -- Main evaluator with fuel (§9) --
  evalF = fuel: env: tm:
    if fuel <= 0 then throw "normalization budget exceeded"
    else let t = tm.tag; f = fuel - 1; ev = evalF f env; in
    # Variables and binding
    if t == "var" then builtins.elemAt env tm.idx
    else if t == "let" then evalF f ([ (ev tm.val) ] ++ env) tm.body
    else if t == "ann" then ev tm.term

    # Functions
    else if t == "pi" then vPi tm.name (ev tm.domain) (mkClosure env tm.codomain)
    else if t == "lam" then vLam tm.name (ev tm.domain) (mkClosure env tm.body)
    else if t == "app" then vAppF f (ev tm.fn) (ev tm.arg)

    # Pairs
    else if t == "sigma" then vSigma tm.name (ev tm.fst) (mkClosure env tm.snd)
    else if t == "pair" then vPair (ev tm.fst) (ev tm.snd)
    else if t == "fst" then vFst (ev tm.pair)
    else if t == "snd" then vSnd (ev tm.pair)

    # Natural numbers
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
        (evalF (f - n) env base)
        (builtins.genList (x: x) n)
    else if t == "nat-elim" then
      vNatElimF f (ev tm.motive) (ev tm.base) (ev tm.step) (ev tm.scrut)

    # Booleans
    else if t == "bool" then vBool
    else if t == "true" then vTrue
    else if t == "false" then vFalse
    else if t == "bool-elim" then
      vBoolElim (ev tm.motive) (ev tm.onTrue) (ev tm.onFalse) (ev tm.scrut)

    # Lists
    else if t == "list" then vList (ev tm.elem)
    else if t == "nil" then vNil (ev tm.elem)
    # cons — trampolined for deep lists (5000+ elements)
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
            ef = evalF state.fuel env;
          in { acc = vCons (ef node.elem) (ef node.head) state.acc; fuel = state.fuel - 1; }
        ) { acc = evalF (f - n) env base; fuel = f - n; } (builtins.genList (x: x) n);
      in result.acc
    else if t == "list-elim" then
      vListElimF f (ev tm.elem) (ev tm.motive) (ev tm.nil) (ev tm.cons) (ev tm.scrut)

    # Unit
    else if t == "unit" then vUnit
    else if t == "tt" then vTt

    # Void
    else if t == "void" then vVoid
    else if t == "absurd" then vAbsurd (ev tm.type) (ev tm.term)

    # Sum
    else if t == "sum" then vSum (ev tm.left) (ev tm.right)
    else if t == "inl" then vInl (ev tm.left) (ev tm.right) (ev tm.term)
    else if t == "inr" then vInr (ev tm.left) (ev tm.right) (ev tm.term)
    else if t == "sum-elim" then
      vSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
        (ev tm.onLeft) (ev tm.onRight) (ev tm.scrut)

    # Identity
    else if t == "eq" then vEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
    else if t == "refl" then vRefl
    else if t == "j" then
      vJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
        (ev tm.base) (ev tm.rhs) (ev tm.eq)

    # Universes
    else if t == "U" then vU tm.level

    # Axiomatized primitives
    else if t == "string" then vString
    else if t == "int" then vInt
    else if t == "float" then vFloat
    else if t == "attrs" then vAttrs
    else if t == "path" then vPath
    else if t == "function" then vFunction
    else if t == "any" then vAny

    # Primitive literals
    else if t == "string-lit" then vStringLit tm.value
    else if t == "int-lit" then vIntLit tm.value
    else if t == "float-lit" then vFloatLit tm.value
    else if t == "attrs-lit" then vAttrsLit
    else if t == "path-lit" then vPathLit
    else if t == "fn-lit" then vFnLit
    else if t == "any-lit" then vAnyLit

    else throw "tc: eval unknown tag '${t}'";

  # -- Public API (default fuel) --
  eval = evalF defaultFuel;
  instantiate = instantiateF defaultFuel;
  vApp = vAppF defaultFuel;
  vNatElim = vNatElimF defaultFuel;
  vListElim = vListElimF defaultFuel;
  vSumElim = vSumElimF defaultFuel;

in mk {
  doc = ''
    # fx.tc.eval — Evaluator

    Pure evaluator: interprets kernel terms in an environment of
    values. Zero effect system imports — part of the trusted computing
    base (TCB).

    Spec reference: kernel-spec.md §4, §9.

    ## Core Functions

    - `eval : Env → Tm → Val` — evaluate with default fuel (10M steps)
    - `evalF : Int → Env → Tm → Val` — evaluate with explicit fuel budget
    - `instantiate : Closure → Val → Val` — apply a closure to an argument

    ## Elimination Helpers

    - `vApp : Val → Val → Val` — apply a function value (beta-reduces VLam, extends spine for VNe)
    - `vFst`, `vSnd` — pair projections
    - `vNatElim`, `vBoolElim`, `vListElim` — inductive eliminators
    - `vAbsurd` — ex falso (only on neutrals)
    - `vSumElim` — sum elimination
    - `vJ` — identity elimination (computes to base on VRefl)

    ## Trampolining (§11.3)

    `vNatElim`, `vListElim`, `succ` chains, and `cons` chains use
    `builtins.genericClosure` to flatten recursive structures iteratively,
    guaranteeing O(1) stack depth on inputs like S^10000(0) or cons^5000.

    ## Fuel Mechanism (§9)

    Each `evalF` call decrements a fuel counter. When fuel reaches 0,
    evaluation throws `"normalization budget exceeded"`. This bounds
    total work and prevents unbounded computation in the Nix evaluator.
    Default budget: 10,000,000 steps.
  '';
  value = {
    inherit eval evalF instantiate;
    inherit vApp vFst vSnd vNatElim vBoolElim vListElim vAbsurd vSumElim vJ;
  };
  tests = let
    T = fx.tc.term;

    # Helper: build S^n(0) as a term
    succN = n: if n == 0 then T.mkZero else T.mkSucc (succN (n - 1));

    # Identity function: λ(x:Nat). x
    idTm = T.mkLam "x" T.mkNat (T.mkVar 0);

    # Application: (λx.x) 0
    appIdZero = T.mkApp idTm T.mkZero;
  in {
    # -- Variable lookup --
    "eval-var-0" = { expr = (eval [ vZero vTrue ] (T.mkVar 0)).tag; expected = "VZero"; };
    "eval-var-1" = { expr = (eval [ vZero vTrue ] (T.mkVar 1)).tag; expected = "VTrue"; };

    # -- Let binding --
    "eval-let" = {
      expr = (eval [] (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0))).tag;
      expected = "VZero";
    };

    # -- Annotation erasure --
    "eval-ann" = {
      expr = (eval [] (T.mkAnn T.mkZero T.mkNat)).tag;
      expected = "VZero";
    };

    # -- Functions --
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

    # -- Pairs --
    "eval-sigma" = { expr = (eval [] (T.mkSigma "x" T.mkNat T.mkBool)).tag; expected = "VSigma"; };
    "eval-pair" = { expr = (eval [] (T.mkPair T.mkZero T.mkTrue T.mkNat)).tag; expected = "VPair"; };
    "eval-fst" = {
      expr = (eval [] (T.mkFst (T.mkPair T.mkZero T.mkTrue T.mkNat))).tag;
      expected = "VZero";
    };
    "eval-snd" = {
      expr = (eval [] (T.mkSnd (T.mkPair T.mkZero T.mkTrue T.mkNat))).tag;
      expected = "VTrue";
    };
    "eval-fst-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkFst (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Natural numbers --
    "eval-nat" = { expr = (eval [] T.mkNat).tag; expected = "VNat"; };
    "eval-zero" = { expr = (eval [] T.mkZero).tag; expected = "VZero"; };
    "eval-succ" = { expr = (eval [] (T.mkSucc T.mkZero)).tag; expected = "VSucc"; };
    "eval-succ-3" = {
      expr = (eval [] (succN 3)).pred.pred.pred.tag;
      expected = "VZero";
    };

    # NatElim: base case
    "eval-nat-elim-zero" = {
      expr = (eval [ vNat vZero (freshVar 2) ]
        (T.mkNatElim (T.mkVar 0) (T.mkVar 1) (T.mkVar 2) T.mkZero)).tag;
      expected = "VZero";
    };

    # NatElim: step case S(0)
    "eval-nat-elim-succ1" = {
      expr =
        let
          stepTm = T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)));
          r = eval [] (T.mkNatElim (T.mkLam "n" T.mkNat (T.mkU 0)) T.mkZero stepTm (T.mkSucc T.mkZero));
        in r.tag;
      expected = "VSucc";
    };

    # NatElim: stuck on neutral
    "eval-nat-elim-stuck" = {
      expr = (eval [ (freshVar 0) vNat vZero (freshVar 3) ]
        (T.mkNatElim (T.mkVar 1) (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Booleans --
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

    # -- Lists --
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

    # -- Unit --
    "eval-unit" = { expr = (eval [] T.mkUnit).tag; expected = "VUnit"; };
    "eval-tt" = { expr = (eval [] T.mkTt).tag; expected = "VTt"; };

    # -- Void --
    "eval-void" = { expr = (eval [] T.mkVoid).tag; expected = "VVoid"; };
    "eval-absurd-stuck" = {
      expr = (eval [ (freshVar 0) ] (T.mkAbsurd T.mkNat (T.mkVar 0))).tag;
      expected = "VNe";
    };

    # -- Sum --
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

    # -- Identity --
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

    # -- Universes --
    "eval-U0" = { expr = (eval [] (T.mkU 0)).tag; expected = "VU"; };
    "eval-U0-level" = { expr = (eval [] (T.mkU 0)).level; expected = 0; };
    "eval-U1-level" = { expr = (eval [] (T.mkU 1)).level; expected = 1; };

    # -- Axiomatized primitives --
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

    # -- Closure instantiation --
    "instantiate-identity" = {
      expr = (instantiate (mkClosure [] (T.mkVar 0)) vZero).tag;
      expected = "VZero";
    };
    "instantiate-const" = {
      expr = (instantiate (mkClosure [ vTrue ] (T.mkVar 1)) vZero).tag;
      expected = "VTrue";
    };

    # -- Fuel mechanism (§9) --
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

    # Fuel threading: NatElim with fuel=100 on S^200(0) must exhaust.
    # Before fix, each fold step got full fuel budget; now fuel decrements per step.
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
    # Fuel threading: ListElim with fuel=100 on 200-element list must exhaust.
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

    # Fuel threading: Cons eval with fuel=100 on 200-element cons chain must exhaust.
    # Before fix, each fold step got full fuel budget; now fuel deducts chain length.
    "fuel-threading-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (builtins.tryEval (builtins.deepSeq
        (evalF 100 [] (mkList 200))
        true)).success;
      expected = false;
    };
    # Cons eval with sufficient fuel succeeds
    "fuel-sufficient-cons-eval" = {
      expr = let
        mkList = n: builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) n);
      in (eval [] (mkList 50)).tag;
      expected = "VCons";
    };

    # -- §11.3 Stress tests (eval level) --

    # S^10000(0) evaluates to VSucc chain (trampoline not needed for eval,
    # but confirms eval handles deep Succ terms via lazy wrapping)
    "stress-eval-10000" = {
      expr = let
        bigNat = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 10000);
      in (eval [] bigNat).tag;
      expected = "VSucc";
    };

    # NatElim on S^1000(0) — trampoline stress (spec §11.3)
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
