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
    else if t == "VPair" then T.mkPair (quote d v.fst) (quote d v.snd) T.mkUnit
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
    else if t == "VBool" then T.mkBool
    else if t == "VTrue" then T.mkTrue
    else if t == "VFalse" then T.mkFalse
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
    else if t == "VVoid" then T.mkVoid
    else if t == "VSum" then T.mkSum (quote d v.left) (quote d v.right)
    else if t == "VInl" then T.mkInl (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VInr" then T.mkInr (quote d v.left) (quote d v.right) (quote d v.val)
    else if t == "VEq" then T.mkEq (quote d v.type) (quote d v.lhs) (quote d v.rhs)
    else if t == "VRefl" then T.mkRefl
    else if t == "VU" then T.mkU v.level
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
    else if t == "EBoolElim" then
      T.mkBoolElim (quote d elim.motive) (quote d elim.onTrue) (quote d elim.onFalse) head
    else if t == "EListElim" then
      T.mkListElim (quote d elim.elem) (quote d elim.motive) (quote d elim.onNil) (quote d elim.onCons) head
    else if t == "EAbsurd" then T.mkAbsurd (quote d elim.type) head
    else if t == "ESumElim" then
      T.mkSumElim (quote d elim.left) (quote d elim.right) (quote d elim.motive)
        (quote d elim.onLeft) (quote d elim.onRight) head
    else if t == "EJ" then
      T.mkJ (quote d elim.type) (quote d elim.lhs) (quote d elim.motive)
        (quote d elim.base) (quote d elim.rhs) head
    else if t == "EStrEq" then T.mkStrEq head (quote d elim.arg)
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
    inherit (V) vNat vZero vSucc vBool vTrue vFalse vPi vLam vSigma vPair
      vList vNil vCons vUnit vTt vVoid vSum vInl vInr vEq vRefl vU vNe
      mkClosure eApp eFst eSnd eNatElim eBoolElim eListElim eAbsurd eSumElim eJ;
  in {
    # -- Level to index --
    "lvl2ix-0" = { expr = lvl2Ix 1 0; expected = 0; };
    "lvl2ix-1" = { expr = lvl2Ix 3 0; expected = 2; };
    "lvl2ix-2" = { expr = lvl2Ix 3 2; expected = 0; };

    # -- Simple values --
    "quote-nat" = { expr = (quote 0 vNat).tag; expected = "nat"; };
    "quote-zero" = { expr = (quote 0 vZero).tag; expected = "zero"; };
    "quote-succ" = { expr = (quote 0 (vSucc vZero)).tag; expected = "succ"; };
    "quote-bool" = { expr = (quote 0 vBool).tag; expected = "bool"; };
    "quote-true" = { expr = (quote 0 vTrue).tag; expected = "true"; };
    "quote-false" = { expr = (quote 0 vFalse).tag; expected = "false"; };
    "quote-unit" = { expr = (quote 0 vUnit).tag; expected = "unit"; };
    "quote-tt" = { expr = (quote 0 vTt).tag; expected = "tt"; };
    "quote-void" = { expr = (quote 0 vVoid).tag; expected = "void"; };
    "quote-refl" = { expr = (quote 0 vRefl).tag; expected = "refl"; };
    "quote-U0" = { expr = (quote 0 (vU 0)).tag; expected = "U"; };
    "quote-U0-level" = { expr = (quote 0 (vU 0)).level; expected = 0; };
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
    "quote-pair" = { expr = (quote 0 (vPair vZero vTrue)).tag; expected = "pair"; };
    "quote-list" = { expr = (quote 0 (vList vNat)).tag; expected = "list"; };
    "quote-nil" = { expr = (quote 0 (vNil vNat)).tag; expected = "nil"; };
    "quote-cons" = { expr = (quote 0 (vCons vNat vZero (vNil vNat))).tag; expected = "cons"; };
    "quote-sum" = { expr = (quote 0 (vSum vNat vBool)).tag; expected = "sum"; };
    "quote-inl" = { expr = (quote 0 (vInl vNat vBool vZero)).tag; expected = "inl"; };
    "quote-inr" = { expr = (quote 0 (vInr vNat vBool vTrue)).tag; expected = "inr"; };
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
    "quote-ne-bool-elim" = {
      expr = (quote 1 (vNe 0 [ (eBoolElim vNat vZero (vSucc vZero)) ])).tag;
      expected = "bool-elim";
    };
    "quote-ne-list-elim" = {
      expr = (quote 1 (vNe 0 [ (eListElim vNat vNat vZero vZero) ])).tag;
      expected = "list-elim";
    };
    "quote-ne-absurd" = {
      expr = (quote 1 (vNe 0 [ (eAbsurd vNat) ])).tag;
      expected = "absurd";
    };
    "quote-ne-sum-elim" = {
      expr = (quote 1 (vNe 0 [ (eSumElim vNat vBool vNat vZero vZero) ])).tag;
      expected = "sum-elim";
    };
    "quote-ne-j" = {
      expr = (quote 1 (vNe 0 [ (eJ vNat vZero vNat vZero vZero) ])).tag;
      expected = "j";
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
      expr = (quote 0 (vSigma "x" vNat (mkClosure [] T.mkBool))).tag;
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
      expr = (nf [] (T.mkFst (T.mkPair T.mkZero T.mkTrue T.mkNat))).tag;
      expected = "zero";
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
