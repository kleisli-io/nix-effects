# Type-checking kernel: HOAS surface combinators
#
# Higher-Order Abstract Syntax layer using Nix lambdas for variable binding.
# Combinators produce an intermediate HOAS tree; `elaborate` compiles it
# to de Bruijn indexed Tm terms that the kernel can check/infer.
#
# HOAS markers: { _hoas = true; level = N; } — produced by binding
# combinators, compiled away by elaborate. No Nix lambdas leak into
# the kernel value domain.
#
# Spec reference: kernel-spec.md, kernel-mvp-research.md §2
{ fx, api, ... }:

let
  inherit (api) mk;
  T = fx.tc.term;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  CH = fx.tc.check;

  # -- HOAS variable markers --
  # A marker is a lightweight attrset that stands for a bound variable
  # at a specific binding depth (level). elaborate converts these to
  # T.mkVar with the correct de Bruijn index.
  _hoasTag = "__nix-effects-hoas-marker__";
  mkMarker = level: { _hoas = _hoasTag; inherit level; };
  isMarker = x: builtins.isAttrs x && x ? _hoas && x._hoas == _hoasTag;

  # -- HOAS AST node constructors --
  # These build an intermediate tree that elaborate walks.

  # Types
  nat = { _htag = "nat"; };
  bool = { _htag = "bool"; };
  unit = { _htag = "unit"; };
  void = { _htag = "void"; };
  listOf = elem: { _htag = "list"; inherit elem; };
  sum = left: right: { _htag = "sum"; inherit left right; };
  eq = type: lhs: rhs: { _htag = "eq"; inherit type lhs rhs; };
  u = level: { _htag = "U"; inherit level; };

  # Binding types — take Nix lambda for the body
  forall = name: domain: bodyFn:
    { _htag = "pi"; inherit name domain; body = bodyFn; };

  sigma = name: fst: sndFn:
    { _htag = "sigma"; inherit name fst; body = sndFn; };

  # Terms
  lam = name: domain: bodyFn:
    { _htag = "lam"; inherit name domain; body = bodyFn; };

  let_ = name: type: val: bodyFn:
    { _htag = "let"; inherit name type val; body = bodyFn; };

  zero = { _htag = "zero"; };
  succ = pred: { _htag = "succ"; inherit pred; };
  true_ = { _htag = "true"; };
  false_ = { _htag = "false"; };
  tt = { _htag = "tt"; };
  nil = elem: { _htag = "nil"; inherit elem; };
  cons = elem: head: tail: { _htag = "cons"; inherit elem head tail; };
  pair = fst: snd: ann: { _htag = "pair"; inherit fst snd ann; };
  inl = left: right: term: { _htag = "inl"; inherit left right term; };
  inr = left: right: term: { _htag = "inr"; inherit left right term; };
  refl = { _htag = "refl"; };
  absurd = type: term: { _htag = "absurd"; inherit type term; };
  ann = term: type: { _htag = "ann"; inherit term type; };
  app = fn: arg: { _htag = "app"; inherit fn arg; };

  # Eliminators
  ind = motive: base: step: scrut:
    { _htag = "nat-elim"; inherit motive base step scrut; };
  boolElim = motive: onTrue: onFalse: scrut:
    { _htag = "bool-elim"; inherit motive onTrue onFalse scrut; };
  listElim = elem: motive: onNil: onCons: scrut:
    { _htag = "list-elim"; inherit elem motive onNil onCons scrut; };
  sumElim = left: right: motive: onLeft: onRight: scrut:
    { _htag = "sum-elim"; inherit left right motive onLeft onRight scrut; };
  j = type: lhs: motive: base: rhs: eq_:
    { _htag = "j"; inherit type lhs motive base rhs; eq = eq_; };

  # -- Elaboration: HOAS tree → de Bruijn Tm --
  #
  # elaborate : Int → HoasTree → Tm
  # depth tracks the current binding depth. When we encounter a binding
  # combinator (pi, lam, sigma, let), we:
  #   1. Apply the stored Nix lambda to mkMarker(depth)
  #   2. Recursively elaborate the resulting body at depth+1
  #   3. Markers with level L become T.mkVar(depth - L - 1)
  elaborate = depth: h:
    # Marker → variable
    if isMarker h then
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
    if t == "nat" then T.mkNat
    else if t == "bool" then T.mkBool
    else if t == "unit" then T.mkUnit
    else if t == "void" then T.mkVoid
    else if t == "U" then T.mkU h.level
    else if t == "list" then T.mkList (elaborate depth h.elem)
    else if t == "sum" then T.mkSum (elaborate depth h.left) (elaborate depth h.right)
    else if t == "eq" then
      T.mkEq (elaborate depth h.type) (elaborate depth h.lhs) (elaborate depth h.rhs)

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
              let marker = mkMarker item.key; in
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
    else if t == "zero" then T.mkZero
    # succ — trampolined for deep naturals (5000+)
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
      in builtins.foldl' (acc: _: T.mkSucc acc) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "true" then T.mkTrue
    else if t == "false" then T.mkFalse
    else if t == "tt" then T.mkTt
    else if t == "refl" then T.mkRefl
    else if t == "nil" then T.mkNil (elaborate depth h.elem)
    # cons — trampolined for deep lists (5000+ elements)
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
      in builtins.foldl' (acc: i:
        let node = (builtins.elemAt chain (n - 1 - i)).val; in
        T.mkCons (elaborate depth node.elem) (elaborate depth node.head) acc
      ) (elaborate depth base) (builtins.genList (x: x) n)
    else if t == "pair" then
      T.mkPair (elaborate depth h.fst) (elaborate depth h.snd) (elaborate depth h.ann)
    else if t == "inl" then
      T.mkInl (elaborate depth h.left) (elaborate depth h.right) (elaborate depth h.term)
    else if t == "inr" then
      T.mkInr (elaborate depth h.left) (elaborate depth h.right) (elaborate depth h.term)
    else if t == "absurd" then
      T.mkAbsurd (elaborate depth h.type) (elaborate depth h.term)
    else if t == "ann" then
      T.mkAnn (elaborate depth h.term) (elaborate depth h.type)
    else if t == "app" then
      T.mkApp (elaborate depth h.fn) (elaborate depth h.arg)

    # -- Eliminators --
    else if t == "nat-elim" then
      T.mkNatElim (elaborate depth h.motive) (elaborate depth h.base)
        (elaborate depth h.step) (elaborate depth h.scrut)
    else if t == "bool-elim" then
      T.mkBoolElim (elaborate depth h.motive) (elaborate depth h.onTrue)
        (elaborate depth h.onFalse) (elaborate depth h.scrut)
    else if t == "list-elim" then
      T.mkListElim (elaborate depth h.elem) (elaborate depth h.motive)
        (elaborate depth h.onNil) (elaborate depth h.onCons) (elaborate depth h.scrut)
    else if t == "sum-elim" then
      T.mkSumElim (elaborate depth h.left) (elaborate depth h.right)
        (elaborate depth h.motive) (elaborate depth h.onLeft)
        (elaborate depth h.onRight) (elaborate depth h.scrut)
    else if t == "j" then
      T.mkJ (elaborate depth h.type) (elaborate depth h.lhs)
        (elaborate depth h.motive) (elaborate depth h.base)
        (elaborate depth h.rhs) (elaborate depth h.eq)

    else throw "hoas.elaborate: unknown tag: ${t}";

  # -- Convenience: elaborate from depth 0 --
  elab = elaborate 0;

  # -- Convenience wrappers using the kernel checker --
  checkHoas = hoasTy: hoasTm:
    let
      ty = elab hoasTy;
      tm = elab hoasTm;
      vTy = E.eval [] ty;
    in CH.runCheck (CH.check CH.emptyCtx tm vTy);

  inferHoas = hoasTm:
    let tm = elab hoasTm;
    in CH.runCheck (CH.infer CH.emptyCtx tm);

  # -- Natural number literal helper --
  natLit = n:
    builtins.foldl' (acc: _: succ acc) zero (builtins.genList (x: x) n);

in mk {
  doc = ''
    HOAS surface combinators for the type-checking kernel.
    Use Nix lambdas for variable binding — elaborate compiles to de Bruijn Tm.
    Example: forall "A" (u 0) (A: forall "x" A (_: A))  →  Π(A:U₀). A → A
  '';
  value = {
    # Types
    inherit nat bool unit void listOf sum eq u;
    # Binding
    inherit forall sigma lam let_;
    # Terms
    inherit zero succ true_ false_ tt nil cons pair inl inr refl absurd ann app;
    # Eliminators
    inherit ind boolElim listElim sumElim j;
    # Elaboration
    inherit elaborate elab;
    # Convenience
    inherit checkHoas inferHoas natLit;
  };
  tests = {
    # ===== Combinator tests (elaborate produces correct Tm) =====

    # -- Type combinators --
    "elab-nat" = { expr = (elab nat).tag; expected = "nat"; };
    "elab-bool" = { expr = (elab bool).tag; expected = "bool"; };
    "elab-unit" = { expr = (elab unit).tag; expected = "unit"; };
    "elab-void" = { expr = (elab void).tag; expected = "void"; };
    "elab-U0" = { expr = (elab (u 0)).tag; expected = "U"; };
    "elab-U0-level" = { expr = (elab (u 0)).level; expected = 0; };
    "elab-list" = { expr = (elab (listOf nat)).tag; expected = "list"; };
    "elab-sum" = { expr = (elab (sum nat bool)).tag; expected = "sum"; };
    "elab-eq" = { expr = (elab (eq nat zero zero)).tag; expected = "eq"; };

    # -- Binding type: forall --
    "elab-forall-tag" = {
      expr = (elab (forall "x" nat (_: nat))).tag;
      expected = "pi";
    };
    "elab-forall-domain" = {
      expr = (elab (forall "x" nat (_: nat))).domain.tag;
      expected = "nat";
    };
    "elab-forall-body-var" = {
      # forall "x" Nat (x: x) — body is Var(0)
      expr = (elab (forall "x" nat (x: x))).codomain.tag;
      expected = "var";
    };
    "elab-forall-body-idx" = {
      expr = (elab (forall "x" nat (x: x))).codomain.idx;
      expected = 0;
    };

    # -- Binding type: sigma --
    "elab-sigma-tag" = {
      expr = (elab (sigma "x" nat (_: bool))).tag;
      expected = "sigma";
    };

    # -- Binding terms: lam --
    "elab-lam-tag" = {
      expr = (elab (lam "x" nat (x: x))).tag;
      expected = "lam";
    };
    "elab-lam-body-idx" = {
      expr = (elab (lam "x" nat (x: x))).body.idx;
      expected = 0;
    };

    # -- let_ --
    "elab-let-tag" = {
      expr = (elab (let_ "x" nat zero (x: x))).tag;
      expected = "let";
    };

    # -- Non-binding terms --
    "elab-zero" = { expr = (elab zero).tag; expected = "zero"; };
    "elab-succ" = { expr = (elab (succ zero)).tag; expected = "succ"; };
    "elab-true" = { expr = (elab true_).tag; expected = "true"; };
    "elab-false" = { expr = (elab false_).tag; expected = "false"; };
    "elab-tt" = { expr = (elab tt).tag; expected = "tt"; };
    "elab-nil" = { expr = (elab (nil nat)).tag; expected = "nil"; };
    "elab-cons" = { expr = (elab (cons nat zero (nil nat))).tag; expected = "cons"; };
    "elab-pair" = { expr = (elab (pair zero true_ nat)).tag; expected = "pair"; };
    "elab-inl" = { expr = (elab (inl nat bool zero)).tag; expected = "inl"; };
    "elab-inr" = { expr = (elab (inr nat bool true_)).tag; expected = "inr"; };
    "elab-refl" = { expr = (elab refl).tag; expected = "refl"; };
    "elab-ann" = { expr = (elab (ann zero nat)).tag; expected = "ann"; };
    "elab-app" = { expr = (elab (app (lam "x" nat (x: x)) zero)).tag; expected = "app"; };
    "elab-absurd" = { expr = (elab (absurd nat (lam "x" void (x: x)))).tag; expected = "absurd"; };

    # -- Error path: non-serializable value doesn't crash toJSON --
    "elab-error-non-serializable" = {
      expr = (builtins.tryEval (elab (x: x))).success;
      expected = false;
    };

    # -- Sentinel hardening: {_hoas=true} is NOT a marker --
    "elab-reject-fake-marker" = {
      expr = (builtins.tryEval (elab { _hoas = true; level = 0; })).success;
      expected = false;
    };

    # -- Eliminators --
    "elab-nat-elim" = {
      expr = (elab (ind (lam "n" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
        zero)).tag;
      expected = "nat-elim";
    };
    "elab-bool-elim" = {
      expr = (elab (boolElim (lam "b" bool (_: nat)) zero (succ zero) true_)).tag;
      expected = "bool-elim";
    };

    # -- Nested binding: de Bruijn indices correct --
    "elab-nested-var-outer" = {
      # forall "A" U0 (A: forall "x" A (_: A))
      # Inner body uses A which is at depth 0 when bound, now at depth 2
      # So idx = 2 - 0 - 1 = 1
      expr = (elab (forall "A" (u 0) (a:
        forall "x" a (_: a)))).codomain.codomain.idx;
      expected = 1;
    };
    "elab-nested-var-inner" = {
      # forall "A" U0 (A: forall "x" A (x: x))
      # x is at depth 1, used at depth 2 → idx = 2 - 1 - 1 = 0
      expr = (elab (forall "A" (u 0) (_:
        forall "x" nat (x: x)))).codomain.codomain.idx;
      expected = 0;
    };

    # -- natLit helper --
    "natLit-0" = { expr = (elab (natLit 0)).tag; expected = "zero"; };
    "natLit-3" = { expr = (elab (natLit 3)).pred.pred.pred.tag; expected = "zero"; };

    # -- Stack safety: deep succ chain elaboration --
    "elab-succ-5000" = {
      expr = let tm = elab (natLit 5000); in tm.tag;
      expected = "succ";
    };

    # -- Stack safety: deep nested Pi chain elaboration --
    "elab-pi-8000" = {
      expr = let
        deepPi = builtins.foldl' (acc: _:
          forall "_" nat (_: acc)
        ) nat (builtins.genList (x: x) 8000);
        tm = elab deepPi;
      in tm.tag;
      expected = "pi";
    };

    # -- Stack safety: deep nested Lam chain elaboration --
    "elab-lam-8000" = {
      expr = let
        deepLam = builtins.foldl' (acc: _:
          lam "_" nat (_: acc)
        ) zero (builtins.genList (x: x) 8000);
        tm = elab deepLam;
      in tm.tag;
      expected = "lam";
    };

    # -- Stack safety: deep cons chain elaboration --
    "elab-cons-5000" = {
      expr = let
        bigList = builtins.foldl' (acc: _:
          cons nat zero acc
        ) (nil nat) (builtins.genList (x: x) 5000);
        tm = elab bigList;
      in tm.tag;
      expected = "cons";
    };

    # ===== Kernel integration: type-check elaborated terms =====

    # Zero : Nat
    "check-zero" = {
      expr = (checkHoas nat zero).tag;
      expected = "zero";
    };

    # S(S(0)) : Nat
    "check-succ2" = {
      expr = (checkHoas nat (succ (succ zero))).tag;
      expected = "succ";
    };

    # True : Bool
    "check-true" = {
      expr = (checkHoas bool true_).tag;
      expected = "true";
    };

    # () : Unit
    "check-tt" = {
      expr = (checkHoas unit tt).tag;
      expected = "tt";
    };

    # nil Nat : List Nat
    "check-nil" = {
      expr = (checkHoas (listOf nat) (nil nat)).tag;
      expected = "nil";
    };

    # cons Nat 0 (nil Nat) : List Nat
    "check-cons" = {
      expr = (checkHoas (listOf nat) (cons nat zero (nil nat))).tag;
      expected = "cons";
    };

    # inl Nat Bool 0 : Sum Nat Bool
    "check-inl" = {
      expr = (checkHoas (sum nat bool) (inl nat bool zero)).tag;
      expected = "inl";
    };

    # pair(0, true) : Σ(x:Nat).Bool
    "check-pair" = {
      expr = (checkHoas (sigma "x" nat (_: bool)) (pair zero true_ (sigma "x" nat (_: bool)))).tag;
      expected = "pair";
    };

    # Refl : Eq(Nat, 0, 0)
    "check-refl" = {
      expr = (checkHoas (eq nat zero zero) refl).tag;
      expected = "refl";
    };

    # ===== Theorem tests =====

    # Polymorphic identity: λ(A:U₀). λ(x:A). x  :  Π(A:U₀). A → A
    "theorem-poly-id" = {
      expr = let
        ty = forall "A" (u 0) (a: forall "x" a (_: a));
        tm = lam "A" (u 0) (a: lam "x" a (x: x));
      in (checkHoas ty tm).tag;
      expected = "lam";
    };

    # 0 + 0 = 0 by computation: NatElim(_, 0, λk.λih.S(ih), 0) = 0, Refl
    "theorem-0-plus-0" = {
      expr = let
        addZero = ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih))) zero;
        eqTy = eq nat addZero zero;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # n + 0 = n by induction:
    #   motive: λn. Eq(Nat, add(n,0), n)
    #   base: Refl  (add(0,0) = 0 by computation)
    #   step: λk. λih. cong succ ih  (where add(S(k),0) = S(add(k,0)))
    # cong f p = J(A, a, λb.λ_. Eq(B, f(a), f(b)), refl, b, p)
    # For our purposes, since add(S(k), 0) computes to S(add(k, 0)) by the
    # step of NatElim, and ih : add(k,0) = k, we need:
    #   S(add(k,0)) = S(k), which follows from congruence on ih.
    #
    # Actually, since add is defined by NatElim and NatElim on S(k) computes
    # the step, we get: add(S(k), 0) = S(add(k, 0)). Combined with ih : add(k,0) = k
    # we need S(add(k,0)) = S(k). The J eliminator can produce this.
    #
    # However, encoding cong via J in HOAS is complex. Let's use a simpler approach:
    # The checker normalizes both sides before comparing, so if add(n,0) reduces to n
    # for all n, we just need Refl. But NatElim doesn't reduce symbolically.
    # Instead, test a concrete case: n=3.
    "theorem-3-plus-0-eq-3" = {
      expr = let
        three = succ (succ (succ zero));
        add_n_0 = ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih))) three;
        eqTy = eq nat add_n_0 three;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # Dependent pair: (0, Refl) : Σ(x:Nat). Eq(Nat, x, 0)
    "theorem-dep-pair" = {
      expr = let
        ty = sigma "x" nat (x: eq nat x zero);
        tm = pair zero refl (sigma "x" nat (x: eq nat x zero));
      in (checkHoas ty tm).tag;
      expected = "pair";
    };

    # BoolElim type-checks: if true then 0 else 1 : Nat
    "theorem-bool-elim" = {
      expr = let
        tm = boolElim (lam "b" bool (_: nat)) zero (succ zero) true_;
      in (inferHoas (ann tm nat)).type.tag;
      expected = "VNat";
    };

    # ===== Roundtrip: elaborate → eval → quote → eval → quote =====

    "roundtrip-lam-id" = {
      expr = let
        tm = elab (lam "x" nat (x: x));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-forall" = {
      expr = let
        tm = elab (forall "A" (u 0) (a: forall "x" a (_: a)));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-sigma" = {
      expr = let
        tm = elab (sigma "x" nat (_: bool));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-nat-elim" = {
      expr = let
        tm = elab (ind (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
          (succ (succ zero)));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    "roundtrip-natLit-5" = {
      expr = let tm = elab (natLit 5);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    # Stress test — stack safety (B4)
    "natLit-5000" = {
      expr = (elab (natLit 5000)).tag;
      expected = "succ";
    };
  };
}
