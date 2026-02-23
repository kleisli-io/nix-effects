# Type-checking kernel: Conversion (definitional equality)
#
# conv : Depth -> Val -> Val -> Bool
# Checks definitional equality of two values at binding depth d.
# Purely structural on normalized values — no type information used.
# No eta expansion. Cumulativity handled in check.nix Sub rule only.
# Pure function — zero effect system imports.
#
# Spec reference: kernel-spec.md §6
{ fx, api, ... }:

let
  inherit (api) mk;
  V = fx.tc.value;
  E = fx.tc.eval;

  # -- Main conversion checker --
  # Returns true if v1 and v2 are definitionally equal at depth d.
  conv = d: v1: v2:
    let t1 = v1.tag; t2 = v2.tag; in

    # §6.1 Structural rules — simple values
    if t1 == "VNat" && t2 == "VNat" then true
    else if t1 == "VBool" && t2 == "VBool" then true
    else if t1 == "VUnit" && t2 == "VUnit" then true
    else if t1 == "VVoid" && t2 == "VVoid" then true
    else if t1 == "VZero" && t2 == "VZero" then true
    else if t1 == "VTrue" && t2 == "VTrue" then true
    else if t1 == "VFalse" && t2 == "VFalse" then true
    else if t1 == "VTt" && t2 == "VTt" then true
    else if t1 == "VRefl" && t2 == "VRefl" then true
    else if t1 == "VU" && t2 == "VU" then v1.level == v2.level
    # VSucc — trampolined for deep naturals (S^5000+)
    else if t1 == "VSucc" && t2 == "VSucc" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; a = v1; b = v2; }];
          operator = item:
            if item.a.tag == "VSucc" && item.b.tag == "VSucc"
            then [{ key = item.key + 1; a = item.a.pred; b = item.b.pred; }]
            else [];
        };
        last = builtins.elemAt chain (builtins.length chain - 1);
      in conv d last.a last.b

    # §6.2 Binding forms — compare under binders with fresh var
    else if t1 == "VPi" && t2 == "VPi" then
      conv d v1.domain v2.domain
      && conv (d + 1) (E.instantiate v1.closure (V.freshVar d))
                      (E.instantiate v2.closure (V.freshVar d))
    else if t1 == "VLam" && t2 == "VLam" then
      conv (d + 1) (E.instantiate v1.closure (V.freshVar d))
                   (E.instantiate v2.closure (V.freshVar d))
    else if t1 == "VSigma" && t2 == "VSigma" then
      conv d v1.fst v2.fst
      && conv (d + 1) (E.instantiate v1.closure (V.freshVar d))
                      (E.instantiate v2.closure (V.freshVar d))

    # §6.3 Compound values
    else if t1 == "VPair" && t2 == "VPair" then
      conv d v1.fst v2.fst && conv d v1.snd v2.snd
    else if t1 == "VList" && t2 == "VList" then conv d v1.elem v2.elem
    else if t1 == "VNil" && t2 == "VNil" then conv d v1.elem v2.elem
    # VCons — trampolined: peel tails iteratively, check elem+head per level
    else if t1 == "VCons" && t2 == "VCons" then
      let
        chain = builtins.genericClosure {
          startSet = [{ key = 0; a = v1; b = v2; }];
          operator = item:
            if item.a.tag == "VCons" && item.b.tag == "VCons"
            then [{ key = item.key + 1; a = item.a.tail; b = item.b.tail; }]
            else [];
        };
        last = builtins.elemAt chain (builtins.length chain - 1);
      in builtins.foldl' (acc: item:
        acc && (
          if item.a.tag == "VCons" && item.b.tag == "VCons"
          then conv d item.a.elem item.b.elem && conv d item.a.head item.b.head
          else true
        )
      ) true chain
      && conv d last.a last.b
    else if t1 == "VSum" && t2 == "VSum" then
      conv d v1.left v2.left && conv d v1.right v2.right
    else if t1 == "VInl" && t2 == "VInl" then
      conv d v1.left v2.left && conv d v1.right v2.right && conv d v1.val v2.val
    else if t1 == "VInr" && t2 == "VInr" then
      conv d v1.left v2.left && conv d v1.right v2.right && conv d v1.val v2.val
    else if t1 == "VEq" && t2 == "VEq" then
      conv d v1.type v2.type && conv d v1.lhs v2.lhs && conv d v1.rhs v2.rhs

    # §6.4 Neutrals — same head variable and convertible spines
    else if t1 == "VNe" && t2 == "VNe" then
      v1.level == v2.level && convSp d v1.spine v2.spine

    # §6.5 Catch-all — different constructors are never equal
    else false;

  # -- Spine conversion --
  convSp = d: sp1: sp2:
    let len1 = builtins.length sp1; len2 = builtins.length sp2; in
    if len1 != len2 then false
    else if len1 == 0 then true
    else builtins.foldl' (acc: i:
      acc && convElim d (builtins.elemAt sp1 i) (builtins.elemAt sp2 i)
    ) true (builtins.genList (i: i) len1);

  # -- Elimination frame conversion --
  convElim = d: e1: e2:
    let t1 = e1.tag; t2 = e2.tag; in
    if t1 != t2 then false
    else if t1 == "EApp" then conv d e1.arg e2.arg
    else if t1 == "EFst" then true
    else if t1 == "ESnd" then true
    else if t1 == "ENatElim" then
      conv d e1.motive e2.motive && conv d e1.base e2.base && conv d e1.step e2.step
    else if t1 == "EBoolElim" then
      conv d e1.motive e2.motive && conv d e1.onTrue e2.onTrue && conv d e1.onFalse e2.onFalse
    else if t1 == "EListElim" then
      conv d e1.elem e2.elem && conv d e1.motive e2.motive
      && conv d e1.onNil e2.onNil && conv d e1.onCons e2.onCons
    else if t1 == "EAbsurd" then conv d e1.type e2.type
    else if t1 == "ESumElim" then
      conv d e1.left e2.left && conv d e1.right e2.right
      && conv d e1.motive e2.motive && conv d e1.onLeft e2.onLeft
      && conv d e1.onRight e2.onRight
    else if t1 == "EJ" then
      conv d e1.type e2.type && conv d e1.lhs e2.lhs
      && conv d e1.motive e2.motive && conv d e1.base e2.base
      && conv d e1.rhs e2.rhs
    else false;

in mk {
  doc = ''
    Conversion checker for the type-checking kernel.
    conv : Depth -> Val -> Val -> Bool.
    Structural equality on normalized values. No eta. No type info.
  '';
  value = { inherit conv convSp convElim; };
  tests = let
    inherit (V) vNat vZero vSucc vBool vTrue vFalse vPi vLam vSigma vPair
      vList vNil vCons vUnit vTt vVoid vSum vInl vInr vEq vRefl vU vNe
      mkClosure eApp eFst eSnd;
    T = fx.tc.term;
  in {
    # §6.1 Structural rules — reflexivity
    "conv-nat" = { expr = conv 0 vNat vNat; expected = true; };
    "conv-bool" = { expr = conv 0 vBool vBool; expected = true; };
    "conv-unit" = { expr = conv 0 vUnit vUnit; expected = true; };
    "conv-void" = { expr = conv 0 vVoid vVoid; expected = true; };
    "conv-zero" = { expr = conv 0 vZero vZero; expected = true; };
    "conv-true" = { expr = conv 0 vTrue vTrue; expected = true; };
    "conv-false" = { expr = conv 0 vFalse vFalse; expected = true; };
    "conv-tt" = { expr = conv 0 vTt vTt; expected = true; };
    "conv-refl" = { expr = conv 0 vRefl vRefl; expected = true; };
    "conv-U0" = { expr = conv 0 (vU 0) (vU 0); expected = true; };
    "conv-U1" = { expr = conv 0 (vU 1) (vU 1); expected = true; };

    # Structural rules — inequality
    "conv-nat-bool" = { expr = conv 0 vNat vBool; expected = false; };
    "conv-zero-true" = { expr = conv 0 vZero vTrue; expected = false; };
    "conv-U0-U1" = { expr = conv 0 (vU 0) (vU 1); expected = false; };
    "conv-true-false" = { expr = conv 0 vTrue vFalse; expected = false; };

    # VSucc
    "conv-succ-eq" = { expr = conv 0 (vSucc vZero) (vSucc vZero); expected = true; };
    "conv-succ-neq" = { expr = conv 0 (vSucc vZero) (vSucc (vSucc vZero)); expected = false; };
    "conv-succ-deep" = {
      expr = conv 0 (vSucc (vSucc vZero)) (vSucc (vSucc vZero));
      expected = true;
    };

    # §6.2 Binding forms
    "conv-pi" = {
      # Π(x:Nat).Nat ≡ Π(y:Nat).Nat (names don't matter)
      expr = conv 0
        (vPi "x" vNat (mkClosure [] T.mkNat))
        (vPi "y" vNat (mkClosure [] T.mkNat));
      expected = true;
    };
    "conv-pi-diff-domain" = {
      expr = conv 0
        (vPi "x" vNat (mkClosure [] T.mkNat))
        (vPi "x" vBool (mkClosure [] T.mkNat));
      expected = false;
    };
    "conv-pi-diff-codomain" = {
      expr = conv 0
        (vPi "x" vNat (mkClosure [] T.mkNat))
        (vPi "x" vNat (mkClosure [] T.mkBool));
      expected = false;
    };
    "conv-pi-dependent" = {
      # Π(x:Nat).x ≡ Π(y:Nat).y — both bodies reference the bound var
      expr = conv 0
        (vPi "x" vNat (mkClosure [] (T.mkVar 0)))
        (vPi "y" vNat (mkClosure [] (T.mkVar 0)));
      expected = true;
    };

    # Binding forms with different dependent bodies
    "conv-pi-dep-diff-body" = {
      # Π(x:Nat).x vs Π(x:Nat).Nat — different dependent codomains
      expr = conv 0
        (vPi "x" vNat (mkClosure [] (T.mkVar 0)))
        (vPi "x" vNat (mkClosure [] T.mkNat));
      expected = false;
    };
    "conv-sigma-dep-diff-body" = {
      # Σ(x:Nat).x vs Σ(x:Nat).Nat — different dependent second components
      expr = conv 0
        (vSigma "x" vNat (mkClosure [] (T.mkVar 0)))
        (vSigma "x" vNat (mkClosure [] T.mkNat));
      expected = false;
    };
    "conv-ne-multi-spine-diff" = {
      # x₀(Zero)(True) vs x₀(Zero)(False) — second frame differs
      expr = conv 2
        (vNe 0 [ (eApp vZero) (eApp vTrue) ])
        (vNe 0 [ (eApp vZero) (eApp vFalse) ]);
      expected = false;
    };

    "conv-lam" = {
      # λ(x:Nat).x ≡ λ(y:Nat).y
      expr = conv 0
        (vLam "x" vNat (mkClosure [] (T.mkVar 0)))
        (vLam "y" vNat (mkClosure [] (T.mkVar 0)));
      expected = true;
    };
    "conv-lam-diff-body" = {
      expr = conv 0
        (vLam "x" vNat (mkClosure [] T.mkZero))
        (vLam "x" vNat (mkClosure [] (T.mkSucc T.mkZero)));
      expected = false;
    };
    "conv-sigma" = {
      expr = conv 0
        (vSigma "x" vNat (mkClosure [] T.mkBool))
        (vSigma "y" vNat (mkClosure [] T.mkBool));
      expected = true;
    };

    # §6.3 Compound values
    "conv-pair" = { expr = conv 0 (vPair vZero vTrue) (vPair vZero vTrue); expected = true; };
    "conv-pair-diff" = { expr = conv 0 (vPair vZero vTrue) (vPair vZero vFalse); expected = false; };
    "conv-list" = { expr = conv 0 (vList vNat) (vList vNat); expected = true; };
    "conv-list-diff" = { expr = conv 0 (vList vNat) (vList vBool); expected = false; };
    "conv-nil" = { expr = conv 0 (vNil vNat) (vNil vNat); expected = true; };
    "conv-cons" = {
      expr = conv 0 (vCons vNat vZero (vNil vNat)) (vCons vNat vZero (vNil vNat));
      expected = true;
    };
    "conv-cons-diff" = {
      expr = conv 0
        (vCons vNat vZero (vNil vNat))
        (vCons vNat (vSucc vZero) (vNil vNat));
      expected = false;
    };
    "conv-sum" = { expr = conv 0 (vSum vNat vBool) (vSum vNat vBool); expected = true; };
    "conv-inl" = {
      expr = conv 0 (vInl vNat vBool vZero) (vInl vNat vBool vZero);
      expected = true;
    };
    "conv-inl-diff" = {
      expr = conv 0 (vInl vNat vBool vZero) (vInl vNat vBool (vSucc vZero));
      expected = false;
    };
    "conv-inr" = {
      expr = conv 0 (vInr vNat vBool vTrue) (vInr vNat vBool vTrue);
      expected = true;
    };
    "conv-eq" = {
      expr = conv 0 (vEq vNat vZero vZero) (vEq vNat vZero vZero);
      expected = true;
    };
    "conv-eq-diff" = {
      expr = conv 0 (vEq vNat vZero vZero) (vEq vNat vZero (vSucc vZero));
      expected = false;
    };

    # §6.4 Neutrals
    "conv-ne-same" = { expr = conv 1 (vNe 0 []) (vNe 0 []); expected = true; };
    "conv-ne-diff-level" = { expr = conv 2 (vNe 0 []) (vNe 1 []); expected = false; };
    "conv-ne-app" = {
      expr = conv 1 (vNe 0 [ (eApp vZero) ]) (vNe 0 [ (eApp vZero) ]);
      expected = true;
    };
    "conv-ne-app-diff" = {
      expr = conv 1 (vNe 0 [ (eApp vZero) ]) (vNe 0 [ (eApp vTrue) ]);
      expected = false;
    };
    "conv-ne-fst" = {
      expr = conv 1 (vNe 0 [ eFst ]) (vNe 0 [ eFst ]);
      expected = true;
    };
    "conv-ne-snd" = {
      expr = conv 1 (vNe 0 [ eSnd ]) (vNe 0 [ eSnd ]);
      expected = true;
    };
    "conv-ne-diff-spine-len" = {
      expr = conv 1 (vNe 0 [ (eApp vZero) ]) (vNe 0 []);
      expected = false;
    };
    "conv-ne-diff-elim" = {
      expr = conv 1 (vNe 0 [ eFst ]) (vNe 0 [ eSnd ]);
      expected = false;
    };

    # Symmetry property
    "conv-sym-nat-bool" = {
      expr = (conv 0 vNat vBool) == (conv 0 vBool vNat);
      expected = true;
    };
    "conv-sym-succ" = {
      expr = let a = vSucc vZero; b = vSucc (vSucc vZero); in
        (conv 0 a b) == (conv 0 b a);
      expected = true;
    };

    # No eta — f and λx.f(x) are NOT definitionally equal (§6.5)
    # freshVar(0) is a neutral, VLam wrapping App(freshVar(0), freshVar(1)) is its eta-expansion
    "conv-no-eta-lam" = {
      expr = conv 1
        (V.freshVar 0)
        (vLam "x" vNat (mkClosure [ (V.freshVar 0) ] (T.mkApp (T.mkVar 1) (T.mkVar 0))));
      expected = false;
    };

    # Stress tests — stack safety (B1/B2)
    "conv-succ-5000" = {
      expr = let
        deep = builtins.foldl' (acc: _: vSucc acc) vZero (builtins.genList (x: x) 5000);
      in conv 0 deep deep;
      expected = true;
    };
    "conv-succ-5000-neq" = {
      expr = let
        a = builtins.foldl' (acc: _: vSucc acc) vZero (builtins.genList (x: x) 5000);
        b = builtins.foldl' (acc: _: vSucc acc) vZero (builtins.genList (x: x) 4999);
      in conv 0 a b;
      expected = false;
    };
    "conv-cons-5000" = {
      expr = let
        deep = builtins.foldl' (acc: _: vCons vNat vZero acc) (vNil vNat) (builtins.genList (x: x) 5000);
      in conv 0 deep deep;
      expected = true;
    };
    "conv-cons-5000-neq" = {
      expr = let
        a = builtins.foldl' (acc: _: vCons vNat vZero acc) (vNil vNat) (builtins.genList (x: x) 5000);
        b = builtins.foldl' (acc: _: vCons vNat vZero acc) (vNil vNat) (builtins.genList (x: x) 4999);
      in conv 0 a b;
      expected = false;
    };
  };
}
