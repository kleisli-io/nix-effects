# Inline tests for the HOAS surface: combinator-level elaboration shape
# checks, kernel-integration checks through `checkHoas`/`inferHoas`,
# theorem proofs, description-level semantic equivalence, datatype macro
# coverage (UnitDT / BoolDT / NatDT / ListDT / SumDT / TreeDT / W-type),
# and deep-stack / neutral-scrutinee stress tests.
{ self, fx, ... }:

let
  E = fx.tc.eval;
  Q = fx.tc.quote;
  V = fx.tc.value;

  inherit (self)
    nat bool unit void string int_ float_ attrs path function_ any
    listOf sum eq u
    level levelZero levelSuc levelMax natToLevel
    forall sigma lam let_
    zero succ true_ false_ tt nil cons pair inl inr refl
    stringLit intLit floatLit attrsLit pathLit fnLit anyLit
    opaqueLam absurd ann app fst_ snd_
    ind boolElim listElim sumElim
    desc descAt mu descRet descArg descRec descPi descCon descElim
    descI descIAt muI retI recI piI plusI plus
    interpHoasAt allHoasAt natDesc listDesc sumDesc descDesc iso
    fin fzero fsuc finElim absurdFin0
    natCaseU natPredCase vec vnil vcons vecElim vhead vtail
    eqDesc eqDT reflDT eqToEqDT eqDTToEq eqIsoFwd eqIsoBwd
    field recField piFieldD con datatype datatypeP unitPrim
    elab checkHoas inferHoas natLit;
in {
  scope = {};
  tests = {
    # ===== Combinator tests (elaborate produces correct Tm) =====

    # -- Type combinators --
    "elab-nat" = { expr = (elab nat).tag; expected = "mu"; };
    "elab-bool" = { expr = (elab bool).tag; expected = "mu"; };
    "elab-unit" = { expr = (elab unit).tag; expected = "unit"; };
    "elab-void" = { expr = (elab void).tag; expected = "app"; };
    "elab-U0" = { expr = (elab (u 0)).tag; expected = "U"; };
    "elab-U0-level" = { expr = (elab (u 0)).level.tag; expected = "level-zero"; };
    "elab-list" = { expr = (elab (listOf nat)).tag; expected = "app"; };
    "elab-sum" = { expr = (elab (sum nat bool)).tag; expected = "app"; };
    "elab-eq" = { expr = (elab (eq nat zero zero)).tag; expected = "eq"; };

    # -- Binding type: forall --
    "elab-forall-tag" = {
      expr = (elab (forall "x" nat (_: nat))).tag;
      expected = "pi";
    };
    "elab-forall-domain" = {
      expr = (elab (forall "x" nat (_: nat))).domain.tag;
      expected = "mu";
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
    "elab-zero" = { expr = (elab zero).tag; expected = "desc-con"; };
    "elab-succ" = { expr = (elab (succ zero)).tag; expected = "desc-con"; };
    "elab-true" = { expr = (elab true_).tag; expected = "desc-con"; };
    "elab-false" = { expr = (elab false_).tag; expected = "desc-con"; };
    "elab-tt" = { expr = (elab tt).tag; expected = "tt"; };
    # nil/cons elaborate to desc-con whose payload is `inl …`/`inr …`,
    # selecting the nil vs cons summand of listDesc's plus-coproduct.
    "elab-nil" = {
      expr = let t = elab (nil nat); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inl";
    };
    "elab-cons" = {
      expr = let t = elab (cons nat zero (nil nat)); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inr";
    };
    "elab-pair" = { expr = (elab (pair zero true_)).tag; expected = "pair"; };
    # inl/inr elaborate to desc-con whose payload is `inl …`/`inr …`,
    # selecting the left vs right summand of sumDesc's plus-coproduct.
    "elab-inl" = {
      expr = let t = elab (inl nat bool zero); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inl";
    };
    "elab-inr" = {
      expr = let t = elab (inr nat bool true_); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inr";
    };
    "elab-refl" = { expr = (elab refl).tag; expected = "refl"; };
    "elab-ann" = { expr = (elab (ann zero nat)).tag; expected = "ann"; };
    "elab-app" = { expr = (elab (app (lam "x" nat (x: x)) zero)).tag; expected = "app"; };
    "elab-absurd" = { expr = (elab (absurd nat (lam "x" void (x: x)))).tag; expected = "app"; };
    "elab-fst" = { expr = (elab (fst_ (pair zero true_))).tag; expected = "fst"; };
    "elab-snd" = { expr = (elab (snd_ (pair zero true_))).tag; expected = "snd"; };

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
    # nat-elim surface combinator elaborates to nested let-bindings around
    # a desc-ind: `let P = motive in let B = base in let S = step in
    # desc-ind …`. The let-wrapping makes motive/step/base inferable (VAR
    # via lookupType) so the descInd check rule can type the body.
    "elab-nat-elim" = {
      expr = (elab (ind 0 (lam "n" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
        zero)).tag;
      expected = "let";
    };
    "elab-bool-elim" = {
      expr = (elab (boolElim 0 (lam "b" bool (_: nat)) zero (succ zero) true_)).tag;
      expected = "let";
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
    "natLit-0" = { expr = (elab (natLit 0)).tag; expected = "desc-con"; };
    "natLit-3" = { expr = (elab (natLit 3)).tag; expected = "desc-con"; };

    # -- Stack safety: deep succ chain elaboration --
    "elab-succ-5000" = {
      expr = let tm = elab (natLit 5000); in tm.tag;
      expected = "desc-con";
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
      expected = "desc-con";
    };

    # ===== Kernel integration: type-check elaborated terms =====

    # Zero : Nat — descCon natDesc (inl …)
    "check-zero" = {
      expr = let t = checkHoas nat zero; in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inl";
    };

    # S(S(0)) : Nat — outer desc-con has payload `inr …`; inner is s(0).
    "check-succ2" = {
      expr = let t = checkHoas nat (succ (succ zero)); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inr";
    };

    # True : Bool
    "check-true" = {
      expr = (checkHoas bool true_).tag;
      expected = "desc-con";
    };

    # () : Unit
    "check-tt" = {
      expr = (checkHoas unit tt).tag;
      expected = "tt";
    };

    # nil Nat : List Nat — descCon (listDesc nat) (inl …)
    "check-nil" = {
      expr = let t = checkHoas (listOf nat) (nil nat); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inl";
    };

    # cons Nat 0 (nil Nat) : List Nat — descCon (listDesc nat) (inr …)
    "check-cons" = {
      expr = let t = checkHoas (listOf nat) (cons nat zero (nil nat)); in "${t.tag}/${t.d.tag}";
      expected = "desc-con/inr";
    };

    # inl Nat Bool 0 : Sum Nat Bool — descCon (sumDesc nat bool) (inl …)
    "check-inl" = {
      expr = let t = checkHoas (sum nat bool) (inl nat bool zero); in
        "${t.tag}/${t.d.tag}";
      expected = "desc-con/inl";
    };

    # pair(0, true) : Σ(x:Nat).Bool
    "check-pair" = {
      expr = (checkHoas (sigma "x" nat (_: bool)) (pair zero true_)).tag;
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
        addZero = ind 0 (lam "n" nat (_: nat)) zero
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
    # Actually, since add is defined by NatElim and NatElim on S(k)
    # computes the step, we get: add(S(k), 0) = S(add(k, 0)). Combined
    # with ih : add(k,0) = k we need S(add(k,0)) = S(k). The J eliminator
    # can produce this.
    #
    # However, encoding cong via J in HOAS is complex. Let's use a
    # simpler approach: the checker normalizes both sides before
    # comparing, so if add(n,0) reduces to n for all n, we just need
    # Refl. But NatElim doesn't reduce symbolically. Instead, test a
    # concrete case: n=3.
    "theorem-3-plus-0-eq-3" = {
      expr = let
        three = succ (succ (succ zero));
        add_n_0 = ind 0 (lam "n" nat (_: nat)) zero
          (lam "k" nat (_: lam "ih" nat (ih: succ ih))) three;
        eqTy = eq nat add_n_0 three;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # Dependent pair: (0, Refl) : Σ(x:Nat). Eq(Nat, x, 0)
    "theorem-dep-pair" = {
      expr = let
        ty = sigma "x" nat (x: eq nat x zero);
        tm = pair zero refl;
      in (checkHoas ty tm).tag;
      expected = "pair";
    };

    # BoolElim type-checks: if true then 0 else 1 : Nat
    # `nat` is `mu natDesc`, so the inferred value tag is "VMu".
    "theorem-bool-elim" = {
      expr = let
        tm = boolElim 0 (lam "b" bool (_: nat)) zero (succ zero) true_;
      in (inferHoas (ann tm nat)).type.tag;
      expected = "VMu";
    };

    # ===== Description-based prelude integration =====
    # End-to-end semantic checks that the μ-description rebind of
    # Nat/List/Sum computes the same values as the primitive
    # representations under conv.

    # add(2, 3) = 5 on description-based Nat — exercises the rebound
    # `ind` adapter (let-bound P/B/S around descInd) plus Σ-η + ⊤-η in
    # the step.
    "integration-desc-nat-add-2-3" = {
      expr = let
        two   = succ (succ zero);
        three = succ (succ (succ zero));
        five  = succ (succ (succ (succ (succ zero))));
        addTm = lam "m" nat (m: lam "n" nat (n:
                  ind 0 (lam "_" nat (_: nat))
                      n
                      (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                      m));
        eqTy = eq nat (app (app addTm two) three) five;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # length [0, 0, 0] = 3 on description-based List — exercises the
    # rebound `listElim` adapter (let-bound P/N/C around descInd) on the
    # cons chain.
    "integration-desc-list-length-3" = {
      expr = let
        zeros = cons nat zero (cons nat zero (cons nat zero (nil nat)));
        three = succ (succ (succ zero));
        lenTm = listElim 0 nat (lam "_" (listOf nat) (_: nat))
                  zero
                  (lam "h" nat (_:
                   lam "t" (listOf nat) (_:
                   lam "ih" nat (ih: succ ih))))
                  zeros;
        eqTy = eq nat lenTm three;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # sumElim id id (inl Nat Nat 7) = 7 on description-based Sum —
    # exercises the rebound `sumElim` adapter (let-bound P/L/R around
    # descInd) with a constant motive Nat, where the trivial rih : ⊤ is
    # discharged in both arms.
    "integration-desc-sum-elim-inl" = {
      expr = let
        seven = succ (succ (succ (succ (succ (succ (succ zero))))));
        scrut = inl nat nat seven;
        motiveNat = lam "_" (sum nat nat) (_: nat);
        idNat = lam "n" nat (n: n);
        result = sumElim 0 nat nat motiveNat idNat idNat scrut;
        eqTy = eq nat result seven;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # sumElim id id (inr Nat Nat 4) = 4 — mirror test exercises the
    # right arm.
    "integration-desc-sum-elim-inr" = {
      expr = let
        four = succ (succ (succ (succ zero)));
        scrut = inr nat nat four;
        motiveNat = lam "_" (sum nat nat) (_: nat);
        idNat = lam "n" nat (n: n);
        result = sumElim 0 nat nat motiveNat idNat idNat scrut;
        eqTy = eq nat result four;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # W-type wellformedness: μ(wDesc Bool (b: if b then Unit else Void)) : U(0).
    # `wDesc A B = descArg 0 A (a: descPi 0 (B a) descRet)` — B is a
    # Nix meta-level function (A → U at the HOAS surface), applied at
    # elaboration time. Exercises the descPi case in the kernel's Desc
    # check rule; `k = 0` pins both domains to `U(0)`.
    "integration-desc-wtype-wellformed" = {
      expr = let
        wDesc = A: B: descArg 0 A (a: descPi 0 (B a) descRet);
        wBool = wDesc bool (a:
                  boolElim 1 (lam "_" bool (_: u 0)) unit void a);
      in (checkHoas (u 0) (mu wBool tt)).tag;
      expected = "mu";
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
        tm = elab (ind 0 (lam "n" nat (_: nat)) zero
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
      expected = "desc-con";
    };

    # ===== Primitive type elaboration =====

    "elab-string" = { expr = (elab string).tag; expected = "string"; };
    "elab-int" = { expr = (elab int_).tag; expected = "int"; };
    "elab-float" = { expr = (elab float_).tag; expected = "float"; };
    "elab-attrs" = { expr = (elab attrs).tag; expected = "attrs"; };
    "elab-path" = { expr = (elab path).tag; expected = "path"; };
    "elab-function" = { expr = (elab function_).tag; expected = "function"; };
    "elab-any" = { expr = (elab any).tag; expected = "any"; };

    # ===== Primitive literal elaboration =====

    "elab-string-lit" = { expr = (elab (stringLit "hi")).tag; expected = "string-lit"; };
    "elab-string-lit-value" = { expr = (elab (stringLit "hi")).value; expected = "hi"; };
    "elab-int-lit" = { expr = (elab (intLit 42)).tag; expected = "int-lit"; };
    "elab-int-lit-value" = { expr = (elab (intLit 42)).value; expected = 42; };
    "elab-float-lit" = { expr = (elab (floatLit 3.14)).tag; expected = "float-lit"; };
    "elab-float-lit-value" = { expr = (elab (floatLit 3.14)).value; expected = 3.14; };
    "elab-attrs-lit" = { expr = (elab attrsLit).tag; expected = "attrs-lit"; };
    "elab-path-lit" = { expr = (elab pathLit).tag; expected = "path-lit"; };
    "elab-fn-lit" = { expr = (elab fnLit).tag; expected = "fn-lit"; };
    "elab-any-lit" = { expr = (elab anyLit).tag; expected = "any-lit"; };

    # ===== Primitive kernel integration =====

    "check-string-lit" = {
      expr = (checkHoas string (stringLit "hello")).tag;
      expected = "string-lit";
    };
    "check-int-lit" = {
      expr = (checkHoas int_ (intLit 7)).tag;
      expected = "int-lit";
    };
    "check-float-lit" = {
      expr = (checkHoas float_ (floatLit 2.5)).tag;
      expected = "float-lit";
    };
    "check-attrs-lit" = {
      expr = (checkHoas attrs attrsLit).tag;
      expected = "attrs-lit";
    };
    "check-path-lit" = {
      expr = (checkHoas path pathLit).tag;
      expected = "path-lit";
    };
    "check-fn-lit" = {
      expr = (checkHoas function_ fnLit).tag;
      expected = "fn-lit";
    };
    "check-any-lit" = {
      expr = (checkHoas any anyLit).tag;
      expected = "any-lit";
    };

    # ===== Opaque lambda: trust boundary for Pi =====

    "elab-opaque-lam" = {
      expr = (elab (opaqueLam (x: x) (forall "x" nat (_: nat)))).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda checks at matching Pi type
    "opaque-lam-checks-at-pi" = {
      expr = let
        piTy = forall "x" nat (_: nat);
      in (checkHoas piTy (opaqueLam (x: x) piTy)).tag;
      expected = "opaque-lam";
    };

    # Opaque lambda rejects domain mismatch
    "opaque-lam-rejects-domain-mismatch" = {
      expr = let
        targetPi = forall "x" nat (_: nat);
        annotPi = forall "x" bool (_: nat);
      in (checkHoas targetPi (opaqueLam (x: x) annotPi)) ? error;
      expected = true;
    };

    # Opaque lambda rejects non-Pi target type
    "opaque-lam-rejects-non-pi" = {
      expr = (checkHoas nat (opaqueLam (x: x) (forall "x" nat (_: nat)))) ? error;
      expected = true;
    };

    # Opaque lambda infers Pi type from annotation
    "opaque-lam-infers-pi-type" = {
      expr = let
        piTy = forall "x" nat (_: nat);
        result = inferHoas (ann (opaqueLam (x: x) piTy) piTy);
      in result.type.tag;
      expected = "VPi";
    };

    # Opaque lambda quote roundtrip: eval → quote → eval = same structure
    "opaque-lam-quote-roundtrip" = {
      expr = let
        H = { inherit nat forall opaqueLam elab; };
        piTy = H.forall "x" H.nat (_: H.nat);
        tm = H.elab (H.opaqueLam (x: x) piTy);
        Q' = fx.tc.quote;
      in Q'.nf [] (Q'.nf [] tm) == Q'.nf [] tm;
      expected = true;
    };

    # Conv: same Nix function → conv-equal
    "opaque-lam-conv-reflexive" = {
      expr = let
        f = x: x;
        piTy = forall "x" nat (_: nat);
        tm1 = elab (opaqueLam f piTy);
        tm2 = elab (opaqueLam f piTy);
        E' = fx.tc.eval;
        C' = fx.tc.conv;
        v1 = E'.eval [] tm1;
        v2 = E'.eval [] tm2;
      in C'.conv 0 v1 v2;
      expected = true;
    };

    # Conv: different Nix functions → not conv-equal
    "opaque-lam-conv-distinct" = {
      expr = let
        f = x: x;
        g = x: succ x;
        piTy = forall "x" nat (_: nat);
        tm1 = elab (opaqueLam f piTy);
        tm2 = elab (opaqueLam g piTy);
        E' = fx.tc.eval;
        C' = fx.tc.conv;
        v1 = E'.eval [] tm1;
        v2 = E'.eval [] tm2;
      in C'.conv 0 v1 v2;
      expected = false;
    };

    # ----- Description-level acceptance tests -----

    # Acceptance A1: direct descElim on descRet infers motive(descRet).
    # With motive λ_:Desc. U→U, the result type is a VPi.
    "desc-elim-direct-infer" = {
      expr = let
        motive = lam "_" desc (_: forall "_" (u 0) (_: u 0));
        # Indexed on-case arities: onRet/onRec bind the index `j`, onPi
        # binds the index function `f : S → I`. onArg has no index binder
        # because `descArg` does not carry one.
        onRet  = lam "j" unit (_:
                 lam "X" (u 0) (_: unit));
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: desc)) (_:
                 lam "ih" (forall "s" S (_: forall "_" (u 0) (_: u 0))) (ih:
                 lam "X" (u 0) (X':
                   sigma "s" S (s: app (app ih s) X')))));
        onRec  = lam "j" unit (_:
                 lam "D" desc (_:
                 lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
                 lam "X" (u 0) (X':
                   sigma "_" X' (_: app ih X')))));
        onPi   = lam "S" (u 0) (S:
                 lam "f" (forall "_" S (_: unit)) (_:
                 lam "D" desc (_:
                 lam "ih" (forall "_" (u 0) (_: u 0)) (ih:
                 lam "X" (u 0) (X':
                   sigma "_" (forall "_" S (_: X')) (_: app ih X'))))));
        # `descRet` (= retI tt) is a bare canonical intro: its j = tt has
        # no infer rule under the bidirectional discipline. The outer `ann
        # _ desc` routes synthesis through CHECK against `Desc ⊤`, where
        # `check.nix`'s desc-ret rule accepts bare canonical forms.
        onPlus = lam "A" desc (_:
                 lam "B" desc (_:
                 lam "ihA" (forall "_" (u 0) (_: u 0)) (_:
                 lam "ihB" (forall "_" (u 0) (_: u 0)) (_:
                 lam "X" (u 0) (X':
                   sigma "_" X' (_: X'))))));
        tm = descElim 0 motive onRet onArg onRec onPi onPlus (ann descRet desc);
      in (inferHoas tm).type.tag;
      expected = "VPi";
    };

    # Motive body at universe level 1 is accepted for both `desc-ind` and
    # `desc-elim`. `checkMotive` descends the n-lam prefix and validates
    # the innermost codomain via `checkType`, which accepts any universe
    # level — the large-elim invariant across both description
    # eliminators.

    # desc-elim: motive `(D':Desc ⊤) → U(0)` with body `u 0 : U(1)` at the
    # innermost position. Exercises the universe-polymorphic path
    # documented at `check/infer.nix:289-294`.
    "descElim-u1-motive-checks" = {
      expr = let
        motive = lam "_" desc (_: u 0);
        onRet  = lam "j" unit (_: nat);
        onArg  = lam "S" (u 0) (_:
                 lam "T" (forall "_" (u 0) (_: desc)) (_:
                 lam "ih" (forall "s" (u 0) (_: u 0)) (_: nat)));
        onRec  = lam "j" unit (_:
                 lam "D" desc (_:
                 lam "ih" (u 0) (_: nat)));
        onPi   = lam "S" (u 0) (_:
                 lam "f" (forall "_" (u 0) (_: unit)) (_:
                 lam "D" desc (_:
                 lam "ih" (u 0) (_: nat))));
        onPlus = lam "A" desc (_:
                 lam "B" desc (_:
                 lam "ihA" (u 0) (_:
                 lam "ihB" (u 0) (_: nat))));
        tm = descElim 0 motive onRet onArg onRec onPi onPlus (ann descRet desc);
      in (inferHoas tm).type.tag;
      expected = "VU";
    };

    # interpHoasAt 0 ≡ interpF — compare nf of HOAS-elaborated term
    # against the quoted result of eval.nix's interp at the same D, X.

    # ⟦ret tt⟧(X)(tt) = Eq ⊤ tt tt — under I=⊤, the ret-leaf interpretation
    # is the propositional-equality witness collapsed by Unit-η.
    "interpHoasAt-matches-interpF-ret" = {
      expr = let
        Xfam = lam "_" unit (_: nat);
        lhsNf = Q.nf [] (elab (interpHoasAt 0 unit descRet Xfam tt));
        dVal = E.eval [] (elab descRet);
        xVal = E.eval [] (elab Xfam);
        rhsNf = Q.quote 0 (E.interp V.vLevelZero V.vUnit dVal xVal V.vTt);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦rec tt (ret tt)⟧(X)(tt) = Σ(_: X tt). Eq ⊤ tt tt
    "interpHoasAt-matches-interpF-rec-ret" = {
      expr = let
        D = descRec descRet;
        Xfam = lam "_" unit (_: bool);
        lhsNf = Q.nf [] (elab (interpHoasAt 0 unit D Xfam tt));
        rhsNf = Q.quote 0 (E.interp V.vLevelZero V.vUnit
          (E.eval [] (elab D)) (E.eval [] (elab Xfam)) V.vTt);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦arg bool (b: ret tt)⟧(X)(tt) = Σ(b:Bool). Eq ⊤ tt tt
    "interpHoasAt-matches-interpF-arg-bool" = {
      expr = let
        D = descArg 0 bool (_: descRet);
        Xfam = lam "_" unit (_: nat);
        lhsNf = Q.nf [] (elab (interpHoasAt 0 unit D Xfam tt));
        rhsNf = Q.quote 0 (E.interp V.vLevelZero V.vUnit
          (E.eval [] (elab D)) (E.eval [] (elab Xfam)) V.vTt);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ⟦pi bool (λ_.tt) (ret tt)⟧(X)(tt) = Σ(_: Bool→X tt). Eq ⊤ tt tt
    "interpHoasAt-matches-interpF-pi-bool" = {
      expr = let
        D = descPi 0 bool descRet;
        Xfam = lam "_" unit (_: nat);
        lhsNf = Q.nf [] (elab (interpHoasAt 0 unit D Xfam tt));
        rhsNf = Q.quote 0 (E.interp V.vLevelZero V.vUnit
          (E.eval [] (elab D)) (E.eval [] (elab Xfam)) V.vTt);
      in lhsNf == rhsNf;
      expected = true;
    };

    # `descArg k S T : desc^(max kS kT) I` — descArg at level 0 with
    # body returning desc^0 yields desc^0. Inferred type level matches
    # `VLevelZero` and the universe-of-the-type is `U(1)`.
    "descArg-level-zero-infers-desc-zero" = {
      expr = let
        r = inferHoas (descArg 0 nat (s: retI (ann tt unit)));
      in r.type.level.tag;
      expected = "VLevelZero";
    };
    # descArg at level 1 (with body returning desc^0) yields desc^1.
    # The contained `S = u 0 : U(1)` forces the description to live at
    # universe `suc 1 = U(2)`.
    "descArg-level-one-infers-desc-one" = {
      expr = let
        r = inferHoas (descArg 1 (u 0) (S: retI (ann tt unit)));
        lev = r.type.level;
      in lev.tag == "VLevelSuc" && lev.pred.tag == "VLevelZero";
      expected = true;
    };
    # Polymorphic descArg: `Π(k:Level). desc^(suc k) ⊤`. Witnesses that
    # the kVar at the descArg's level slot threads through to the
    # inferred result type's level — closing the universe-polymorphism
    # loop end-to-end.
    "descArg-level-polymorphic-checks" = {
      expr = (checkHoas
        (forall "k" level (k: descIAt (levelSuc k) unit))
        (lam "k" level (k: descArg (levelSuc k) (u k) (S: retI (ann tt unit))))) ? error;
      expected = false;
    };

    # descDesc : Π(k:Level). Desc^(suc k) ⊤ — type-checks at the
    # polymorphic universe-tracking forall (the descArg summand
    # quantifies over `S : U(k)` with leading level `(suc k)`, which
    # forces the description to live at `desc^(suc k) ⊤`), and
    # instantiates cleanly at sample levels k ∈ {0, 1, 2}.
    "descDesc-type-checks" = {
      expr = (checkHoas
        (forall "k" level (k: descAt (levelSuc k)))
        descDesc) ? error;
      expected = false;
    };
    "descDesc-at-level-zero" = {
      expr = (checkHoas
        (descAt (levelSuc levelZero))
        (app descDesc levelZero)).tag;
      expected = "app";
    };
    "descDesc-at-level-one" = {
      expr = (checkHoas
        (descAt (levelSuc (levelSuc levelZero)))
        (app descDesc (levelSuc levelZero))) ? error;
      expected = false;
    };
    "descDesc-at-level-two" = {
      expr = (checkHoas
        (descAt (levelSuc (levelSuc (levelSuc levelZero))))
        (app descDesc (levelSuc (levelSuc levelZero)))) ? error;
      expected = false;
    };

    # ===== iso reduction tests =====
    #
    # `iso : Π(k:Level). Iso (Desc^k ⊤) (μ(descDesc k) tt)` bundles
    # `to`, `from`, `toFrom`, `fromTo`. With strict equality at the
    # `descArg`/`descPi` level slot, every inhabitant of `Desc^k` is
    # homogeneous-k by typing, so the iso is genuinely polymorphic
    # rather than a section dressed in Π. These tests pin both the
    # polymorphic type-shape and the round-trip behaviour as
    # persistent regressions.

    # iso elaborates to a polymorphic Π over Level.
    "iso-type-checks-polymorphic" = {
      expr = (inferHoas iso).type.tag;
      expected = "VPi";
    };

    # iso instantiates at concrete levels — confirms the Π body
    # normalises to the Σ-bundle (the Iso record) at each k.
    "iso-at-level-zero-instantiates" = {
      expr = (inferHoas (app iso levelZero)).type.tag;
      expected = "VSigma";
    };
    "iso-at-level-one-instantiates" = {
      expr = (inferHoas (app iso (levelSuc levelZero))).type.tag;
      expected = "VSigma";
    };
    "iso-at-level-two-instantiates" = {
      expr = (inferHoas (app iso (levelSuc (levelSuc levelZero)))).type.tag;
      expected = "VSigma";
    };

    # Round-trip `from(to D) ≡ D` on prelude descriptions at k=0. Each
    # exercises a different mix of `descDesc 0`'s plus-coproduct
    # summands: natDesc hits ret + arg + rec; listDesc hits arg + rec
    # + plus; sumDesc hits arg + plus.
    "iso-roundtrip-natDesc-k0" = {
      expr = let
        iso0      = app iso levelZero;
        to0       = fst_ iso0;
        from0     = fst_ (snd_ iso0);
        roundTrip = app from0 (app to0 natDesc);
      in Q.nf [] (elab roundTrip) == Q.nf [] (elab natDesc);
      expected = true;
    };
    "iso-roundtrip-listDesc-bool-k0" = {
      expr = let
        iso0      = app iso levelZero;
        to0       = fst_ iso0;
        from0     = fst_ (snd_ iso0);
        D         = listDesc bool;
        roundTrip = app from0 (app to0 D);
      in Q.nf [] (elab roundTrip) == Q.nf [] (elab D);
      expected = true;
    };
    "iso-roundtrip-sumDesc-nat-bool-k0" = {
      expr = let
        iso0      = app iso levelZero;
        to0       = fst_ iso0;
        from0     = fst_ (snd_ iso0);
        D         = sumDesc nat bool;
        roundTrip = app from0 (app to0 D);
      in Q.nf [] (elab roundTrip) == Q.nf [] (elab D);
      expected = true;
    };

    # `toFrom natDesc : Eq (Desc^0 ⊤) (from(to natDesc)) natDesc` —
    # the proof component of the iso at a concrete input. Asserts
    # that the recursive proof structure built by `descInd` is
    # well-typed (the type tag is `VEq`).
    "iso-toFrom-natDesc-typechecks" = {
      expr = let
        iso0    = app iso levelZero;
        toFrom0 = fst_ (snd_ (snd_ iso0));
      in (inferHoas (app toFrom0 natDesc)).type.tag;
      expected = "VEq";
    };

    # ⟦natDesc⟧(X)(tt) — exercises the boolElim inside the arg body
    "interpHoasAt-matches-interpF-natDesc" = {
      expr = let
        Xfam = lam "_" unit (_: bool);
        lhsNf = Q.nf [] (elab (interpHoasAt 0 unit natDesc Xfam tt));
        rhsNf = Q.quote 0 (E.interp V.vLevelZero V.vUnit
          (E.eval [] (elab natDesc))
          (E.eval [] (elab Xfam)) V.vTt);
      in lhsNf == rhsNf;
      expected = true;
    };

    # allHoasAt 0 ≡ allTy — exercises the motive's d-binder annotation
    # `d : interpHoasAt 0 D (mu Douter)`, which onArg requires so that
    # `fst_ d` / `snd_ d` inside the body type-check under desc-elim's
    # paTy rule.

    # All ⊤ natDesc descRet P tt refl = ⊤ (no recursive arg; d : Eq ⊤ tt tt = refl)
    "allHoasAt-matches-allTy-ret" = {
      expr = let
        pHoas = lam "_i" unit (iArg: lam "_" (mu natDesc iArg) (_: u 0));
        lhsNf = Q.nf [] (elab (allHoasAt 0 0 unit natDesc descRet pHoas tt refl));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab descRet);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab refl);
        rhsNf = Q.quote 0 (E.allTy V.vLevelZero V.vLevelZero V.vUnit douter dsub pVal V.vTt dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # All ⊤ natDesc (rec tt (ret tt)) P tt (zero, refl) exercises onRec.
    # d : ⟦rec tt (ret tt)⟧(muFam) tt = Σ(_: μnatDesc tt). Eq ⊤ tt tt.
    "allHoasAt-matches-allTy-rec-ret" = {
      expr = let
        pHoas = lam "_i" unit (iArg: lam "_" (mu natDesc iArg) (_: u 0));
        zeroH = descCon natDesc tt (pair true_ refl);
        dH = pair zeroH refl;
        D = descRec descRet;
        lhsNf = Q.nf [] (elab (allHoasAt 0 0 unit natDesc D pHoas tt dH));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab D);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab dH);
        rhsNf = Q.quote 0 (E.allTy V.vLevelZero V.vLevelZero V.vUnit douter dsub pVal V.vTt dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # All ⊤ natDesc (arg bool (_: ret tt)) P tt (true_, refl) exercises
    # onArg — the case whose type-checking depends on the motive's
    # d-binder annotation. d inhabits Σ(b:Bool). Eq ⊤ tt tt.
    "allHoasAt-matches-allTy-arg-bool-ret" = {
      expr = let
        pHoas = lam "_i" unit (iArg: lam "_" (mu natDesc iArg) (_: u 0));
        D = descArg 0 bool (_: descRet);
        dH = pair true_ refl;
        lhsNf = Q.nf [] (elab (allHoasAt 0 0 unit natDesc D pHoas tt dH));
        douter = E.eval [] (elab natDesc);
        dsub = E.eval [] (elab D);
        pVal = E.eval [] (elab pHoas);
        dVal = E.eval [] (elab dH);
        rhsNf = Q.quote 0 (E.allTy V.vLevelZero V.vLevelZero V.vUnit douter dsub pVal V.vTt dVal);
      in lhsNf == rhsNf;
      expected = true;
    };

    # ===== Indexed-description acceptance (I = Nat / I = Bool) =====
    # These exercise the indexed kernel path directly — the `descI`/`retI`
    # /`recI`/`piI` primitives at non-⊤ indices — rather than the ⊤-slice
    # aliases (`desc`/`descRet`/`descRec`/`descPi`) that specialise I to
    # Unit.

    # `retI 3 : Desc Nat` — j = 3 inhabits I = Nat.
    "indexed-desc-ret-at-nat-checks" = {
      expr = (checkHoas (descI nat) (retI (natLit 3))).tag;
      expected = "desc-ret";
    };

    # `recI 2 (retI 3) : Desc Nat` — j = 2, subdesc `retI 3 : Desc Nat`.
    "indexed-desc-rec-at-nat-checks" = {
      expr = (checkHoas (descI nat) (recI (natLit 2) (retI (natLit 3)))).tag;
      expected = "desc-rec";
    };

    # `piI 0 Bool (λb. boolElim _ 2 3 b) (retI 4) : Desc Nat` — the index
    # function is bool-dependent, exercising the non-constant f case.
    "indexed-desc-pi-at-nat-dependent-f" = {
      expr = let
        fAnn = ann (lam "b" bool (b:
                 boolElim 0 (lam "_" bool (_: nat))
                          (natLit 2) (natLit 3) b))
                   (forall "_" bool (_: nat));
        D = piI 0 bool fAnn (retI (natLit 4));
      in (checkHoas (descI nat) D).tag;
      expected = "desc-pi";
    };

    # Rejection: `retI 3 : Desc Bool` fails — j = 3 is a Nat, not a Bool.
    # The `desc-ret` CHECK rule at check.nix:174-177 threads `ty.I` into
    # the check on `tm.j`, producing a type mismatch.
    "indexed-desc-ret-wrong-index-rejects" = {
      expr = (checkHoas (descI bool) (retI (natLit 3))) ? error;
      expected = true;
    };

    # `μ (retI 3 : Desc Nat) 3 : U(0)` — mu at the matching target index.
    "indexed-mu-at-nat-checks" = {
      expr = (checkHoas (u 0) (muI nat (retI (natLit 3)) (natLit 3))).tag;
      expected = "mu";
    };

    # ===== de Bruijn indices under Pi `_` binders =====
    # The value-level on-cases at `eval/desc.nix` (`interpOnArg`,
    # `interpOnPi`, `allOnPi`, `evOnPi`) each embed a Pi-domain
    # annotation whose codomain references the index type `I`. Under
    # the Pi's `_` binder the closure env is `[_, S, I]`, so references
    # to `I` must use `Var 2`; `Var 1` resolves to `S`, yielding a
    # description at the wrong index type and breaking any stuck-scrut
    # `vDescElim` that relies on these on-cases.
    #
    # `vDescElim` fully reduces on a concrete `VDesc*` and drops the
    # intermediate Pi-domain annotations from its result, so this
    # invariant is only observable when the scrut is `VNe + eDescElim`
    # — the frame quotes the motive and on-case VLams as-is. The tests
    # below force that shape by calling `E.interp` / `E.allTy` on a
    # bare neutral description (`vNe 0 []`) at `I = ⊤`.
    #
    # At `I = ⊤` the index value is `vUnit`, which quotes to the
    # literal `{tag="unit"}`. A `Var 2` slot in the on-case body
    # therefore materialises as `{tag="unit"}` after quote; a `Var 1`
    # slot would resolve to the fresh-Var binding for `S` and quote as
    # `{tag="var"; idx=1}`.
    #
    # Shared setup: build the quoted NF of `interp V.vUnit (vNe 0 []) X
    # tt` (or the analogous `allTy` call) and navigate to the descElim
    # node inside the spine.

    # `interpOnArg`: `T`'s Pi annotation is `Π _:S. Desc I`. The
    # Desc's `I` component must quote to unit, not to a fresh-Var
    # bound for `S`.
    "interpOnArg-T-codomain-quotes-to-I" = {
      expr = let
        T' = fx.tc.term;
        Dstuck = V.vNe 0 [];
        Xfam = V.vLam "_" V.vUnit (V.mkClosure [] T'.mkNat);
        qt = Q.quote 1 (E.interp V.vLevelZero V.vUnit Dstuck Xfam V.vTt);
        descElim = qt.fn.fn;
      in descElim.onArg.body.domain.codomain.I.tag;
      expected = "unit";
    };

    # `interpOnPi`: `f`'s Pi annotation is `Π _:S. I`. The codomain
    # must quote to unit, not to a fresh-Var bound for `S`.
    "interpOnPi-f-codomain-quotes-to-I" = {
      expr = let
        T' = fx.tc.term;
        Dstuck = V.vNe 0 [];
        Xfam = V.vLam "_" V.vUnit (V.mkClosure [] T'.mkNat);
        qt = Q.quote 1 (E.interp V.vLevelZero V.vUnit Dstuck Xfam V.vTt);
        descElim = qt.fn.fn;
      in descElim.onPi.body.domain.codomain.tag;
      expected = "unit";
    };

    # `allOnPi`: analogous probe via `E.allTy` on a stuck desc. `f`'s
    # Pi codomain must quote to unit.
    "allOnPi-f-codomain-quotes-to-I" = {
      expr = let
        T' = fx.tc.term;
        Dstuck = V.vNe 0 [];
        # P : (i:⊤) → μ Dstuck i → U — use a trivial constant.
        P = V.vLam "i" V.vUnit (V.mkClosure [] (T'.mkU T'.mkLevelZero));
        qt = Q.quote 1 (E.allTy V.vLevelZero V.vLevelZero V.vUnit Dstuck Dstuck P V.vTt V.vRefl);
        descElim = qt.fn.fn.fn;
      in descElim.onPi.body.domain.codomain.tag;
      expected = "unit";
    };

    # `evOnPi` carries the same `Var 2` invariant in the `everywhere`
    # family. It is exercised indirectly through `vDescIndF` whenever a
    # datatype elim runs on a neutral motive over a `π` field (e.g.
    # W-types, `piField`-containing datatypes); a dedicated stuck
    # `descInd` probe analogous to the three above would pin it
    # directly.

    # `E.allTy` accepts a non-concrete Level *value* — `mkAllMotive`
    # threads K through the closure env as a Val, so a level
    # expression like `max 0 0` (which doesn't reduce to a `VLevelSuc^n
    # VLevelZero` chain at the value layer) flows through verbatim and
    # ends up baked into the motive's universe annotation.
    "allTy-accepts-non-concrete-level" = {
      expr = let
        Dstuck = V.vNe 0 [];
        P = V.vLam "i" V.vUnit (V.mkClosure [] (fx.tc.term.mkU fx.tc.term.mkLevelZero));
        Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
        result = E.allTy Kval V.vLevelZero V.vUnit Dstuck Dstuck P V.vTt V.vRefl;
      in result.tag;
      expected = "VNe";
    };

    # The U-annotation embedded in the motive's Σ chain inhabits the
    # provided level Val verbatim — quoting the stuck allTy result and
    # navigating to the motive's body universe shows the `VLevelMax`
    # node faithfully preserved (rather than coerced to a constant).
    "allTy-non-concrete-level-preserved-in-quote" = {
      expr = let
        Dstuck = V.vNe 0 [];
        P = V.vLam "i" V.vUnit (V.mkClosure [] (fx.tc.term.mkU fx.tc.term.mkLevelZero));
        Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
        qt = Q.quote 1 (E.allTy Kval V.vLevelZero V.vUnit Dstuck Dstuck P V.vTt V.vRefl);
        descElim = qt.fn.fn.fn;
      in descElim.motive.body.codomain.codomain.codomain.level.tag;
      expected = "level-max";
    };

    # ===== Datatype macro =====
    # UnitDT: the n=1 degenerate case — singleton constructor with no
    # fields. D = descRet, T = μ descRet, tt = descCon D tt, elim P step
    # scrut reduces to step. Exercises the leaf dispatchStep with no
    # field or IH projection, and the n=1 no-tag encoding.

    "datatype-unit-spec-name" = {
      expr = (datatype "Unit" [ (con "tt" []) ]).name;
      expected = "Unit";
    };
    "datatype-unit-spec-meta" = {
      expr = (datatype "Unit" [ (con "tt" []) ])._dtypeMeta;
      expected = {
        name = "Unit";
        indexed = false;
        indexTy = unitPrim;
        cons = [{ name = "tt"; fields = []; }];
      };
    };
    # The macro emits D as `ann <spine> desc` so the outer Tm is an `ann`;
    # `.term` is the raw spine. For a single zero-field con, spine = descRet.
    "datatype-unit-D-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).D).term.tag;
      expected = "desc-ret";
    };
    "datatype-unit-T-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-elab" = {
      expr = (elab (datatype "Unit" [ (con "tt" []) ]).tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Unit" [ (con "tt" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-unit-tt-check-T" = {
      expr = let U = datatype "Unit" [ (con "tt" []) ];
             in (checkHoas U.T U.tt).tag;
      expected = "desc-con";
    };
    "datatype-unit-elim-reduces-to-step" = {
      # elim (λ_:T. ⊤) tt U.tt  ≡nf≡  tt
      # The motive is constantly ⊤, the step is `tt : ⊤`, the scrutinee
      # is U.tt. descInd on the single-constructor μ descRet reduces
      # straight to the step (no field projection, no IH).
      expr = let
        U = datatype "Unit" [ (con "tt" []) ];
        applied = app (app (app (U.elim 0)
          (lam "x" U.T (_: unit)))
          tt)
          U.tt;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # The macro elim must be INFERABLE as a closed term — bare lam
    # cascades are checkable-only in the bidirectional kernel, so the
    # macro wraps the elim in `ann <body> <full-Π-type>`. This test
    # fires an applied elim through `checkHoas` to prove the chain of
    # `app`s type-checks; nf-equivalence
    # (datatype-unit-elim-reduces-to-step) bypasses checking and would
    # silently mask a non-inferable elim.
    "datatype-unit-elim-checks" = {
      expr = let
        U = datatype "Unit" [ (con "tt" []) ];
        applied = app (app (app (U.elim 0)
          (lam "x" U.T (_: unit)))
          tt)
          U.tt;
      in (checkHoas unit applied).tag;
      expected = "app";
    };
    # Direct inference of the closed elim: confirms `ann` pins a Π type
    # the kernel can recover without reducing the body.
    "datatype-unit-elim-infers-pi" = {
      expr = let U = datatype "Unit" [ (con "tt" []) ];
             in (inferHoas (U.elim 0)).type.tag;
      expected = "VPi";
    };
    "datatype-rejects-n0" = {
      expr = (builtins.tryEval (datatype "Empty" [])).success;
      expected = false;
    };
    "datatype-rejects-duplicate-cons" = {
      expr = (builtins.tryEval
               (datatype "Dup" [ (con "a" []) (con "a" []) ])).success;
      expected = false;
    };

    # BoolDT: n=2 with both arms zero-field. Exercises:
    #   - spineDesc n>=2 (right-associated Bool tag spine).
    #   - encodeTag n>=2 (true_/false_ tag prefixes).
    #   - dispatchStep n>=2 branch case with leaf onTrue / onFalse,
    #     ctx threaded with `pair false_` for the second arm.
    "datatype-bool-spec-name" = {
      expr = (datatype "Bool" [ (con "true" []) (con "false" []) ]).name;
      expected = "Bool";
    };
    "datatype-bool-spec-meta" = {
      expr = (datatype "Bool" [ (con "true" []) (con "false" []) ])._dtypeMeta;
      expected = {
        name = "Bool";
        indexed = false;
        indexTy = unitPrim;
        cons = [
          { name = "true";  fields = []; }
          { name = "false"; fields = []; }
        ];
      };
    };
    # D = ann (descArg bool (b: boolElim _ descRet descRet b)) desc — the
    # Two zero-field ctors produce a plus-coproduct spineDesc with both
    # summands degenerate to descRet. ann-wrapper routes D through CHECK;
    # `.term` is the raw spine.
    "datatype-bool-D-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).D).term.tag;
      expected = "desc-plus";
    };
    "datatype-bool-T-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-elab" = {
      expr = (elab (datatype "Bool" [ (con "true" []) (con "false" []) ]).false).tag;
      expected = "desc-con";
    };
    # Macro D matches the canonical bool-fold structure: plus of two
    # descRet summands. Compared against a hand-written equivalent via
    # nf to absorb α-renaming.
    "datatype-bool-D-matches-handwritten" = {
      expr = let
        macroD = (datatype "Bool" [ (con "true" []) (con "false" []) ]).D;
        handD = plus descRet descRet;
      in Q.nf [] (elab macroD) == Q.nf [] (elab handD);
      expected = true;
    };
    # True constructor's payload commits the 0th (inl) summand of the
    # plus tree, with witness refl : Eq ⊤ tt tt at the ret-leaf.
    "datatype-bool-true-payload-shape" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
      in (elab B.true).d.tag;
      expected = "inl";
    };
    # False constructor commits the 1st (inr) summand.
    "datatype-bool-false-payload-shape" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
      in (elab B.false).d.tag;
      expected = "inr";
    };
    "datatype-bool-T-check-U0" = {
      expr = (checkHoas (u 0) (datatype "Bool" [ (con "true" []) (con "false" []) ]).T).tag;
      expected = "mu";
    };
    "datatype-bool-true-check-T" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (checkHoas B.T B.true).tag;
      expected = "desc-con";
    };
    "datatype-bool-false-check-T" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (checkHoas B.T B.false).tag;
      expected = "desc-con";
    };
    # Closed elim is inferable as a Π type via the ann wrapper.
    "datatype-bool-elim-infers-pi" = {
      expr = let B = datatype "Bool" [ (con "true" []) (con "false" []) ];
             in (inferHoas (B.elim 0)).type.tag;
      expected = "VPi";
    };
    # Reduction on the true scrutinee selects step_true.
    # Motive: const ⊤. step_true = tt : ⊤. step_false = tt : ⊤.
    # elim P step_true step_false B.true ≡nf≡ tt.
    "datatype-bool-elim-reduces-true" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app (B.elim 0)
          (lam "_" B.T (_: unit)))
          tt)  # step_true
          tt)  # step_false
          B.true;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # Reduction on the false scrutinee selects step_false.
    # Discriminating motive (P b = if b then ⊤ else ⊤ — both arms
    # collapse to ⊤ because we have no second monomorphic ground type
    # in scope at U0 to distinguish them, but the dispatch chain is
    # still exercised structurally and verified by separately checking
    # that the elim chains through a non-collapsing motive in the next
    # test).
    "datatype-bool-elim-reduces-false" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app (B.elim 0)
          (lam "_" B.T (_: unit)))
          tt)
          tt)
          B.false;
      in Q.nf [] (elab applied) == Q.nf [] (elab tt);
      expected = true;
    };
    # Distinguishing motive: P b = T (the BoolDT type itself).
    # step_true = B.false, step_false = B.true (negation).
    # elim P (B.false) (B.true) B.true ≡nf≡ B.false.
    # elim P (B.false) (B.true) B.false ≡nf≡ B.true.
    # This proves the boolElim dispatch genuinely picks the correct arm
    # rather than collapsing both to a common normal form.
    "datatype-bool-elim-negates-true" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        neg = scrut: app (app (app (app (B.elim 0)
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          scrut;
      in Q.nf [] (elab (neg B.true)) == Q.nf [] (elab B.false);
      expected = true;
    };
    "datatype-bool-elim-negates-false" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        neg = scrut: app (app (app (app (B.elim 0)
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          scrut;
      in Q.nf [] (elab (neg B.false)) == Q.nf [] (elab B.true);
      expected = true;
    };
    # Applied negation chain through checkHoas: proves the entire
    # `app`-cascade is type-checkable (the elim's ann wrapper makes the
    # head of the chain inferable; each step's check rule then
    # validates).
    "datatype-bool-elim-checks-applied" = {
      expr = let
        B = datatype "Bool" [ (con "true" []) (con "false" []) ];
        applied = app (app (app (app (B.elim 0)
          (lam "_" B.T (_: B.T)))
          B.false)
          B.true)
          B.true;
      in (checkHoas B.T applied).tag;
      expected = "app";
    };

    # NatDT: n=2 with one fielded constructor (succ takes a recField).
    # Exercises:
    #   - conDesc with recField (descRec extension).
    #   - mkCtor curried lam over fields, ann-wrapped against the
    #     constructor's Π type.
    #   - stepTyOf with fielded cons: Π over the field, then Π over the
    #     IH, terminating in P (succ pred).
    #   - buildStepApply with field projection (fst payload) and IH
    #     projection (fst payloadIH).
    #   - nf-equivalence against the inline natElim adapter. Both
    #     eval-discard their type scaffolding (let_ vs ann) so the
    #     descInd reductions agree.
    "datatype-nat-spec-name" = {
      expr = (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).name;
      expected = "Nat";
    };
    "datatype-nat-spec-meta" = {
      expr = (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ])._dtypeMeta;
      expected = {
        name = "Nat";
        indexed = false;
        indexTy = unitPrim;
        cons = [
          { name = "zero"; fields = []; }
          { name = "succ"; fields = [ { name = "pred"; kind = "recAt"; } ]; }
        ];
      };
    };
    # Macro D matches the prelude `natDesc` exactly via nf.
    "datatype-nat-D-matches-natDesc" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
      in Q.nf [] (elab N.D) == Q.nf [] (elab natDesc);
      expected = true;
    };
    "datatype-nat-T-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).T).tag;
      expected = "mu";
    };
    "datatype-nat-T-check-U0" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas (u 0) N.T).tag;
      expected = "mu";
    };
    # Zero commits the 0th (inl) summand of the plus tree; the ret-leaf
    # witness is refl : Eq ⊤ tt tt.
    "datatype-nat-zero-payload" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
      in (elab N.zero).d.tag;
      expected = "inl";
    };
    "datatype-nat-zero-checks" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas N.T N.zero).tag;
      expected = "desc-con";
    };
    # Constructor succ is fielded — the macro emits an ann-wrapped
    # curried lam, so its top-level _htag is "ann" until applied.
    "datatype-nat-succ-elab" = {
      expr = (elab (datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]).succ).tag;
      expected = "ann";
    };
    "datatype-nat-succ-infers-pi" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (inferHoas N.succ).type.tag;
      expected = "VPi";
    };
    # Applied succ commits the 1st (inr) summand, carrying the pred
    # recursive argument paired with the ret-leaf refl witness.
    "datatype-nat-succ-applied-payload" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        macroSucc = app N.succ N.zero;
      in (Q.nf [] (elab macroSucc)).d.tag;
      expected = "inr";
    };
    # Saturated macro-ctor application flattens at elab time to a flat
    # `desc-con` Tm (shared-dTm chain of length 1). The kernel checks
    # it against the type and returns the reconstructed desc-con term.
    "datatype-nat-succ-applied-checks" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (checkHoas N.T (app N.succ N.zero)).tag;
      expected = "desc-con";
    };
    "datatype-nat-elim-infers-pi" = {
      expr = let N = datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ]; in (inferHoas (N.elim 0)).type.tag;
      expected = "VPi";
    };

    # nf-equivalence between the macro elim and the inline `ind` adapter
    # for representative (M, B, S, scrut) vectors. Both sides
    # eval-discard their type scaffolding (let_ vs ann), so any
    # divergence after nf is a genuine semantic regression in the
    # macro.
    #
    # Motive M = (λ_:nat. nat). Base B = zero. Step varies per test.
    #
    # Scrutinee 1: zero. The descInd's onTrue branch fires; macro
    # buildStepApply returns step_zero (B), the adapter's onTrue
    # returns base.
    "datatype-nat-elim-nf-gate-zero" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: ih));
        scrut = zero;
        macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
        adapterApplied = ind 0 M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 2: succ zero. Both onFalse branches fire; macro
    # projects (fst r, fst rih) and applies step_succ; the adapter
    # emits the same projection chain inline.
    "datatype-nat-elim-nf-gate-one" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: ih));
        scrut = succ zero;
        macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
        adapterApplied = ind 0 M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 3: succ (succ zero). Two layers of trampoline; checks
    # the nested descInd reduction agrees.
    "datatype-nat-elim-nf-gate-two" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
        scrut = succ (succ zero);
        macroApplied = app (app (app (app (N.elim 0) M) B) S) scrut;
        adapterApplied = ind 0 M B S scrut;
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # Scrutinee 4: a fresh-variable neutral scrutinee. This is the
    # critical case — neutral scrutinees do NOT reduce, so both terms
    # must produce the SAME stuck normal form (descInd D motive stepF
    # neutral) modulo α. Distinguishes "macro and adapter happen to
    # agree on closed scrutinees" from "macro and adapter agree as
    # terms".
    "datatype-nat-elim-nf-gate-neutral" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        M = lam "_" nat (_: nat);
        B = zero;
        S = lam "k" nat (k: lam "ih" nat (ih: succ ih));
        # Fresh-variable neutral: the elim is wrapped in an outer lam
        # that binds `n : nat`, then applied to that bound variable. nf
        # cannot reduce it since `n` is neutral.
        macroAtN = lam "n" nat (n:
          app (app (app (app (N.elim 0) M) B) S) n);
        adapterAtN = lam "n" nat (n: ind 0 M B S n);
      in Q.nf [] (elab macroAtN) == Q.nf [] (elab adapterAtN);
      expected = true;
    };

    # End-to-end semantic test: addition on macro-Nat reduces
    # correctly. add(2, 3) = 5 via the macro elim and macro
    # constructors, exercising the IH projection through actual
    # recursion rather than just nf comparison against the inline
    # adapter.
    "datatype-nat-elim-add-2-3" = {
      expr = let
        N = datatype "Nat" [
          (con "zero" [])
          (con "succ" [ (recField "pred") ])
        ];
        # add m n = elim (λ_. nat) n (λk.λih. succ ih) m
        # Recursing on m: zero case → n; succ k case → succ (add k n).
        add = m: n:
          app (app (app (app (N.elim 0)
            (lam "_" N.T (_: N.T)))
            n)
            (lam "k" N.T (k: lam "ih" N.T (ih: app N.succ ih))))
            m;
        two = app N.succ (app N.succ N.zero);
        three = app N.succ (app N.succ (app N.succ N.zero));
        five = app N.succ (app N.succ (app N.succ (app N.succ (app N.succ N.zero))));
      in Q.nf [] (elab (add two three)) == Q.nf [] (elab five);
      expected = true;
    };

    # Universe-K-1 motive: `N.elim 1` applied to a motive that returns
    # `U(0)` inhabits a step type whose All-hypothesis lands in `U(1)`.
    # Exercises the K-threading pipeline at a concrete K — HOAS allHoasAt
    # emits `u 1`, kernel mkAllMotive bakes `term.mkU (mkLevelSuc mkLevelZero)`, and the
    # motive level recovered from `checkMotive` lines up.
    "datatype-nat-elim-universe-one" = {
      expr = let
        N = datatype "Nat" [ (con "zero" []) (con "succ" [ (recField "pred") ]) ];
        M = lam "_" N.T (_: u 0);
        B = unit;
        S = lam "_k" N.T (_: lam "ih" (u 0) (ih: ih));
        applied = app (app (app (app (N.elim 1) M) B) S) N.zero;
      in (checkHoas (u 0) applied).tag;
      expected = "app";
    };

    # Same shape through the HOAS `ind` combinator, which threads K into
    # `N.elim` and allHoasAt identically. `ind` wraps the elim application
    # in a `let_` chain that lifts P/B/S to inferable positions, so the
    # elaborated tag is `let` rather than the bare `app` spine.
    "ind-universe-one" = {
      expr = (checkHoas (u 0) (ind 1 (lam "_" nat (_: u 0)) unit
                                 (lam "_" nat (_: lam "_" (u 0) (ih: ih))) zero)).tag;
      expected = "let";
    };

    # HOAS `ind` accepts a HOAS Level term in its `k` slot (not just a
    # Nix-meta Int). `levelMax levelZero levelZero` is conv-equal to
    # `levelZero` under the kernel's Level normaliser, so the motive
    # `λ_:nat. nat` (returning U(0)) type-checks at this K — but the
    # elaborated Tm carries a `level-max` node end-to-end, exercising
    # the polymorphic-K route from HOAS through `elaborateLevel` and
    # down to `mkAllMotive`'s closure-env-threaded `K_val`.
    "ind-hoas-level-term-accepted" = {
      expr = (checkHoas nat
        (ind (levelMax levelZero levelZero)
             (lam "_" nat (_: nat))
             zero
             (lam "_" nat (_: lam "_" nat (ih: succ ih)))
             zero)).tag;
      expected = "let";
    };

    # The level expression `levelMax levelZero levelZero` survives
    # elaborate verbatim — `elaborateLevel` recurses on the HOAS
    # construct rather than coercing it to a constant. The motive's
    # universe annotation in the elaborated `let_ "P" piMotiveTy …`
    # therefore carries a `level-max` Tm.
    "ind-hoas-level-term-elab-shape" = {
      expr = let
        tm = elab (ind (levelMax levelZero levelZero)
                       (lam "_" nat (_: nat))
                       zero
                       (lam "_" nat (_: lam "_" nat (ih: succ ih)))
                       zero);
      in tm.type.codomain.level.tag;
      expected = "level-max";
    };

    # Universe-polymorphic eliminator: a function quantifying over a
    # bound `k : Level`, with motive `P : nat → U(k)` returning at the
    # bound level. `ind k …` in the body forces `descInd`'s infer rule
    # to thread a `vNe` Level Val through `mkAllMotive`'s closure env
    # — concrete-level coercion at the call site cannot apply, so the
    # K-as-Val discipline is exercised end-to-end.
    "ind-polymorphic-motive-k-bound" = {
      expr = let
        ty = forall "k" level (k:
             forall "P" (forall "_" nat (_: u k)) (P:
             forall "B" (app P zero) (_:
             forall "S" (forall "n" nat (n:
                          forall "_" (app P n) (_: app P (succ n)))) (_:
             forall "n" nat (n: app P n)))));
        body = lam "k" level (k:
               lam "P" (forall "_" nat (_: u k)) (P:
               lam "B" (app P zero) (B:
               lam "S" (forall "n" nat (n:
                         forall "_" (app P n) (_: app P (succ n)))) (S:
               lam "n" nat (n: ind k P B S n)))));
      in (checkHoas ty body).tag;
      expected = "lam";
    };

    # `reifyLevel` is the inverse of `elaborateLevel`: kernel Level
    # value → HOAS Level node. Concrete chains, `vLevelMax`, and `vNe`
    # (a bound Level variable in the surrounding context) all reify
    # without throwing — closing the round-trip kernel ↔ HOAS for
    # universe levels.
    "reifyLevel-zero" = {
      expr = (fx.tc.hoas.reifyLevel V.vLevelZero)._htag;
      expected = "level-zero";
    };
    "reifyLevel-suc" = {
      expr = (fx.tc.hoas.reifyLevel (V.vLevelSuc V.vLevelZero))._htag;
      expected = "level-suc";
    };
    "reifyLevel-max" = {
      expr = (fx.tc.hoas.reifyLevel (V.vLevelMax V.vLevelZero V.vLevelZero))._htag;
      expected = "level-max";
    };
    # A neutral Level (a bound Level Var at de Bruijn level 0) reifies
    # to a marker. Wrapping the marker under a fresh `forall` that
    # introduces a Level binder at depth 0 elaborates the marker back
    # to `mkVar 0` — proving the round-trip Var → marker → Var.
    "reifyLevel-vNe-round-trips-to-Var" = {
      expr = let
        marker = fx.tc.hoas.reifyLevel (V.vNe 0 [ ]);
        wrapped = forall "k" level (_: u marker);
      in (elab wrapped).codomain.level.tag;
      expected = "var";
    };
    # Whole-pipeline closure: `reifyType` on a `VU` whose level is
    # `vLevelMax` no longer throws via the spine analysis. The result
    # is a HOAS `u` node whose level slot carries the reified Level
    # term verbatim.
    "reifyType-VU-non-concrete-level" = {
      expr = let
        Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
        uVal = V.vU Kval;
      in (fx.tc.elaborate.reifyType uVal)._htag;
      expected = "U";
    };
    "reifyType-VU-non-concrete-level-preserves-max" = {
      expr = let
        Kval = V.vLevelMax V.vLevelZero V.vLevelZero;
        uVal = V.vU Kval;
      in (fx.tc.elaborate.reifyType uVal).level._htag;
      expected = "level-max";
    };

    # natToLevel surface combinator — accepts an Int and elaborates to
    # `mkNatToLevel (mkSucc^n mkZero)`, which reduces definitionally to
    # `mkLevelSuc^n mkLevelZero` per Decision #2 corollary.
    "elab-natToLevel-zero-tag" = {
      expr = (elab (natToLevel 0)).tag;
      expected = "nat-to-level";
    };
    "elab-natToLevel-zero-payload" = {
      expr = (elab (natToLevel 0)).n.tag;
      expected = "zero";
    };
    "elab-natToLevel-3-payload" = {
      # `natToLevel 3` elaborates to a term whose `n` is `succ^3 zero`.
      expr = (elab (natToLevel 3)).n.pred.pred.pred.tag;
      expected = "zero";
    };
    "natToLevel-3-checks-at-Level" = {
      # End-to-end: surface `natToLevel 3` checks against `level`.
      expr = (checkHoas level (natToLevel 3)).tag;
      expected = "nat-to-level";
    };
    "natToLevel-3-reduces-to-suc3-zero" = {
      # The bridge's defining equation: `natToLevel 3 ≡ suc^3 zero` at
      # the Level sort, decided by conv after eval.
      expr = let
        lhs = E.eval [] (elab (natToLevel 3));
        rhs = V.vLevelSuc (V.vLevelSuc (V.vLevelSuc V.vLevelZero));
      in fx.tc.conv.conv 0 lhs rhs;
      expected = true;
    };
    "u-natToLevel-1-elaborates-as-U-of-suc-zero" = {
      # `u (natToLevel 1)` is a universe `U(natToLevel 1) ≡ U(1)` —
      # exercised through the level slot, normalised at conv time.
      expr = let
        ty = E.eval [] (elab (u (natToLevel 1)));
      in fx.tc.conv.conv 0 ty (V.vU (V.vLevelSuc V.vLevelZero));
      expected = true;
    };


    # ===== ListDT tests (datatypeP; parameter A; linear-recursive) =====

    # ListDT: 1-param polymorphic, 2 constructors. `cons` carries one
    # data field (head : A) and one recursive field (tail : List A) —
    # this is the profile linearProfile accepts as Just [A].
    "datatype-list-spec-name" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in L.name;
      expected = "List";
    };
    "datatype-list-spec-params" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in builtins.length L.params;
      expected = 1;
    };
    # Macro D applied to nat is nf-equivalent to the hand-written
    # `listDesc nat`. The polymorphic λA. mono.D fully applies to give
    # the per-instance description; nf normalizes through the
    # `app (ann (λA. ...) ty) nat` β-redex, the ann wrapper, and the
    # listDesc's Bool-fold scaffold.
    "datatype-list-D-matches-listDesc" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in Q.nf [] (elab (app L.D nat)) == Q.nf [] (elab (listDesc nat));
      expected = true;
    };
    # Polymorphic T at A=nat elaborates to a μ value.
    "datatype-list-T-nat-elab" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in (elab (app L.T nat)).tag;
      # app of a lambda-annotated type — elaborated as an app tree.
      # The outer elab tag is "app" (not yet β-reduced); eval reduces
      # to VMu.
      expected = "app";
    };
    # `ListDT.nil nat` type-checks against `ListDT.T nat`.
    "datatype-list-nil-checks" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        result = checkHoas (app L.T nat) (app L.nil nat);
      in !(result ? error);
      expected = true;
    };
    # `ListDT.cons nat zero (ListDT.nil nat)` type-checks.
    "datatype-list-cons-one-checks" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        hoasVal = app (app (app L.cons nat) zero) (app L.nil nat);
        result = checkHoas (app L.T nat) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic cons at A=nat infers to a Π over head, tail (curried).
    "datatype-list-cons-at-nat-infers-pi" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
      in (inferHoas (app L.cons nat)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro ListDT.elim against the inline
    # `listElim` adapter on the empty list. Motive (λ_. nat), onNil =
    # zero, onCons returns `succ head` to differentiate base from step.
    "datatype-list-elim-nf-gate-empty" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        onNil = zero;
        onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
        scrut = app L.nil nat;
        macroApplied = app (app (app (app (app (L.elim 0) nat) M) onNil) onCons) scrut;
        adapterApplied = listElim 0 nat M onNil
          (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
          (nil nat);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a one-element list: cons zero nil. Both sides reduce
    # to `succ zero` after normalization.
    "datatype-list-elim-nf-gate-one" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        onNil = zero;
        onCons = lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)));
        scrut = app (app (app L.cons nat) zero) (app L.nil nat);
        macroApplied = app (app (app (app (app (L.elim 0) nat) M) onNil) onCons) scrut;
        adapterApplied = listElim 0 nat M zero
          (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
          (cons nat zero (nil nat));
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a fresh-variable neutral list scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
    "datatype-list-elim-nf-gate-neutral" = {
      expr = let
        L = datatypeP "List" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "nil"  [])
            (con "cons" [ (field "head" A) (recField "tail") ])
          ]);
        M = lam "_" (app L.T nat) (_: nat);
        macroAtL = lam "l" (app L.T nat) (l:
          app (app (app (app (app (L.elim 0) nat) M) zero)
            (lam "h" nat (h: lam "t" (app L.T nat) (t: lam "ih" nat (ih: succ h)))))
            l);
        adapterAtL = lam "l" (listOf nat) (l:
          listElim 0 nat (lam "_" (listOf nat) (_: nat)) zero
            (lam "h" nat (h: lam "t" (listOf nat) (t: lam "ih" nat (ih: succ h))))
            l);
      in Q.nf [] (elab macroAtL) == Q.nf [] (elab adapterAtL);
      expected = true;
    };

    # Tree: non-linear recursive (node has two rec fields). The peel's
    # linearProfile on the false-branch description `descRec (descRec
    # descRet)` returns null; the check falls through to non-trampolined
    # descCon handling without crashing. A payload-shape classifier
    # would mis-read `pair false (pair LEFTREC (pair RIGHTREC tt))` as
    # a list-shape head+rec and crash on the null elemVal —
    # description-shape dispatch avoids that class of miscount.
    "peel-declines-tree-shape" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        result = checkHoas (app Tree.T nat) nodeLL;
      in !(result ? error);
      expected = true;
    };

    # ===== SumDT tests (datatypeP; two parameters; non-recursive) =====

    # SumDT: 2-param polymorphic, 2 constructors. Each constructor
    # carries a single data field and no recursive field — exercises
    # the nParams=2 branch of datatypeP's parameter loop. chainShapeOk
    # requires a final rec field, so the chain-flattener declines on
    # `inl`/`inr` and the regular ann-lam cascade handles every
    # application.
    "datatype-sum-spec-name" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in S.name;
      expected = "Sum";
    };
    "datatype-sum-spec-params" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in builtins.length S.params;
      expected = 2;
    };
    # Macro D applied to (nat, bool) is nf-equivalent to the
    # hand-written `sumDesc nat bool`. The polymorphic λA.λB. mono.D
    # fully applies to give the per-instance description; nf normalizes
    # through the two `app (ann (λ. ...) ty) _` β-redexes, the ann
    # wrappers, and the sumDesc Bool-fold scaffold.
    "datatype-sum-D-matches-sumDesc" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in Q.nf [] (elab (app (app S.D nat) bool))
         == Q.nf [] (elab (sumDesc nat bool));
      expected = true;
    };
    # Polymorphic T fully applied to (nat, bool) elaborates as an app
    # tree (the outer ann (λA.λB. ...) ty awaiting two β-reductions);
    # eval reduces it to VMu.
    "datatype-sum-T-applied-elab" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in (elab (app (app S.T nat) bool)).tag;
      expected = "app";
    };
    # `SumDT.inl nat bool zero` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inl-checks" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        hoasVal = app (app (app S.inl nat) bool) zero;
        result = checkHoas (app (app S.T nat) bool) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # `SumDT.inr nat bool true_` type-checks against `SumDT.T nat bool`.
    "datatype-sum-inr-checks" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        hoasVal = app (app (app S.inr nat) bool) true_;
        result = checkHoas (app (app S.T nat) bool) hoasVal;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic inl partially applied to its two type parameters
    # infers to a Π over `value` — the curried single-data-field
    # signature.
    "datatype-sum-inl-at-types-infers-pi" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
      in (inferHoas (app (app S.inl nat) bool)).type.tag;
      expected = "VPi";
    };
    # nf-equivalence of the macro SumDT.elim against the inline
    # `sumElim` adapter on an `inl` scrutinee. Motive picks `nat`
    # (constant), onLeft is identity on Nat, onRight is the Bool→Nat
    # true↦zero false↦zero constant — both sides reduce to `zero` on
    # `inl nat bool zero`.
    "datatype-sum-elim-nf-gate-inl" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        scrut = app (app (app S.inl nat) bool) zero;
        macroApplied =
          app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) scrut;
        adapterApplied =
          sumElim 0 nat bool M onLeft onRight (inl nat bool zero);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-equivalence on an `inr` scrutinee. Same motive/cases; this
    # exercises the false-branch of the descInd boolElim dispatch.
    "datatype-sum-elim-nf-gate-inr" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        scrut = app (app (app S.inr nat) bool) true_;
        macroApplied =
          app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) scrut;
        adapterApplied =
          sumElim 0 nat bool M onLeft onRight (inr nat bool true_);
      in Q.nf [] (elab macroApplied) == Q.nf [] (elab adapterApplied);
      expected = true;
    };
    # nf-gate on a fresh-variable neutral Sum scrutinee — pins the
    # stuck normal form equality under the macro vs the adapter.
    "datatype-sum-elim-nf-gate-neutral" = {
      expr = let
        S = datatypeP "Sum"
          [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
          (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
            (con "inl" [ (field "value" A) ])
            (con "inr" [ (field "value" B) ])
          ]);
        M = lam "_" (app (app S.T nat) bool) (_: nat);
        onLeft  = lam "a" nat  (a: a);
        onRight = lam "b" bool (_: zero);
        macroAtS = lam "s" (app (app S.T nat) bool) (s:
          app (app (app (app (app (app (S.elim 0) nat) bool) M) onLeft) onRight) s);
        adapterAtS = lam "s" (sum nat bool) (s:
          sumElim 0 nat bool (lam "_" (sum nat bool) (_: nat))
            onLeft onRight s);
      in Q.nf [] (elab macroAtS) == Q.nf [] (elab adapterAtS);
      expected = true;
    };

    # ===== TreeDT tests (datatypeP; one parameter; non-linear recursion) =====

    # TreeDT is a non-prelude user-defined datatype with two
    # constructors: `leaf` carries one data field, `node` carries two
    # recursive fields. `node`'s shape `descRec (descRec descRet)`
    # falls outside linearProfile's acceptance (no terminal data
    # spine), so the chain-flattener declines and the regular ann-lam
    # cascade handles every application. The eliminator's dispatchStep
    # projects two recursive IHs at positions 0 and 1 of payloadIH
    # (one per rec field, in declaration order).
    "datatype-tree-spec-name" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in Tree.name;
      expected = "Tree";
    };
    "datatype-tree-spec-params" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in builtins.length Tree.params;
      expected = 1;
    };
    "datatype-tree-spec-cons" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in builtins.length Tree._dtypeMeta.cons;
      expected = 2;
    };
    # Polymorphic T at A=nat elaborates as an app tree (ann-wrapped λA.
    # ... awaiting β); eval reduces to VMu.
    "datatype-tree-T-at-nat-elab" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (elab (app Tree.T nat)).tag;
      expected = "app";
    };
    # `Tree.leaf nat zero` type-checks against `Tree.T nat`.
    "datatype-tree-leaf-checks" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        result = checkHoas (app Tree.T nat) leafZero;
      in !(result ? error);
      expected = true;
    };
    # `Tree.node nat (leaf 0) (leaf 0)` type-checks against `Tree.T nat`.
    # Exercises the two-rec-fields fallback path: the chain-flatten
    # precondition rejects (chainShapeOk requires the last field to be
    # `rec` and all earlier fields to be `data`), so the application
    # elaborates through the regular ann-lam cascade. The kernel's
    # desc-con peel then sees a `descRec (descRec descRet)` description,
    # linearProfile returns null, and the peel declines without
    # mis-reading the payload.
    "datatype-tree-node-of-leaves-checks" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        result = checkHoas (app Tree.T nat) nodeLL;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic leaf at A=nat infers to a Π over `value : nat`.
    "datatype-tree-leaf-at-nat-infers-pi" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (inferHoas (app Tree.leaf nat)).type.tag;
      expected = "VPi";
    };
    # Polymorphic elim at A=nat infers to a Π (over the motive P).
    "datatype-tree-elim-at-nat-infers-pi" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
      in (inferHoas (app (Tree.elim 0) nat)).type.tag;
      expected = "VPi";
    };
    # End-to-end semantic test: count leaves of a 2-leaf tree.
    # leafCount = elim with motive (λ_. nat),
    #   step_leaf  = λ_. succ zero
    #   step_node  = λl r il ir. add il ir
    # `node (leaf 0) (leaf 0)` reduces via descInd to `add 1 1 = 2`.
    # The equality `leafCount tree ≡ succ (succ zero)` holds by
    # reduction; refl type-checks against it.
    "datatype-tree-elim-leaf-count-2" = {
      expr = let
        Tree = datatypeP "Tree" [{ name = "A"; kind = u 0; }] (ps:
          let A = builtins.elemAt ps 0; in [
            (con "leaf" [ (field "value" A) ])
            (con "node" [ (recField "left") (recField "right") ])
          ]);
        Tnat = app Tree.T nat;
        leafZero = app (app Tree.leaf nat) zero;
        nodeLL = app (app (app Tree.node nat) leafZero) leafZero;
        addTm = lam "m" nat (m: lam "n" nat (n:
                  ind 0 (lam "_" nat (_: nat))
                      n
                      (lam "k" nat (_: lam "ih" nat (ih: succ ih)))
                      m));
        M = lam "_" Tnat (_: nat);
        sLeaf = lam "v" nat (_: succ zero);
        sNode = lam "l" Tnat (_:
                lam "r" Tnat (_:
                lam "il" nat (il:
                lam "ir" nat (ir: app (app addTm il) ir))));
        countTm = app (app (app (app (app (Tree.elim 0) nat) M) sLeaf) sNode) nodeLL;
        two = succ (succ zero);
        eqTy = eq nat countTm two;
      in (checkHoas eqTy refl).tag;
      expected = "refl";
    };

    # ===== W-type tests (datatypeP; dependent parameter kinds) =====

    # W is parameterised by S (shapes : U) and P (positions : S → U).
    # The second parameter's KIND depends on the first — `P : S → U`
    # cannot be expressed with a fixed Hoas kind, so `datatypeP`
    # accepts `kind` as either a Hoas (fixed) OR a function
    # `markers → Hoas` (dependent on previously-bound parameter
    # markers). This mirrors the existing `field`/`fieldD` and
    # `piField`/`piFieldD` dependency pattern at the parameter level.
    #
    # The single ctor `sup` carries one data field (s : S) and one
    # dependent pi field (f : (P s) → W S P), exercising piFieldD's
    # `prev`-threaded type construction. chainShapeOk requires
    # last.kind == "recAt"; sup's last field is "piD", so the
    # chain-flattener declines and the regular ann-lam cascade handles
    # every application.
    "datatype-w-spec-name" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
      in W.name;
      expected = "W";
    };
    "datatype-w-spec-params" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
      in builtins.length W.params;
      expected = 2;
    };
    # W's macro D fully applied to (bool, λs.boolElim _ unit void s) is
    # nf-equivalent to the hand-written `descArg bool (s: descPi
    # (boolP s) descRet)` from the integration-desc-wtype-wellformed
    # test. Pins the D-emission shape against the canonical W-type
    # description.
    "datatype-w-D-matches-wDesc" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        macroD = app (app W.D bool) boolP;
        manualD = descArg 0 bool (s:
                    descPi 0 (app boolP s) descRet);
      in Q.nf [] (elab macroD) == Q.nf [] (elab manualD);
      expected = true;
    };
    # `W.T bool boolP` reduces to `μ wBoolDesc` and inhabits `U(0)`,
    # matching the `integration-desc-wtype-wellformed` shape test.
    "datatype-w-T-wellformed" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        Tw = app (app W.T bool) boolP;
        result = checkHoas (u 0) Tw;
      in !(result ? error);
      expected = true;
    };
    # Polymorphic `sup` partially applied to its two type parameters
    # infers to a Π over `s : bool` (the head of the curried field
    # signature). Validates that datatypeP's poly-ctor wrapper composes
    # the two `ann (λS λP. ...)` outer layers without losing
    # inferability.
    "datatype-w-sup-at-types-infers-pi" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim 1 (lam "_" bool (_: u 0)) unit void s);
      in (inferHoas (app (app W.sup bool) boolP)).type.tag;
      expected = "VPi";
    };
    # End-to-end ctor application: `sup false_ (λx:void. absurd Tw x)`
    # is a vacuous-position W value (P false_ = void, so f's domain is
    # empty and absurd discharges the body). Type-checks against `Tw =
    # W bool boolP`. Exercises piFieldD's dependent type-construction
    # and the absurd-on-void elimination through the macro's ctor type.
    "datatype-w-sup-vacuous-checks" = {
      expr = let
        W = datatypeP "W"
          [ { name = "S"; kind = u 0; }
            { name = "P"; kind = ms: forall "_" (builtins.elemAt ms 0) (_: u 0); } ]
          (ps: let S = builtins.elemAt ps 0; P = builtins.elemAt ps 1; in [
            (con "sup" [ (field "s" S) (piFieldD "f" (prev: app P prev.s)) ])
          ]);
        boolP = lam "s" bool (s:
                  boolElim 1 (lam "_" bool (_: u 0)) unit void s);
        Tw = app (app W.T bool) boolP;
        vacuous = lam "x" void (x: absurd Tw x);
        sup0 = app (app (app (app W.sup bool) boolP) false_) vacuous;
        result = checkHoas Tw sup0;
      in !(result ? error);
      expected = true;
    };

    # ===== datatypeI / datatypePI regressions =====
    # The macro's output should nf-equal the hand-written prelude
    # definitions for Fin (monomorphic indexed), Vec (parametric
    # indexed), and Eq (parametric indexed with parameter-dependent
    # index type). Comparison uses `Q.nf` on closed forms — for fields
    # that are Nix-level functions (constructors, elim), the test
    # closes them by wrapping in `lam` over fresh markers so both sides
    # sit under the same de Bruijn environment.

    "datatypeI-fin-D-matches-finDesc" = {
      expr = let
        FinDT = self.datatypeI "Fin" self.nat [
          (self.conI "fzero" [ (self.field "m" self.nat) ]
            (p: self.succ p.m))
          (self.conI "fsuc"  [ (self.field "m" self.nat)
                               (self.recFieldAt "k" (p: p.m)) ]
            (p: self.succ p.m))
        ];
      in Q.nf [] (elab FinDT.D) == Q.nf [] (elab self.finDesc);
      expected = true;
    };

    # `FinDT.T` is an `ann`-lam family-as-function: the macro's binder
    # is named `"i"` (abstract index position), the hand-written `self.fin`
    # names it `"n"`. `Q.nf` preserves lam binder names (quote.nix:25-27
    # propagates `VLam.name`), so a direct Tm-tree comparison diverges on
    # an α-equivalent choice. Applying both sides to a fresh marker
    # β-reduces the binder out of the nf — the semantics is compared by
    # application, matching the pattern used by `datatypePI-eq-T-matches-eqDT`.
    "datatypeI-fin-T-matches-fin" = {
      expr = let
        FinDT = self.datatypeI "Fin" self.nat [
          (self.conI "fzero" [ (self.field "m" self.nat) ]
            (p: self.succ p.m))
          (self.conI "fsuc"  [ (self.field "m" self.nat)
                               (self.recFieldAt "k" (p: p.m)) ]
            (p: self.succ p.m))
        ];
        macroForm = lam "n" self.nat (n: app FinDT.T n);
        handForm  = lam "n" self.nat (n: app self.fin n);
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    "datatypeI-fin-fzero-matches" = {
      expr = let
        FinDT = self.datatypeI "Fin" self.nat [
          (self.conI "fzero" [ (self.field "m" self.nat) ]
            (p: self.succ p.m))
          (self.conI "fsuc"  [ (self.field "m" self.nat)
                               (self.recFieldAt "k" (p: p.m)) ]
            (p: self.succ p.m))
        ];
        macroForm = lam "m" self.nat (m: app FinDT.fzero m);
        handForm  = lam "m" self.nat (m: self.fzero m);
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    "datatypeI-fin-fsuc-matches" = {
      expr = let
        FinDT = self.datatypeI "Fin" self.nat [
          (self.conI "fzero" [ (self.field "m" self.nat) ]
            (p: self.succ p.m))
          (self.conI "fsuc"  [ (self.field "m" self.nat)
                               (self.recFieldAt "k" (p: p.m)) ]
            (p: self.succ p.m))
        ];
        macroForm = lam "m" self.nat (m:
                    lam "k" (app self.fin m) (k:
                      app (app FinDT.fsuc m) k));
        handForm  = lam "m" self.nat (m:
                    lam "k" (app self.fin m) (k:
                      self.fsuc m k));
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    "datatypePI-vec-D-matches-vecDesc" = {
      expr = let
        VecDT = self.datatypePI "Vec"
          [ { name = "A"; kind = u 0; } ]
          (_: self.nat)
          (ps: let A = builtins.elemAt ps 0; in [
            (self.conI "vnil"  [] (_: self.zero))
            (self.conI "vcons"
              [ (self.field "m" self.nat)
                (self.field "x" A)
                (self.recFieldAt "xs" (p: p.m)) ]
              (p: self.succ p.m))
          ]);
        macroForm = lam "A" (u 0) (A: app VecDT.D A);
        handForm  = lam "A" (u 0) (A: self.vecDesc A);
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    # Same α-equivalence pattern as `datatypeI-fin-T-matches-fin`: apply
    # `VecDT.T A` and `self.vec A` to a fresh nat marker so the inner
    # index binder ("i" in the macro vs "n" in the hand-written) is
    # β-reduced out of the resulting nf.
    "datatypePI-vec-T-matches-vec" = {
      expr = let
        VecDT = self.datatypePI "Vec"
          [ { name = "A"; kind = u 0; } ]
          (_: self.nat)
          (ps: let A = builtins.elemAt ps 0; in [
            (self.conI "vnil"  [] (_: self.zero))
            (self.conI "vcons"
              [ (self.field "m" self.nat)
                (self.field "x" A)
                (self.recFieldAt "xs" (p: p.m)) ]
              (p: self.succ p.m))
          ]);
        macroForm = lam "A" (u 0) (A:
                    lam "n" self.nat (n: app (app VecDT.T A) n));
        handForm  = lam "A" (u 0) (A:
                    lam "n" self.nat (n: app (self.vec A) n));
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    "datatypePI-eq-D-matches-eqDesc" = {
      expr = let
        EqDT = self.datatypePI "Eq"
          [ { name = "A"; kind = u 0; }
            { name = "a"; kind = ms: builtins.elemAt ms 0; } ]
          (ps: builtins.elemAt ps 0)
          (ps: let a = builtins.elemAt ps 1; in [
            (self.conI "refl" [] (_: a))
          ]);
        macroForm = lam "A" (u 0) (A:
                    lam "a" A (a: app (app EqDT.D A) a));
        handForm  = lam "A" (u 0) (A:
                    lam "a" A (a: self.eqDesc A a));
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    "datatypePI-eq-T-matches-eqDT" = {
      expr = let
        EqDT = self.datatypePI "Eq"
          [ { name = "A"; kind = u 0; }
            { name = "a"; kind = ms: builtins.elemAt ms 0; } ]
          (ps: builtins.elemAt ps 0)
          (ps: let a = builtins.elemAt ps 1; in [
            (self.conI "refl" [] (_: a))
          ]);
        macroForm = lam "A" (u 0) (A:
                    lam "a" A (a:
                    lam "b" A (b:
                      app (app (app EqDT.T A) a) b)));
        handForm  = lam "A" (u 0) (A:
                    lam "a" A (a:
                    lam "b" A (b: self.eqDT A a b)));
      in Q.nf [] (elab macroForm) == Q.nf [] (elab handForm);
      expected = true;
    };

    # ===== Fin prelude =====
    # `Fin : Nat → U` is indexed over Nat. Two constructors: `fzero m : Fin (succ m)`
    # and `fsuc m k : Fin (succ m)` with `k : Fin m`. `Fin 0` is vacuous — the
    # ret-leaf obligation `Eq Nat (succ m) 0` is uninhabited — and `absurdFin0`
    # discharges the empty-case via no-confusion on Nat.

    "fin-as-type-checks" = {
      # fin : Nat → U. Applied to a concrete Nat, we get a type at U(0).
      expr = let
        ty = app fin (succ (succ zero));
      in (checkHoas (u 0) ty).tag;
      expected = "app";
    };

    "fin0-as-type-checks" = {
      # Fin 0 is a valid type (just uninhabited).
      expr = (checkHoas (u 0) (app fin zero)).tag;
      expected = "app";
    };

    "fzero-at-fin1-checks" = {
      # fzero zero : Fin (succ zero) = Fin 1.
      expr = (checkHoas (app fin (succ zero)) (fzero zero)).tag;
      expected = "desc-con";
    };

    "fzero-at-fin2-checks" = {
      # fzero (succ zero) : Fin 2.
      expr = (checkHoas (app fin (succ (succ zero))) (fzero (succ zero))).tag;
      expected = "desc-con";
    };

    "fsuc-at-fin2-checks" = {
      # fsuc 1 (fzero 0) : Fin 2.
      expr = let
        two = succ (succ zero);
        oneN = succ zero;
      in (checkHoas (app fin two) (fsuc oneN (fzero zero))).tag;
      expected = "desc-con";
    };

    # β-reduction on `finElim P Pz Ps 2 (fzero 1)` — collapses to `Pz 1`.
    # Motive is constant: P n k = nat. Pz m = zero. Ps m k ih = succ ih.
    # Expected NF: `zero` (which nf's to `descCon natDesc tt (pair true_ refl)`).
    "finElim-beta-on-fzero" = {
      expr = let
        two = succ (succ zero);
        oneN = succ zero;
        P    = lam "n" nat (n: lam "_k" (app fin n) (_: nat));
        Pz   = lam "m" nat (_: zero);
        Ps   = lam "m" nat (m: lam "_k" (app fin m) (_: lam "ih" nat (ih: succ ih)));
        elimmed = finElim 0 P Pz Ps two (fzero oneN);
      in Q.nf [] (elab elimmed) == Q.nf [] (elab zero);
      expected = true;
    };

    # β-reduction on `finElim P Pz Ps 2 (fsuc 1 (fzero 0))`:
    #   → Ps 1 (fzero 0) (finElim P Pz Ps 1 (fzero 0))
    #   → Ps 1 (fzero 0) (Pz 0)
    #   → Ps 1 (fzero 0) zero
    #   → succ zero.
    "finElim-beta-on-fsuc" = {
      expr = let
        two = succ (succ zero);
        oneN = succ zero;
        P    = lam "n" nat (n: lam "_k" (app fin n) (_: nat));
        Pz   = lam "m" nat (_: zero);
        Ps   = lam "m" nat (m: lam "_k" (app fin m) (_: lam "ih" nat (ih: succ ih)));
        elimmed = finElim 0 P Pz Ps two (fsuc oneN (fzero zero));
      in Q.nf [] (elab elimmed) == Q.nf [] (elab (succ zero));
      expected = true;
    };

    # `absurdFin0` type-checks at any target type, when applied to a Fin 0
    # inhabitant. Fin 0 has no canonical inhabitant; we supply a neutral via
    # a lam-binder so checkHoas can type-check the elimination.
    "absurdFin0-checks-at-constant-target" = {
      expr = let
        tm = lam "x" (app fin zero) (x: absurdFin0 nat x);
      in (checkHoas (forall "_" (app fin zero) (_: nat)) tm).tag;
      expected = "lam";
    };

    # ===== Vec prelude =====
    # `Vec A : Nat → U` is the indexed list family. Two constructors:
    # `vnil A : Vec A 0` (ret-leaf witness at zero) and
    # `vcons A m x xs : Vec A (succ m)` with `x : A`, `xs : Vec A m`.
    # `vhead A n (vcons A n x xs) ≡ x` — vnil case is unreachable via the
    # `natCaseU unit A` motive (unit at n=0, A at n=succ _).

    "vec-as-type-checks" = {
      # vec nat 2 : U(0).
      expr = (checkHoas (u 0) (app (vec nat) (succ (succ zero)))).tag;
      expected = "app";
    };

    "vec0-as-type-checks" = {
      # vec nat 0 is a valid type (with vnil as sole inhabitant).
      expr = (checkHoas (u 0) (app (vec nat) zero)).tag;
      expected = "app";
    };

    "vnil-at-vec0-checks" = {
      # vnil nat : vec nat 0.
      expr = (checkHoas (app (vec nat) zero) (vnil nat)).tag;
      expected = "desc-con";
    };

    "vcons-at-vec1-checks" = {
      # vcons nat 0 zero (vnil nat) : vec nat 1.
      expr = let
        oneN = succ zero;
      in (checkHoas (app (vec nat) oneN) (vcons nat zero zero (vnil nat))).tag;
      expected = "desc-con";
    };

    # β-reduction on `vecElim P Pn Pc 0 (vnil A)` — collapses to `Pn`.
    # Motive P n xs = nat (constant). Pn = zero. Pc m x xs ih = succ ih.
    # Expected nf: zero.
    "vecElim-beta-on-vnil" = {
      expr = let
        P   = lam "n" nat (n: lam "_xs" (app (vec nat) n) (_: nat));
        Pn  = zero;
        Pc  = lam "m" nat (_m: lam "_x" nat (_: lam "_xs" (app (vec nat) _m) (_:
                lam "ih" nat (ih: succ ih))));
        elimmed = vecElim 0 nat P Pn Pc zero (vnil nat);
      in Q.nf [] (elab elimmed) == Q.nf [] (elab zero);
      expected = true;
    };

    # β-reduction on `vecElim P Pn Pc 1 (vcons A 0 zero (vnil A))`:
    #   → Pc 0 zero (vnil A) (vecElim P Pn Pc 0 (vnil A))
    #   → Pc 0 zero (vnil A) Pn
    #   → succ Pn = succ zero.
    "vecElim-beta-on-vcons" = {
      expr = let
        oneN = succ zero;
        P   = lam "n" nat (n: lam "_xs" (app (vec nat) n) (_: nat));
        Pn  = zero;
        Pc  = lam "m" nat (_m: lam "_x" nat (_: lam "_xs" (app (vec nat) _m) (_:
                lam "ih" nat (ih: succ ih))));
        vs  = vcons nat zero zero (vnil nat);
        elimmed = vecElim 0 nat P Pn Pc oneN vs;
      in Q.nf [] (elab elimmed) == Q.nf [] (elab (succ zero));
      expected = true;
    };

    # `vhead A n (vcons A n x xs) ≡ x`.
    # At A = nat, n = 0, x = zero, xs = vnil nat:
    #   vhead nat 0 (vcons nat 0 zero (vnil nat)) ≡ zero.
    "vhead-beta-on-vcons" = {
      expr = let
        vs = vcons nat zero zero (vnil nat);
        hd = app (app (vhead nat) zero) vs;
      in Q.nf [] (elab hd) == Q.nf [] (elab zero);
      expected = true;
    };

    # `vtail A n (vcons A n x xs) ≡ xs`.
    # At A = nat, n = 0, x = zero, xs = vnil nat:
    #   vtail nat 0 (vcons nat 0 zero (vnil nat)) ≡ vnil nat.
    "vtail-beta-on-vcons" = {
      expr = let
        vs = vcons nat zero zero (vnil nat);
        tl = app (app (vtail nat) zero) vs;
      in Q.nf [] (elab tl) == Q.nf [] (elab (vnil nat));
      expected = true;
    };

    # ===== Eq-as-description =====
    # `eqDT A a b = μ A (retI a) b` expresses propositional equality
    # as a single-constructor indexed inductive family; `reflDT` is
    # the canonical witness at the diagonal. `eqToEqDT` / `eqDTToEq`
    # form an iso with the primitive Eq, and `eqIsoFwd` / `eqIsoBwd`
    # prove the iso identity as HOAS terms.

    "eqDesc-at-nat-zero-checks" = {
      # eqDesc nat zero : Desc nat. The forwarder emits an app spine
      # over `EqDT.D`; under nf both layers β-reduce to the macro's
      # description body, which for the single-ctor refl spine is
      # exactly `retI zero`.
      expr = Q.nf [] (elab (eqDesc nat zero))
          == Q.nf [] (elab (retI zero));
      expected = true;
    };

    "eqDT-at-refl-checks" = {
      # eqDT nat zero zero : U(0). Forwarder's app spine β-reduces
      # under nf to the bare `muI nat (retI zero) zero` the hand-written
      # spelling produced directly.
      expr = Q.nf [] (elab (eqDT nat zero zero))
          == Q.nf [] (elab (muI nat (retI zero) zero));
      expected = true;
    };

    "reflDT-at-zero-checks" = {
      # reflDT nat zero : eqDT nat zero zero.
      expr = (checkHoas (eqDT nat zero zero) (reflDT nat zero)).tag;
      expected = "desc-con";
    };

    "eqToEqDT-at-refl-checks" = {
      # eqToEqDT nat 0 0 refl : eqDT nat 0 0.
      expr = (checkHoas (eqDT nat zero zero)
                        (eqToEqDT nat zero zero refl)).tag;
      expected = "j";
    };

    "eqDTToEq-at-reflDT-checks" = {
      # eqDTToEq nat 0 0 (reflDT nat 0) : eq nat 0 0.
      expr = (checkHoas (eq nat zero zero)
                        (eqDTToEq nat zero zero (reflDT nat zero))).tag;
      expected = "desc-ind";
    };

    # nf-roundtrip at the refl case: `eqDTToEq (eqToEqDT refl) ≡ refl`.
    # J on refl fires to reflDT = descCon eD 0 refl; descInd on that
    # descCon fires to the payload `refl`.
    "eq-iso-fwd-at-refl-nf" = {
      expr = let
        t = eqDTToEq nat zero zero (eqToEqDT nat zero zero refl);
      in Q.nf [] (elab t) == Q.nf [] (elab refl);
      expected = true;
    };

    # nf-roundtrip at the reflDT case: `eqToEqDT (eqDTToEq reflDT) ≡ reflDT`.
    # descInd on descCon fires to payload `refl`; J on refl fires to reflDT.
    "eq-iso-bwd-at-reflDT-nf" = {
      expr = let
        t = eqToEqDT nat zero zero (eqDTToEq nat zero zero (reflDT nat zero));
      in Q.nf [] (elab t) == Q.nf [] (elab (reflDT nat zero));
      expected = true;
    };

    # Iso proofs type-check at their claimed propositions. These are
    # the `to ∘ from ≡ id` / `from ∘ to ≡ id` acceptance witnesses.
    "eq-iso-fwd-checks" = {
      # eqIsoFwd nat 0 0 : Π(e : eq nat 0 0). eq (eq nat 0 0) (...) e.
      expr = let
        ty = forall "e" (eq nat zero zero) (e:
               eq (eq nat zero zero)
                  (eqDTToEq nat zero zero (eqToEqDT nat zero zero e))
                  e);
      in (checkHoas ty (eqIsoFwd nat zero zero)).tag;
      expected = "lam";
    };

    "eq-iso-bwd-checks" = {
      # eqIsoBwd nat 0 0 : Π(x : eqDT nat 0 0). eq (eqDT nat 0 0) (...) x.
      expr = let
        ty = forall "x" (eqDT nat zero zero) (x:
               eq (eqDT nat zero zero)
                  (eqToEqDT nat zero zero (eqDTToEq nat zero zero x))
                  x);
      in (checkHoas ty (eqIsoBwd nat zero zero)).tag;
      expected = "lam";
    };
  };
}
