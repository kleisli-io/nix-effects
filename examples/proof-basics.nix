# Proof Basics: computational proofs with the nix-effects kernel
#
# What you can PROVE with pure Nix — not contracts or effects, but actual
# dependent-type proofs checked at Nix eval time.
#
# The kernel normalizes both sides of an equality and compares them.
# If they reduce to the same normal form, Refl proves the equality.
# This file demonstrates eight proof techniques, from simple arithmetic
# through eliminators, dependent witnesses, and type-level constructs.
#
# Each test name describes the theorem. checkHoas type-checks a term
# against a type; if the result has tag "refl", "pair", or "lam",
# the proof was accepted.
#
#   nix build .#checks.proof-basics   — verify all proofs
{ fx, ... }:

let
  H = fx.types.hoas;
  inherit (H) nat bool void listOf sum eq u
              forall sigma
              lam zero succ true_ false_ nil cons pair inl inr refl
              natLit absurd
              ind boolElim listElim sumElim
              checkHoas;

  # ----- Recursive functions defined via eliminators -----

  # add(m, n) = NatElim(λ_.Nat, n, λk.λih.S(ih), m)
  # Recurses on first argument: add(0,n) = n, add(S(k),n) = S(add(k,n))
  add = m: n:
    ind (lam "_" nat (_: nat)) n
      (lam "k" nat (_: lam "ih" nat (ih: succ ih))) m;

  # not(b) = BoolElim(λ_.Bool, false, true, b)
  not_ = b:
    boolElim (lam "_" bool (_: bool)) false_ true_ b;

  # length(xs) = ListElim(Nat, λ_.Nat, 0, λh.λt.λih.S(ih), xs)
  length = xs:
    listElim nat (lam "_" (listOf nat) (_: nat)) zero
      (lam "h" nat (_: lam "t" (listOf nat) (_:
        lam "ih" nat (ih: succ ih)))) xs;

  # append(xs, ys) = ListElim(Nat, λ_.List Nat, ys, λh.λt.λih.h::ih, xs)
  append = xs: ys:
    listElim nat (lam "_" (listOf nat) (_: listOf nat)) ys
      (lam "h" nat (h: lam "t" (listOf nat) (_:
        lam "ih" (listOf nat) (ih: cons nat h ih)))) xs;

  # ----- Concrete data -----

  list123 = cons nat (natLit 1) (cons nat (natLit 2) (cons nat (natLit 3) (nil nat)));
  list12  = cons nat (natLit 1) (cons nat (natLit 2) (nil nat));
  list3   = cons nat (natLit 3) (nil nat);
  list012 = cons nat zero (cons nat (natLit 1) (cons nat (natLit 2) (nil nat)));

in rec {

  # ===== 1. Computational Equality =====
  #
  # The simplest proofs: both sides normalize to the same value,
  # so Refl (reflexivity) witnesses the equality.

  # 0 + 0 = 0
  addZeroZero =
    (checkHoas (eq nat (add zero zero) zero) refl).tag == "refl";

  # 3 + 5 = 8
  addThreeFive =
    (checkHoas (eq nat (add (natLit 3) (natLit 5)) (natLit 8)) refl).tag == "refl";

  # 10 + 7 = 17
  addTenSeven =
    (checkHoas (eq nat (add (natLit 10) (natLit 7)) (natLit 17)) refl).tag == "refl";

  # not(not(true)) = true
  doubleNegTrue =
    (checkHoas (eq bool (not_ (not_ true_)) true_) refl).tag == "refl";

  # not(not(false)) = false
  doubleNegFalse =
    (checkHoas (eq bool (not_ (not_ false_)) false_) refl).tag == "refl";

  # length([1,2,3]) = 3
  lengthThree =
    (checkHoas (eq nat (length list123) (natLit 3)) refl).tag == "refl";

  # append([1,2], [3]) = [1,2,3]
  appendTwoOne =
    (checkHoas (eq (listOf nat) (append list12 list3) list123) refl).tag == "refl";


  # ===== 2. Dependent Witnesses =====
  #
  # Σ(x:A).P(x) packs a value with evidence of a property.
  # "There exists an x such that P(x)" — and here's the x.

  # (0, Refl) : Σ(x:Nat). x = 0
  witnessZero =
    let
      ty = sigma "x" nat (x: eq nat x zero);
      tm = pair zero refl ty;
    in (checkHoas ty tm).tag == "pair";

  # (8, Refl) : Σ(x:Nat). 3+5 = x
  witnessAddResult =
    let
      ty = sigma "x" nat (x: eq nat (add (natLit 3) (natLit 5)) x);
      tm = pair (natLit 8) refl ty;
    in (checkHoas ty tm).tag == "pair";

  # (true, Refl) : Σ(b:Bool). not(not(b)) = b
  witnessDoubleNeg =
    let
      ty = sigma "b" bool (b: eq bool (not_ (not_ b)) b);
      tm = pair true_ refl ty;
    in (checkHoas ty tm).tag == "pair";


  # ===== 3. NatElim — Recursion on Naturals =====
  #
  # NatElim(motive, base, step, n):
  #   base  : motive(0)
  #   step  : Π(k:Nat). motive(k) → motive(S(k))

  # double(4) = 8 — double(0)=0, double(S(k))=S(S(double(k)))
  natElimDouble =
    let
      double = n: ind (lam "_" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: succ (succ ih)))) n;
    in (checkHoas (eq nat (double (natLit 4)) (natLit 8)) refl).tag == "refl";

  # mul(3,4) = 12 — mul(0,n)=0, mul(S(k),n)=add(n,mul(k,n))
  natElimMul =
    let
      mul = m: n: ind (lam "_" nat (_: nat)) zero
        (lam "k" nat (_: lam "ih" nat (ih: add n ih))) m;
    in (checkHoas (eq nat (mul (natLit 3) (natLit 4)) (natLit 12)) refl).tag == "refl";


  # ===== 4. BoolElim — Case Analysis on Booleans =====

  # if true then 42 else 0 = 42
  boolElimTrue =
    let
      result = boolElim (lam "_" bool (_: nat)) (natLit 42) zero true_;
    in (checkHoas (eq nat result (natLit 42)) refl).tag == "refl";

  # if false then 42 else 0 = 0
  boolElimFalse =
    let
      result = boolElim (lam "_" bool (_: nat)) (natLit 42) zero false_;
    in (checkHoas (eq nat result zero) refl).tag == "refl";


  # ===== 5. ListElim — Structural Recursion on Lists =====
  #
  # ListElim(elem, motive, onNil, onCons, scrut):
  #   onNil  : motive([])
  #   onCons : Π(h:elem). Π(t:List elem). motive(t) → motive(h::t)

  # sum([1,2,3]) = 6
  listSum =
    let
      sumList = xs: listElim nat (lam "_" (listOf nat) (_: nat)) zero
        (lam "h" nat (h: lam "t" (listOf nat) (_:
          lam "ih" nat (ih: add h ih)))) xs;
    in (checkHoas (eq nat (sumList list123) (natLit 6)) refl).tag == "refl";

  # map succ [0,1,2] = [1,2,3]
  listMapSucc =
    let
      mapSucc = xs: listElim nat (lam "_" (listOf nat) (_: listOf nat))
        (nil nat)
        (lam "h" nat (h: lam "t" (listOf nat) (_:
          lam "ih" (listOf nat) (ih: cons nat (succ h) ih)))) xs;
    in (checkHoas (eq (listOf nat) (mapSucc list012) list123) refl).tag == "refl";


  # ===== 6. SumElim — Case Analysis on Coproducts =====
  #
  # Sum(A,B) = Left(a) | Right(b)
  # SumElim(L, R, motive, onLeft, onRight, scrut)

  # case Left(5) of { Left n → n; Right _ → 0 } = 5
  sumElimLeft =
    let
      scrut = inl nat bool (natLit 5);
      result = sumElim nat bool (lam "_" (sum nat bool) (_: nat))
        (lam "n" nat (n: n))
        (lam "b" bool (_: zero))
        scrut;
    in (checkHoas (eq nat result (natLit 5)) refl).tag == "refl";

  # case Right(true) of { Left n → n; Right b → if b then 1 else 0 } = 1
  sumElimRight =
    let
      scrut = inr nat bool true_;
      result = sumElim nat bool (lam "_" (sum nat bool) (_: nat))
        (lam "n" nat (n: n))
        (lam "b" bool (b: boolElim (lam "_" bool (_: nat)) (natLit 1) zero b))
        scrut;
    in (checkHoas (eq nat result (natLit 1)) refl).tag == "refl";


  # ===== 7. Polymorphic Identity =====
  #
  # λ(A:U₀). λ(x:A). x  :  Π(A:U₀). A → A
  # The simplest universe-polymorphic term.

  polyId =
    let
      ty = forall "A" (u 0) (a: forall "x" a (_: a));
      tm = lam "A" (u 0) (a: lam "x" a (x: x));
    in (checkHoas ty tm).tag == "lam";


  # ===== 8. Ex Falso =====
  #
  # From Void (the empty type), derive anything.
  # absurd : Void → A eliminates a Void witness.
  # We can type-check the function but never apply it — Void has no values.

  exFalso =
    let
      ty = forall "A" (u 0) (a: forall "x" void (_: a));
      tm = lam "A" (u 0) (a: lam "x" void (x: absurd a x));
    in (checkHoas ty tm).tag == "lam";


  # ===== All tests =====

  allPass =
    addZeroZero && addThreeFive && addTenSeven
    && doubleNegTrue && doubleNegFalse
    && lengthThree && appendTwoOne
    && witnessZero && witnessAddResult && witnessDoubleNeg
    && natElimDouble && natElimMul
    && boolElimTrue && boolElimFalse
    && listSum && listMapSucc
    && sumElimLeft && sumElimRight
    && polyId && exFalso;
}
