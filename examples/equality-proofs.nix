# Equality Proofs: J eliminator and derived combinators
#
# The J eliminator (identity elimination) is the fundamental proof tool
# for equalities in Martin-Löf type theory. From J, you derive the
# standard combinators: congruence, symmetry, transitivity, and transport.
#
# J(A, a, P, pr, b, eq):
#   A  : the type
#   a  : the left side (center of the elimination)
#   P  : λ(y:A). λ(_:Eq(A,a,y)). Type   — the motive
#   pr : P(a, refl)                     — base case
#   b  : the right side
#   eq : Eq(A, a, b)                    — proof of equality
#   Returns: P(b, eq)
#
# Computation rule: J(A, a, P, pr, b, refl) = pr
# When the equality proof is refl, J returns the base case directly.
#
# Each section defines a generic combinator (type-checked with abstract
# variables) and a concrete application (computed on specific values).
# With concrete data, equalities reduce by computation, so J always
# receives refl — the interesting part is that the GENERIC combinators
# type-check with abstract variables, proving the reasoning valid for
# all inputs.
#
#   nix build .#checks.equality-proofs   — verify all proofs
{ fx, ... }:

let
  H = fx.types.hoas;
  inherit (H) nat bool eq u
              forall
              lam zero succ true_ refl
              natLit app
              ind boolElim j
              checkHoas;

  # Helper: addition via NatElim
  add = m: n:
    ind (lam "_" nat (_: nat)) n
      (lam "k" nat (_: lam "ih" nat (ih: succ ih))) m;

in rec {

  # ===== 1. Congruence (cong) =====
  #
  # If x = y, then f(x) = f(y) for any f.
  # cong : Π(A:U₀). Π(B:U₀). Π(f:A→B). Π(x:A). Π(y:A). Eq(A,x,y) → Eq(B,f(x),f(y))
  #
  # Derivation: J(A, x, λy.λ_.Eq(B,f(x),f(y)), refl, y, p)
  # Base case (y=x): Eq(B, f(x), f(x)) — proved by refl

  congType =
    let
      ty = forall "A" (u 0) (a:
        forall "B" (u 0) (b:
          forall "f" (forall "_" a (_: b)) (f:
            forall "x" a (x:
              forall "y" a (y:
                forall "_" (eq a x y) (_:
                  eq b (app f x) (app f y)))))));
      tm = lam "A" (u 0) (a:
        lam "B" (u 0) (b:
          lam "f" (forall "_" a (_: b)) (f:
            lam "x" a (x:
              lam "y" a (y:
                lam "p" (eq a x y) (p:
                  j a x
                    (lam "y'" a (y': lam "_" (eq a x y') (_: eq b (app f x) (app f y'))))
                    refl y p))))));
    in (checkHoas ty tm).tag == "lam";

  # Concrete: from add(2,1) = 3, derive succ(add(2,1)) = succ(3)
  congConcrete =
    let
      add21 = add (natLit 2) (succ zero);
      three = natLit 3;
      proofTy = eq nat (succ add21) (succ three);
      proofTm = j nat add21
        (lam "y" nat (y: lam "_" (eq nat add21 y) (_: eq nat (succ add21) (succ y))))
        refl three refl;
    in (checkHoas proofTy proofTm).tag == "j";


  # ===== 2. Symmetry (sym) =====
  #
  # If x = y, then y = x.
  # sym : Π(A:U₀). Π(x:A). Π(y:A). Eq(A,x,y) → Eq(A,y,x)
  #
  # Derivation: J(A, x, λy.λ_.Eq(A,y,x), refl, y, p)
  # Base case (y=x): Eq(A, x, x) — proved by refl

  symType =
    let
      ty = forall "A" (u 0) (a:
        forall "x" a (x:
          forall "y" a (y:
            forall "_" (eq a x y) (_:
              eq a y x))));
      tm = lam "A" (u 0) (a:
        lam "x" a (x:
          lam "y" a (y:
            lam "p" (eq a x y) (p:
              j a x
                (lam "y'" a (y': lam "_" (eq a x y') (_: eq a y' x)))
                refl y p))));
    in (checkHoas ty tm).tag == "lam";

  # Concrete: Eq(Nat, add(0,3), 3) → Eq(Nat, 3, add(0,3))
  symConcrete =
    let
      three = natLit 3;
      add03 = add zero three;
      proofTy = eq nat three add03;
      proofTm = j nat add03
        (lam "y" nat (y: lam "_" (eq nat add03 y) (_: eq nat y add03)))
        refl three refl;
    in (checkHoas proofTy proofTm).tag == "j";


  # ===== 3. Transitivity (trans) =====
  #
  # If x = y and y = z, then x = z.
  # trans : Π(A:U₀). Π(x:A). Π(y:A). Π(z:A). Eq(A,x,y) → Eq(A,y,z) → Eq(A,x,z)
  #
  # Derivation: fix p, J on q:
  #   J(A, y, λz.λ_.Eq(A,x,z), p, z, q)
  # Base case (z=y): Eq(A, x, y) — proved by p

  transType =
    let
      ty = forall "A" (u 0) (a:
        forall "x" a (x:
          forall "y" a (y:
            forall "z" a (z:
              forall "_" (eq a x y) (_:
                forall "_" (eq a y z) (_:
                  eq a x z))))));
      tm = lam "A" (u 0) (a:
        lam "x" a (x:
          lam "y" a (y:
            lam "z" a (z:
              lam "p" (eq a x y) (p:
                lam "q" (eq a y z) (q:
                  j a y
                    (lam "z'" a (z': lam "_" (eq a y z') (_: eq a x z')))
                    p z q))))));
    in (checkHoas ty tm).tag == "lam";

  # Concrete: chain add(1,2) = 3 and 3 = add(0,3) to get add(1,2) = add(0,3)
  transConcrete =
    let
      three = natLit 3;
      add12 = add (succ zero) (natLit 2);
      add03 = add zero three;
      # p : Eq(Nat, add(1,2), 3) = refl, then J on q : Eq(Nat, 3, add(0,3)) = refl
      proofTy = eq nat add12 add03;
      proofTm = j nat three
        (lam "z" nat (z: lam "_" (eq nat three z) (_: eq nat add12 z)))
        refl add03 refl;
    in (checkHoas proofTy proofTm).tag == "j";


  # ===== 4. Transport =====
  #
  # If x = y and P(x) holds, then P(y) holds.
  # transport : Π(A:U₀). Π(P:A→U₀). Π(x:A). Π(y:A). Eq(A,x,y) → P(x) → P(y)
  #
  # Derivation: J(A, x, λy.λ_.P(y), px, y, p)
  # Base case (y=x): P(x) — proved by px

  transportType =
    let
      ty = forall "A" (u 0) (a:
        forall "P" (forall "_" a (_: u 0)) (bigP:
          forall "x" a (x:
            forall "y" a (y:
              forall "_" (eq a x y) (_:
                forall "_" (app bigP x) (_:
                  app bigP y))))));
      tm = lam "A" (u 0) (a:
        lam "P" (forall "_" a (_: u 0)) (bigP:
          lam "x" a (x:
            lam "y" a (y:
              lam "p" (eq a x y) (p:
                lam "px" (app bigP x) (px:
                  j a x
                    (lam "y'" a (y': lam "_" (eq a x y') (_: app bigP y')))
                    px y p))))));
    in (checkHoas ty tm).tag == "lam";

  # Concrete: P(b) = BoolElim(λ_.U₀, Nat, Bool, b) — dependent type family
  # true ↦ Nat, false ↦ Bool. Transport zero : P(true) along Eq(Bool, true, true).
  transportConcrete =
    let
      motiveP = b: boolElim (lam "_" bool (_: u 0)) nat bool b;
      proofTm = j bool true_
        (lam "y" bool (y: lam "_" (eq bool true_ y) (_: motiveP y)))
        zero  # zero : Nat = P(true)
        true_ refl;
    in (checkHoas nat proofTm).tag == "j";


  # ===== 5. Combined: cong + sym =====
  #
  # Chain two J applications: first lift an equality through succ (cong),
  # then reverse it (sym). The inner J result feeds as the equality proof
  # to the outer J.
  #
  # Step 1: Eq(Nat, add(2,1), 3) → Eq(Nat, S(add(2,1)), S(3))  [cong succ]
  # Step 2: Eq(Nat, S(add(2,1)), S(3)) → Eq(Nat, S(3), S(add(2,1)))  [sym]

  combinedProof =
    let
      add21 = add (natLit 2) (succ zero);
      three = natLit 3;
      sadd21 = succ add21;
      sthree = succ three;
      # Step 1: cong succ
      congStep = j nat add21
        (lam "y" nat (y: lam "_" (eq nat add21 y) (_: eq nat sadd21 (succ y))))
        refl three refl;
      # Step 2: sym on congStep
      proofTy = eq nat sthree sadd21;
      proofTm = j nat sadd21
        (lam "y" nat (y: lam "_" (eq nat sadd21 y) (_: eq nat y sadd21)))
        refl sthree congStep;
    in (checkHoas proofTy proofTm).tag == "j";


  # ===== All tests =====

  allPass =
    congType && congConcrete
    && symType && symConcrete
    && transType && transConcrete
    && transportType && transportConcrete
    && combinedProof;
}
