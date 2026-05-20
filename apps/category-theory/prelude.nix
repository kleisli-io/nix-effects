# Prelude: short names for kernel combinators plus reusable proof tactics.
#
# Every subsequent file in this library imports from here, so you can
# read any one of them without first learning the full HOAS surface.
#
# Re-exports from `fx.types.hoas`:
#   H, verify       — HOAS combinators and the verifier.
#   Nat, U0, Unit   — base types.
#   Eq, Refl, J     — propositional equality and its eliminator.
#   Pi, lam, app    — Π-type, λ-abstraction, application.
#   ind             — Nat eliminator.
#
# Proof tactics (each expands to a single J application):
#   addHoas         — addition defined by recursion on the first argument.
#   congSucc        — cong specialised to `succ`.
#   symProof        — J-based proof that equality is symmetric.
#   transProof      — J-based proof that equality is transitive.
#   congAddRight    — cong for `add a _` in the right argument.
{ fx }:

let
  H = fx.types.hoas;
  verify = fx.types.verifyAndExtract;

  Nat = H.nat;
  U0 = H.u 0;
  Unit = H.unit;
  Eq = H.eq;
  Refl = H.refl;
  J = H.j;
  Pi = H.forall;
  lam = H.lam;
  app = H.app;
  ind = H.ind;

  # addHoas m n : HOAS Nat.
  # Recursion on m:  add(0,n) ≡ n,  add(S(m),n) ≡ S(add(m,n)).
  # Used both as the verified implementation of `add` and inside proof
  # types, so the kernel sees one canonical definition throughout.
  addHoas = m: n:
    ind 0 (lam "_" Nat (_: Nat)) n
      (lam "_" Nat (_: lam "ih" Nat (ih: H.succ ih)))
      m;

  # congSucc(a, b, p) : Eq(Nat, a, b) → Eq(Nat, S(a), S(b))
  congSucc = a: b: p:
    J Nat a
      (lam "y" Nat (y: lam "_" (Eq Nat a y) (_:
        Eq Nat (H.succ a) (H.succ y))))
      Refl
      b
      p;

  # symProof(A, a, b, p) : Eq(A, a, b) → Eq(A, b, a)
  symProof = A: a: b: p:
    J A a
      (lam "y" A (y: lam "_" (Eq A a y) (_: Eq A y a)))
      Refl
      b
      p;

  # transProof(A, a, b, c, p, q) : Eq(A, a, b) → Eq(A, b, c) → Eq(A, a, c)
  transProof = A: a: b: c: p: q:
    J A b
      (lam "y" A (y: lam "_" (Eq A b y) (_: Eq A a y)))
      p
      c
      q;

  # congAddRight(a, b, b', p) : Eq(Nat, b, b') → Eq(Nat, add(a,b), add(a,b'))
  congAddRight = a: b: b': p:
    J Nat b
      (lam "y" Nat (y: lam "_" (Eq Nat b y) (_:
        Eq Nat (addHoas a b) (addHoas a y))))
      Refl
      b'
      p;

in
{
  inherit H verify;
  inherit Nat U0 Unit Eq Refl J Pi lam app ind;
  inherit addHoas congSucc symProof transProof congAddRight;
}
