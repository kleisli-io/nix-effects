# HOAS aliases and proof-building helpers for the category theory library.
#
# Provides short names for kernel combinators and reusable proof tactics
# (congSucc, symProof, transProof, congAddRight) that expand to J applications.
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
  Sig = H.sigma;
  lam = H.lam;
  app = H.app;
  pair = H.pair;
  ind = H.ind;

  # addHoas : HOAS Nat → HOAS Nat → HOAS Nat
  # Addition as a NatElim tree: add(0,n)≡n, add(S(m),n)≡S(add(m,n)).
  # Used both as verified implementation and inside proof types.
  addHoas = m: n:
    ind (lam "_" Nat (_: Nat)) n
      (lam "_" Nat (_: lam "ih" Nat (ih: H.succ ih)))
      m;

  # congSucc(a, b, p) : Eq(Nat,a,b) → Eq(Nat, S(a), S(b))
  congSucc = a: b: p:
    J Nat a
      (lam "y" Nat (y: lam "_" (Eq Nat a y) (_:
        Eq Nat (H.succ a) (H.succ y))))
      Refl b p;

  # symProof(A, a, b, p) : Eq(A,a,b) → Eq(A,b,a)
  symProof = A: a: b: p:
    J A a
      (lam "y" A (y: lam "_" (Eq A a y) (_: Eq A y a)))
      Refl b p;

  # transProof(A, a, b, c, p, q) : Eq(A,a,b) → Eq(A,b,c) → Eq(A,a,c)
  transProof = A: a: b: c: p: q:
    J A b
      (lam "y" A (y: lam "_" (Eq A b y) (_: Eq A a y)))
      p c q;

  # congAddRight(a, b, b', p) : Eq(Nat,b,b') → Eq(Nat, add(a,b), add(a,b'))
  congAddRight = a: b: b': p:
    J Nat b
      (lam "y" Nat (y: lam "_" (Eq Nat b y) (_:
        Eq Nat (addHoas a b) (addHoas a y))))
      Refl b' p;

in {
  inherit H verify;
  inherit Nat U0 Unit Eq Refl J Pi Sig lam app pair ind;
  inherit addHoas congSucc symProof transProof congAddRight;
}
