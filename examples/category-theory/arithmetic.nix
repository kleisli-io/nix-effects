# Addition on Nat with its seven fundamental verified properties.
#
# Two of the lemmas are free by computation — the definition of `add`
# reduces the left-hand side to the right-hand side, so `refl` suffices.
# The remaining five theorems come from induction on a Nat argument; the
# step case invariably uses `congSucc` (from prelude) to push the
# induction hypothesis through a `succ`. `addComm` combines everything:
# it is proved by induction on `m`, with `addRightZero` as the base case
# witness and `addRightSucc` as the step-case rewrite.
#
# Later files (`algebra.nix`, `functor.nix`) consume the `ann*` forms
# of these lemmas — the HOAS term annotated with its type — so that
# proofs built on top of them stay inferable wherever they appear
# inside a larger term.
#
# Lemmas (free by computation):
#   addLeftZero  : ∀n. add(0, n) = n
#   addSucc      : ∀m n. add(S(m), n) = S(add(m, n))
#
# Theorems (by induction):
#   addRightZero : ∀n. add(n, 0) = n
#   addAssoc     : ∀x y z. add(add(x,y), z) = add(x, add(y,z))
#   addRightSucc : ∀m n. add(m, S(n)) = S(add(m, n))
#   addComm      : ∀m n. add(m, n) = add(n, m)
{ prelude }:

let
  inherit (prelude) H verify Nat Eq Refl Pi lam app ind
    addHoas congSucc symProof transProof;

in
rec {

  # -- Addition --

  addTy = Pi "m" Nat (_: Pi "n" Nat (_: Nat));
  addImpl = lam "m" Nat (m: lam "n" Nat (n: addHoas m n));
  add = verify addTy addImpl;

  # -- Computational lemmas (base/step of NatElim reduce, so refl suffices) --

  addLeftZeroTy = Pi "n" Nat (n: Eq Nat (addHoas H.zero n) n);
  addLeftZeroImpl = lam "n" Nat (_: Refl);
  addLeftZero = verify addLeftZeroTy addLeftZeroImpl;
  annAddLeftZero = H.ann addLeftZeroImpl addLeftZeroTy;

  addSuccTy = Pi "m" Nat (m: Pi "n" Nat (n:
    Eq Nat (addHoas (H.succ m) n) (H.succ (addHoas m n))));
  addSuccImpl = lam "m" Nat (_: lam "n" Nat (_: Refl));
  addSucc = verify addSuccTy addSuccImpl;
  annAddSucc = H.ann addSuccImpl addSuccTy;

  # -- addRightZero: by induction, step uses cong succ --

  addRightZeroTy = Pi "n" Nat (n: Eq Nat (addHoas n H.zero) n);

  addRightZeroImpl = lam "n" Nat (n:
    ind 0
      (lam "k" Nat (k: Eq Nat (addHoas k H.zero) k))
      (H.ann Refl (Eq Nat (addHoas H.zero H.zero) H.zero))
      (lam "k" Nat (k: lam "ih" (Eq Nat (addHoas k H.zero) k) (ih:
        congSucc (addHoas k H.zero) k ih)))
      n);

  addRightZero = verify addRightZeroTy addRightZeroImpl;
  annAddRightZero = H.ann addRightZeroImpl addRightZeroTy;

  # -- addAssoc: by induction on x, step uses cong succ --

  addAssocTy = Pi "x" Nat (x: Pi "y" Nat (y: Pi "z" Nat (z:
    Eq Nat (addHoas (addHoas x y) z) (addHoas x (addHoas y z)))));

  addAssocImpl = lam "x" Nat (x: lam "y" Nat (y: lam "z" Nat (z:
    ind 0
      (lam "k" Nat (k:
        Eq Nat (addHoas (addHoas k y) z) (addHoas k (addHoas y z))))
      (H.ann Refl
        (Eq Nat (addHoas (addHoas H.zero y) z)
          (addHoas H.zero (addHoas y z))))
      (lam "k" Nat (k:
        lam "ih" (Eq Nat (addHoas (addHoas k y) z) (addHoas k (addHoas y z))) (ih:
          congSucc (addHoas (addHoas k y) z) (addHoas k (addHoas y z)) ih)))
      x)));

  addAssoc = verify addAssocTy addAssocImpl;
  annAddAssoc = H.ann addAssocImpl addAssocTy;

  # -- addRightSucc: by induction on m, step uses cong succ --

  addRightSuccTy = Pi "m" Nat (m: Pi "n" Nat (n:
    Eq Nat (addHoas m (H.succ n)) (H.succ (addHoas m n))));

  addRightSuccImpl = lam "m" Nat (m: lam "n" Nat (n:
    ind 0
      (lam "k" Nat (k: Eq Nat (addHoas k (H.succ n)) (H.succ (addHoas k n))))
      (H.ann Refl
        (Eq Nat (addHoas H.zero (H.succ n)) (H.succ (addHoas H.zero n))))
      (lam "k" Nat (k: lam "ih" (Eq Nat (addHoas k (H.succ n)) (H.succ (addHoas k n))) (ih:
        congSucc (addHoas k (H.succ n)) (H.succ (addHoas k n)) ih)))
      m));

  addRightSucc = verify addRightSuccTy addRightSuccImpl;
  annAddRightSucc = H.ann addRightSuccImpl addRightSuccTy;

  # -- addComm: by induction on m --
  #   Base: sym(addRightZero(n))
  #   Step: trans(congSucc(ih), sym(addRightSucc(n,k)))

  addCommTy = Pi "m" Nat (m: Pi "n" Nat (n:
    Eq Nat (addHoas m n) (addHoas n m)));

  addCommImpl = lam "m" Nat (m: lam "n" Nat (n:
    ind 0
      (lam "k" Nat (k: Eq Nat (addHoas k n) (addHoas n k)))
      (symProof Nat (addHoas n H.zero) n (app annAddRightZero n))
      (lam "k" Nat (k:
        lam "ih" (Eq Nat (addHoas k n) (addHoas n k)) (ih:
          transProof Nat
            (H.succ (addHoas k n))
            (H.succ (addHoas n k))
            (addHoas n (H.succ k))
            (congSucc (addHoas k n) (addHoas n k) ih)
            (symProof Nat (addHoas n (H.succ k)) (H.succ (addHoas n k))
              (app (app annAddRightSucc n) k)))))
      m));

  addComm = verify addCommTy addCommImpl;
  annAddComm = H.ann addCommImpl addCommTy;
}
