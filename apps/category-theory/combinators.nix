# Proof combinators derived from J elimination.
#
#   sym   : Π(A:U). Π(a b : A). Eq(A,a,b) → Eq(A,b,a)
#   trans : Π(A:U). Π(a b c : A). Eq(A,a,b) → Eq(A,b,c) → Eq(A,a,c)
#   cong  : Π(A B : U). Π(f : A→B). Π(a b : A). Eq(A,a,b) → Eq(B,f(a),f(b))
#
# Each is a verified HOAS term: type-checked by the kernel, then extracted
# as a callable Nix function.
{ prelude }:

let
  inherit (prelude) verify H U0 Eq Refl J Pi lam app;

in rec {

  # sym(A, a, b, p) = J(A, a, λy.λ_.Eq(A,y,a), refl, b, p)
  symTy = Pi "A" U0 (A: Pi "a" A (a: Pi "b" A (b:
    Pi "_" (Eq A a b) (_: Eq A b a))));

  symImpl = lam "A" U0 (A: lam "a" A (a: lam "b" A (b:
    lam "p" (Eq A a b) (p:
      J A a
        (lam "y" A (y: lam "_" (Eq A a y) (_: Eq A y a)))
        Refl b p))));

  sym = verify symTy symImpl;

  # trans(A, a, b, c, p, q) = J(A, b, λy.λ_.Eq(A,a,y), p, c, q)
  transTy = Pi "A" U0 (A: Pi "a" A (a: Pi "b" A (b: Pi "c" A (c:
    Pi "_" (Eq A a b) (p: Pi "_" (Eq A b c) (_: Eq A a c))))));

  transImpl = lam "A" U0 (A: lam "a" A (a: lam "b" A (b: lam "c" A (c:
    lam "p" (Eq A a b) (p: lam "q" (Eq A b c) (q:
      J A b
        (lam "y" A (y: lam "_" (Eq A b y) (_: Eq A a y)))
        p c q))))));

  trans = verify transTy transImpl;

  # cong(A, B, f, a, b, p) = J(A, a, λy.λ_.Eq(B,f(a),f(y)), refl, b, p)
  congTy = Pi "A" U0 (A: Pi "B" U0 (B:
    Pi "f" (Pi "_" A (_: B)) (f: Pi "a" A (a: Pi "b" A (b:
      Pi "_" (Eq A a b) (_: Eq B (app f a) (app f b)))))));

  congImpl = lam "A" U0 (A: lam "B" U0 (B:
    lam "f" (Pi "_" A (_: B)) (f: lam "a" A (a: lam "b" A (b:
      lam "p" (Eq A a b) (p:
        J A a
          (lam "y" A (y: lam "_" (Eq A a y) (_: Eq B (app f a) (app f y))))
          Refl b p))))));

  cong = verify congTy congImpl;
}
