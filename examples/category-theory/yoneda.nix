# Yoneda's lemma as an equivalence of types.
#
# The library's previous chapters (`algebra.nix`, `functor.nix`) built a
# specific category and a specific functor on it. Yoneda's lemma is the
# general statement that sits behind the presheaf/representable-functor
# correspondence: for any point `a : A` and any type family `B : A → U`,
# the space of sections
#
#     Π(x:A). Eq(A, a, x) → B(x)
#
# is equivalent to the single fibre `B(a)`. Read through the types-as-
# groupoids lens: a "natural transformation" out of the representable
# presheaf `y(a)` is determined by its value on the universal element
# `(a, refl)`.
#
# The equivalence is witnessed by four verified terms:
#
#   yonedaEval : (Π(x:A). Eq(A,a,x) → B(x)) → B(a)          — evaluate at (a, refl)
#   yonedaLift : B(a) → Π(x:A). Eq(A,a,x) → B(x)            — transport along the path
#   evalLift   : Π(b). eval(lift(b)) = b                    — free by computation
#   liftEval   : Π(α). Π(x). Π(p). lift(eval(α))(x,p) = α(x,p) — by path induction
{ prelude }:

let
  inherit (prelude) H verify U0 Eq Refl J Pi lam app;

  # B : A → U₀  (a type family over A)
  TyFam = A: Pi "_" A (_: U0);

  # Π(x:A). Eq(A,a,x) → B(x)  (sections of B along paths from a)
  SectionTy = A: a: B: Pi "x" A (x: Pi "_" (Eq A a x) (_: app B x));

  # J motive for lift: λy.λ_.B(y)
  liftMotive = A: a: B:
    lam "y" A (y: lam "_" (Eq A a y) (_: app B y));

in
rec {

  # -- eval: apply the section at the universal element (a, refl) --

  yonedaEvalTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "_" (SectionTy A a B) (alpha:
      app B a))));

  yonedaEvalImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "alpha" (SectionTy A a B) (alpha:
      app (app alpha a) (H.ann Refl (Eq A a a))))));

  yonedaEval = verify yonedaEvalTy yonedaEvalImpl;

  # -- lift: transport along the path using J --

  yonedaLiftTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "b" (app B a) (b:
      SectionTy A a B))));

  yonedaLiftImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "b" (app B a) (b:
      lam "x" A (x: lam "p" (Eq A a x) (p:
        J A a (liftMotive A a B) b x p))))));

  yonedaLift = verify yonedaLiftTy yonedaLiftImpl;

  # -- evalLift: eval(lift(b)) = b — free by computation --
  #
  # Unfolding: eval(lift(b)) = lift(b)(a,refl) = J(A,a,M,b,a,refl) = b.
  # J reduces on refl, so the proof is Refl.

  evalLiftTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "b" (app B a) (b:
      Eq (app B a)
        (J A a (liftMotive A a B) b a (H.ann Refl (Eq A a a)))
        b))));

  evalLiftImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "b" (app B a) (b:
      H.ann Refl
        (Eq (app B a)
          (J A a (liftMotive A a B) b a (H.ann Refl (Eq A a a)))
          b)))));

  evalLift = verify evalLiftTy evalLiftImpl;

  # -- liftEval: lift(eval(α),x,p) = α(x,p) — by path induction --
  #
  # Expanded: J(A,a,λy.λ_.B(y), α(a,refl), x, p) = α(x,p).
  # By J on p. At the base case (x=a, p=refl), both sides reduce to α(a,refl).

  liftEvalTy = Pi "A" U0 (A: Pi "a" A (a: Pi "B" (TyFam A) (B:
    Pi "alpha" (SectionTy A a B) (alpha:
      Pi "x" A (x: Pi "p" (Eq A a x) (p:
        Eq (app B x)
          (J A a (liftMotive A a B)
            (app (app alpha a) (H.ann Refl (Eq A a a)))
            x
            p)
          (app (app alpha x) p)))))));

  liftEvalImpl = lam "A" U0 (A: lam "a" A (a: lam "B" (TyFam A) (B:
    lam "alpha" (SectionTy A a B) (alpha:
      lam "x" A (x: lam "p" (Eq A a x) (p:
        J A a
          (lam "y" A (y: lam "q" (Eq A a y) (q:
            Eq (app B y)
              (J A a (liftMotive A a B)
                (app (app alpha a) (H.ann Refl (Eq A a a)))
                y
                q)
              (app (app alpha y) q))))
          (H.ann Refl
            (Eq (app B a)
              (J A a (liftMotive A a B)
                (app (app alpha a) (H.ann Refl (Eq A a a)))
                a
                (H.ann Refl (Eq A a a)))
              (app (app alpha a) (H.ann Refl (Eq A a a)))))
          x
          p))))));

  liftEval = verify liftEvalTy liftEvalImpl;
}
