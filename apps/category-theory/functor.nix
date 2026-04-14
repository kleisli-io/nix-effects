# Doubling endofunctor on the Nat category.
#
# The doubling map F_mor(f) = add(f,f) is a monoid homomorphism
# (Nat,+,0) → (Nat,+,0), hence an endofunctor on B(Nat,+,0).
#
# Functoriality:
#   preserveId:   F_mor(0) = 0                     (free by computation)
#   preserveComp: F_mor(add(g,f)) = add(F_mor(g), F_mor(f))
#                 i.e. add(add(g,f), add(g,f)) = add(add(g,g), add(f,f))
#
# The preserveComp proof is a 5-step equational rewriting chain using
# associativity and commutativity of addition.
{ prelude, arithmetic }:

let
  inherit (prelude) H verify Nat Eq Refl Pi lam app
                    addHoas symProof transProof congAddRight;
  inherit (arithmetic) annAddAssoc annAddComm;

in rec {

  doubleTy = Pi "f" Nat (f: Nat);
  doubleImpl = lam "f" Nat (f: addHoas f f);
  double = verify doubleTy doubleImpl;

  # F_mor(0) = add(0,0) = 0 — free by computation
  preserveIdTy = Eq Nat (addHoas H.zero H.zero) H.zero;
  preserveIdImpl = Refl;
  preserveId = verify preserveIdTy preserveIdImpl;

  # F_mor(add(g,f)) = add(F_mor(g), F_mor(f))
  #
  # Proof chain:
  #   add(gf, gf)
  #   = add(g, add(f, gf))         [1: assoc(g, f, gf)]
  #   = add(g, add(f, add(f, g)))  [2: congRight(addComm(g,f))]
  #   = add(g, add(ff, g))         [3: congRight(sym(assoc(f,f,g)))]
  #   = add(g, add(g, ff))         [4: congRight(addComm(ff,g))]
  #   = add(gg, ff)                [5: sym(assoc(g,g,ff))]
  preserveCompTy = Pi "g" Nat (g: Pi "f" Nat (f:
    Eq Nat
      (addHoas (addHoas g f) (addHoas g f))
      (addHoas (addHoas g g) (addHoas f f))));

  preserveCompImpl = lam "g" Nat (g: lam "f" Nat (f:
    let
      gf = addHoas g f;
      ff = addHoas f f;
      gg = addHoas g g;
      s1 = app (app (app annAddAssoc g) f) gf;

      commGF = app (app annAddComm g) f;
      s2 = congAddRight f gf (addHoas f g) commGF;

      s12 = transProof Nat
        (addHoas gf gf)
        (addHoas g (addHoas f gf))
        (addHoas g (addHoas f (addHoas f g)))
        s1
        (congAddRight g (addHoas f gf) (addHoas f (addHoas f g)) s2);

      s3 = symProof Nat
        (addHoas ff g)
        (addHoas f (addHoas f g))
        (app (app (app annAddAssoc f) f) g);

      s123 = transProof Nat
        (addHoas gf gf)
        (addHoas g (addHoas f (addHoas f g)))
        (addHoas g (addHoas ff g))
        s12
        (congAddRight g (addHoas f (addHoas f g)) (addHoas ff g) s3);

      s4 = app (app annAddComm ff) g;

      s1234 = transProof Nat
        (addHoas gf gf)
        (addHoas g (addHoas ff g))
        (addHoas g (addHoas g ff))
        s123
        (congAddRight g (addHoas ff g) (addHoas g ff) s4);

      s5 = symProof Nat
        (addHoas gg ff)
        (addHoas g (addHoas g ff))
        (app (app (app annAddAssoc g) g) ff);

    in transProof Nat
      (addHoas gf gf)
      (addHoas g (addHoas g ff))
      (addHoas gg ff)
      s1234 s5));

  preserveComp = verify preserveCompTy preserveCompImpl;
}
