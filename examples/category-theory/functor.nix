# Structure-preserving maps, as macro-generated datatypes.
#
# Two new types are defined here, both of which are single-constructor
# records built with the same `datatypeP` surface used in algebra.nix:
#
#   MonoidHomOf (A, opA, eA) (B, opB, eB)
#       — maps between monoids that preserve identity and operation.
#
#   FunctorOf   C D
#       — functors between categories. `C` and `D` are given by their
#         object sort, hom family, identity and composition.
#
# The running example is `doubling : (Nat, +, 0) → (Nat, +, 0)`, `f ↦ f+f`.
# We build it twice:
#
#   1. `doubleHom : MonoidHomOf (Nat, +, 0) (Nat, +, 0)` — as a monoid
#      homomorphism. `preserveComp` becomes the arithmetic identity
#      `add(add(g,f), add(g,f)) = add(add(g,g), add(f,f))`, proved by a
#      five-step equational chain using `annAddAssoc` and `annAddComm`.
#
#   2. `doubleFunctor : FunctorOf natCategory natCategory` — the same map
#      viewed as an endofunctor on the one-object category from
#      algebra.nix. Because a monoid is a one-object category, the
#      functor-law proofs reuse the monoid-hom proofs verbatim.
#
# The extracted Nix function `double : Nat → Nat` is the visible payload;
# the instances above certify that it respects the algebraic structure.
{ prelude, arithmetic, algebra }:

let
  inherit (prelude) H verify Nat U0 Unit Eq Refl Pi lam app
    addHoas symProof transProof congAddRight;
  inherit (arithmetic) annAddAssoc annAddComm;
  inherit (algebra) natAddMonoid natCategory;

  # -- MonoidHomDT ------------------------------------------------------
  #
  # Six parameters describe the source and target monoids; three data
  # fields describe the map and its two laws.
  #
  # Every later param (`opA`, `eA`, `opB`, `eB`) depends on prior params,
  # so it uses the function form of `kind` — the same `ms:` idiom as the
  # `Hom` parameter of `CategoryDT`.
  MonoidHomDT = H.datatypeP "MonoidHom"
    [{ name = "A"; kind = U0; }
      {
        name = "opA";
        kind = ms:
          let A = builtins.elemAt ms 0;
          in Pi "_" A (_: Pi "_" A (_: A));
      }
      { name = "eA"; kind = ms: builtins.elemAt ms 0; }
      { name = "B"; kind = U0; }
      {
        name = "opB";
        kind = ms:
          let B = builtins.elemAt ms 3;
          in Pi "_" B (_: Pi "_" B (_: B));
      }
      { name = "eB"; kind = ms: builtins.elemAt ms 3; }]
    (ps:
      let
        A = builtins.elemAt ps 0;
        opA = builtins.elemAt ps 1;
        eA = builtins.elemAt ps 2;
        B = builtins.elemAt ps 3;
        opB = builtins.elemAt ps 4;
        eB = builtins.elemAt ps 5;
      in
      [
        (H.con "mk" [
          (H.field "map" (Pi "_" A (_: B)))
          (H.fieldD "preserveId" (prev:
            Eq B (app prev.map eA) eB))
          (H.fieldD "preserveOp" (prev:
            Pi "x" A (x: Pi "y" A (y:
              Eq B
                (app prev.map (app (app opA x) y))
                (app (app opB (app prev.map x)) (app prev.map y))))))
        ])
      ]);

  # -- FunctorDT --------------------------------------------------------
  #
  # Eight parameters describe the source and target categories; four
  # data fields describe the functor action (fobj, fmap) and the two
  # laws (preserveId, preserveComp).
  FunctorDT = H.datatypeP "Functor"
    [{ name = "ObjC"; kind = U0; }
      {
        name = "HomC";
        kind = ms:
          let O = builtins.elemAt ms 0;
          in Pi "_" O (_: Pi "_" O (_: U0));
      }
      {
        name = "idC";
        kind = ms:
          let O = builtins.elemAt ms 0; Hom = builtins.elemAt ms 1;
          in Pi "a" O (a: app (app Hom a) a);
      }
      {
        name = "compC";
        kind = ms:
          let O = builtins.elemAt ms 0; Hom = builtins.elemAt ms 1;
          in Pi "a" O (a: Pi "b" O (b: Pi "c" O (c:
            Pi "_" (app (app Hom b) c) (_:
              Pi "_" (app (app Hom a) b) (_:
                app (app Hom a) c)))));
      }
      { name = "ObjD"; kind = U0; }
      {
        name = "HomD";
        kind = ms:
          let O = builtins.elemAt ms 4;
          in Pi "_" O (_: Pi "_" O (_: U0));
      }
      {
        name = "idD";
        kind = ms:
          let O = builtins.elemAt ms 4; Hom = builtins.elemAt ms 5;
          in Pi "a" O (a: app (app Hom a) a);
      }
      {
        name = "compD";
        kind = ms:
          let O = builtins.elemAt ms 4; Hom = builtins.elemAt ms 5;
          in Pi "a" O (a: Pi "b" O (b: Pi "c" O (c:
            Pi "_" (app (app Hom b) c) (_:
              Pi "_" (app (app Hom a) b) (_:
                app (app Hom a) c)))));
      }]
    (ps:
      let
        ObjC = builtins.elemAt ps 0;
        HomC = builtins.elemAt ps 1;
        idC = builtins.elemAt ps 2;
        compC = builtins.elemAt ps 3;
        ObjD = builtins.elemAt ps 4;
        HomD = builtins.elemAt ps 5;
        idD = builtins.elemAt ps 6;
        compD = builtins.elemAt ps 7;
      in
      [
        (H.con "mk" [
          (H.field "fobj" (Pi "_" ObjC (_: ObjD)))
          (H.fieldD "fmap" (prev:
            Pi "a" ObjC (a: Pi "b" ObjC (b:
              Pi "_" (app (app HomC a) b) (_:
                app (app HomD (app prev.fobj a)) (app prev.fobj b))))))
          (H.fieldD "preserveId" (prev:
            Pi "a" ObjC (a:
              Eq (app (app HomD (app prev.fobj a)) (app prev.fobj a))
                (app (app (app prev.fmap a) a) (app idC a))
                (app idD (app prev.fobj a)))))
          (H.fieldD "preserveComp" (prev:
            Pi "a" ObjC (a: Pi "b" ObjC (b: Pi "c" ObjC (c:
              Pi "g" (app (app HomC b) c) (g:
                Pi "f" (app (app HomC a) b) (f:
                  Eq (app (app HomD (app prev.fobj a)) (app prev.fobj c))
                    (app (app (app prev.fmap a) c)
                      (app (app (app (app (app compC a) b) c) g) f))
                    (app
                      (app
                        (app
                          (app
                            (app compD
                              (app prev.fobj a))
                            (app prev.fobj b))
                          (app prev.fobj c))
                        (app (app (app prev.fmap b) c) g))
                      (app (app (app prev.fmap a) b) f)))))))))
        ])
      ]);

in
rec {

  inherit MonoidHomDT FunctorDT;

  # Type constructors packaging the six-/eight-tuple of parameters.
  MonoidHomOf = src: tgt:
    app
      (app
        (app
          (app
            (app
              (app MonoidHomDT.T
                src.A)
              src.op)
            src.e)
          tgt.A)
        tgt.op)
      tgt.e;

  FunctorOf = C: D:
    app
      (app
        (app
          (app
            (app
              (app
                (app
                  (app FunctorDT.T
                    C.Obj)
                  C.Hom)
                C.id_)
              C.comp)
            D.Obj)
          D.Hom)
        D.id_)
      D.comp;

  # -- The doubling map -------------------------------------------------

  doubleTy = Pi "f" Nat (_: Nat);
  doubleImpl = lam "f" Nat (f: addHoas f f);
  double = verify doubleTy doubleImpl;

  # -- preserveId: double(0) = 0 ----------------------------------------
  # Free by computation: add(0, 0) reduces to 0.
  preserveIdTy = Eq Nat (addHoas H.zero H.zero) H.zero;
  preserveIdImpl = Refl;
  preserveId = verify preserveIdTy preserveIdImpl;
  annPreserveId = H.ann preserveIdImpl preserveIdTy;

  # -- preserveComp (raw): double(g+f) = double(g) + double(f) ---------
  #
  # Equivalently:  add(add(g,f), add(g,f)) = add(add(g,g), add(f,f)).
  # Proof chain (abbreviating `gf = add g f`, `gg = add g g`, `ff = add f f`):
  #   add(gf, gf)
  #   = add(g, add(f, gf))          [1: annAddAssoc g f gf]
  #   = add(g, add(f, add(f, g)))   [2: congAddRight f . addComm g f]
  #   = add(g, add(ff, g))          [3: congAddRight f . sym (assoc f f g)]
  #   = add(g, add(g, ff))          [4: congAddRight g . addComm ff g]
  #   = add(gg, ff)                 [5: sym (assoc g g ff)]
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

    in
    transProof Nat
      (addHoas gf gf)
      (addHoas g (addHoas g ff))
      (addHoas gg ff)
      s1234
      s5));

  preserveComp = verify preserveCompTy preserveCompImpl;

  # Ann'd forms for use inside larger proof terms (arithmetic.nix uses
  # the same convention for its `annAdd*` lemmas).
  annPreserveComp = H.ann preserveCompImpl preserveCompTy;

  # -- doubleHom : MonoidHomOf (Nat,+,0) (Nat,+,0) ---------------------
  #
  # Packages `double` together with the two laws as a single-constructor
  # record. `preserveOp`'s field type asks for `preserveComp`'s shape
  # with slightly different bracketing (`map (opA x y) = opB (map x) (map y)`);
  # since `opA = opB = add` and `map = double`, it reduces to the same
  # equation and the same proof witnesses it.
  doubleHom = rec {
    map_ = doubleImpl;
    preserveId_ = annPreserveId;
    preserveOp_ = annPreserveComp;

    ty = MonoidHomOf natAddMonoid natAddMonoid;
    impl = builtins.foldl' app MonoidHomDT.mk
      [
        natAddMonoid.A
        natAddMonoid.op
        natAddMonoid.e
        natAddMonoid.A
        natAddMonoid.op
        natAddMonoid.e
        map_
        preserveId_
        preserveOp_
      ];
  };

  # -- doubleFunctor : FunctorOf natCategory natCategory ---------------
  #
  # A monoid is a one-object category; a monoid homomorphism between
  # one-object categories IS a functor between them. With
  # `ObjC = ObjD = Unit` and `HomC = HomD = λ_ _. Nat`, the functor
  # laws reduce to the monoid-hom laws applied at the unique object.
  #
  # `fobj` is the unique map `Unit → Unit`. `fmap` ignores the Unit
  # source/target arguments and doubles the morphism.
  doubleFunctor = rec {
    fobj = lam "_" Unit (u: u);
    fmap = lam "_" Unit (_: lam "_" Unit (_:
      lam "f" Nat (f: addHoas f f)));

    preserveId_ =
      lam "_" Unit (_:
        H.ann Refl (Eq Nat (addHoas H.zero H.zero) H.zero));

    preserveComp_ =
      lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_:
        lam "g" Nat (g: lam "f" Nat (f:
          app (app annPreserveComp g) f)))));

    ty = FunctorOf natCategory natCategory;
    impl = builtins.foldl' app FunctorDT.mk
      [
        natCategory.Obj
        natCategory.Hom
        natCategory.id_
        natCategory.comp
        natCategory.Obj
        natCategory.Hom
        natCategory.id_
        natCategory.comp
        fobj
        fmap
        preserveId_
        preserveComp_
      ];
  };
}
