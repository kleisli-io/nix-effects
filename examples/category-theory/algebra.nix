# Algebraic structures as macro-generated datatypes.
#
# Each structure is a single-constructor datatype with named fields. Later
# fields depend on earlier ones through `fieldD`, so algebraic laws
# reference prior structure by name (`prev.op`, `prev.id`, `prev.comp`)
# instead of peeking into nested Σ-projections.
#
# The family of types:
#   MonoidOf A         — (op, e, assoc, lid, rid) over A.
#   CategoryOf Obj Hom — (id, comp, lid, rid, assoc) over (Obj, Hom).
#
# The family of instances:
#   natAddMonoid : MonoidOf Nat            — (Nat, +, 0).
#   natCategory  : CategoryOf Unit natHom  — one-object category whose
#                                            hom-set is (Nat, +, 0).
#
# Each instance is a Nix record exposing both the HOAS components (so
# downstream modules can refer to `.op`, `.comp`, etc. by name) and the
# bundled (ty, impl) pair that the kernel checks.
#
# The single non-trivial theorem lives here because it is categorical in
# flavour: composition in `natCategory` is commutative. The proof is one
# line once the instance exists — `annAddComm` gives exactly the witness
# that `comp` needs.
#
# A note on macro design: `Obj` and `Hom` are `datatypeP` parameters, not
# in-constructor data fields. The macro encodes data fields via kernel
# `descArg`, which only holds small types (`S : U 0`). A `U 0`-valued or
# `Π Obj. Π Obj. U 0`-valued field would live at `U 1` and so cannot be
# a description argument. Parameters thread through a plain Π-binder
# (`paramPi`), where no such restriction applies. This is the general
# recipe for datatypes that carry universe-level structure.
{ prelude, arithmetic }:

let
  inherit (prelude) H verify Nat U0 Unit Eq Refl Pi lam app;
  inherit (arithmetic)
    addImpl
    annAddLeftZero annAddRightZero annAddAssoc annAddComm;
  inherit (prelude) addHoas;

  # -- Monoid -------------------------------------------------------------

  # Monoid over A: five fields (op, e, assoc, lid, rid).
  MonoidDT = H.datatypeP "Monoid" [{ name = "A"; kind = U0; }] (ps:
    let A = builtins.elemAt ps 0; in [
      (H.con "mk" [
        (H.field "op" (Pi "_" A (_: Pi "_" A (_: A))))
        (H.field "e" A)
        (H.fieldD "assoc" (prev:
          Pi "x" A (x: Pi "y" A (y: Pi "z" A (z:
            Eq A
              (app (app prev.op (app (app prev.op x) y)) z)
              (app (app prev.op x) (app (app prev.op y) z)))))))
        (H.fieldD "lid" (prev:
          Pi "x" A (x:
            Eq A (app (app prev.op prev.e) x) x)))
        (H.fieldD "rid" (prev:
          Pi "x" A (x:
            Eq A (app (app prev.op x) prev.e) x)))
      ])
    ]);

  # -- Category -----------------------------------------------------------

  # Category over (Obj, Hom): five fields (id, comp, lid, rid, assoc).
  CategoryDT = H.datatypeP "Category"
    [{ name = "Obj"; kind = U0; }
      {
        name = "Hom";
        kind = ms:
          let Obj = builtins.elemAt ms 0;
          in Pi "_" Obj (_: Pi "_" Obj (_: U0));
      }]
    (ps:
      let Obj = builtins.elemAt ps 0; Hom = builtins.elemAt ps 1; in [
        (H.con "mk" [
          (H.field "id" (Pi "a" Obj (a: app (app Hom a) a)))
          (H.fieldD "comp" (_prev:
            Pi "a" Obj (a: Pi "b" Obj (b: Pi "c" Obj (c:
              Pi "_" (app (app Hom b) c) (_:
                Pi "_" (app (app Hom a) b) (_:
                  app (app Hom a) c)))))))
          (H.fieldD "lid" (prev:
            Pi "a" Obj (a: Pi "b" Obj (b:
              Pi "f" (app (app Hom a) b) (f:
                Eq (app (app Hom a) b)
                  (app (app (app (app (app prev.comp a) a) b) f) (app prev.id a))
                  f)))))
          (H.fieldD "rid" (prev:
            Pi "a" Obj (a: Pi "b" Obj (b:
              Pi "f" (app (app Hom a) b) (f:
                Eq (app (app Hom a) b)
                  (app (app (app (app (app prev.comp a) b) b) (app prev.id b)) f)
                  f)))))
          (H.fieldD "assoc" (prev:
            Pi "a" Obj (a: Pi "b" Obj (b: Pi "c" Obj (c: Pi "d" Obj (d:
              Pi "f" (app (app Hom a) b) (f:
                Pi "g" (app (app Hom b) c) (g:
                  Pi "h" (app (app Hom c) d) (h:
                    Eq (app (app Hom a) d)
                      (app
                        (app (app (app (app prev.comp a) b) d)
                          (app (app (app (app (app prev.comp b) c) d) h) g))
                        f)
                      (app
                        (app (app (app (app prev.comp a) c) d)
                          h)
                        (app (app (app (app (app prev.comp a) b) c) g) f)))))))))))
        ])
      ]);

in
rec {

  inherit MonoidDT CategoryDT;

  # Type constructors.
  #   MonoidOf A         = μ of the Monoid description, applied to A.
  #   CategoryOf Obj Hom = μ of the Category description, applied to
  #                        the object sort and the hom family.
  MonoidOf = A: app MonoidDT.T A;
  CategoryOf = Obj: Hom: app (app CategoryDT.T Obj) Hom;

  # -- The monoid (Nat, +, 0) -------------------------------------------

  # Components exposed by name so functor.nix can reference them
  # uniformly (e.g. `natAddMonoid.op` instead of `addImpl`).
  natAddMonoid = rec {
    A = Nat;
    op = addImpl;
    e = H.zero;
    assoc = annAddAssoc;
    lid = annAddLeftZero;
    rid = annAddRightZero;

    ty = MonoidOf A;
    impl = builtins.foldl' app MonoidDT.mk [ A op e assoc lid rid ];
  };

  # -- The one-object category over Nat ---------------------------------
  #
  #   Obj = Unit          (one object)
  #   Hom _ _ = Nat        (morphisms are naturals)
  #   id _ = 0             (identity is zero)
  #   comp _ _ _ g f = g+f (composition is addition)
  #
  # All three laws transfer from arithmetic:
  #   lid   : f · id = f   ≡  f + 0 = f       (addRightZero)
  #   rid   : id · f = f   ≡  0 + f = f       (refl — left zero is computational)
  #   assoc : h · (g · f) = (h · g) · f       (addAssoc, re-associated)
  natCategory = rec {
    Obj = Unit;
    Hom = lam "_" Unit (_: lam "_" Unit (_: Nat));
    idTy = Pi "_" Unit (_: Nat);
    id_ = H.ann (lam "_" Unit (_: H.zero)) idTy;
    compTy = Pi "_" Unit (_: Pi "_" Unit (_: Pi "_" Unit (_:
      Pi "_" Nat (_: Pi "_" Nat (_: Nat)))));
    comp = H.ann
      (lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_:
        lam "g" Nat (g: lam "f" Nat (f: addHoas g f))))))
      compTy;
    lid = lam "_" Unit (_: lam "_" Unit (_:
      lam "f" Nat (f: app annAddRightZero f)));
    rid = lam "_" Unit (_: lam "_" Unit (_:
      lam "f" Nat (f: H.ann Refl (Eq Nat (addHoas H.zero f) f))));
    assoc = lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_:
      lam "f" Nat (f: lam "g" Nat (g: lam "h" Nat (h:
        app (app (app annAddAssoc h) g) f)))))));

    ty = CategoryOf Obj Hom;
    impl = builtins.foldl' app CategoryDT.mk
      [ Obj Hom id_ comp lid rid assoc ];
  };

  # -- Composition in natCategory is commutative ------------------------
  #
  # Stated through `natCategory.comp` so the type reads as a statement
  # about morphisms in the category, not about raw `add`. Both sides
  # β-reduce to `add g f = add f g`; the proof is `addComm` at those
  # arguments.
  compCommTy =
    let o = H.tt; in
    Pi "f" Nat (f: Pi "g" Nat (g:
      Eq Nat
        (app (app (app (app (app natCategory.comp o) o) o) g) f)
        (app (app (app (app (app natCategory.comp o) o) o) f) g)));

  compCommImpl = lam "f" Nat (f: lam "g" Nat (g:
    app (app annAddComm g) f));

  compComm = verify compCommTy compCommImpl;
}
