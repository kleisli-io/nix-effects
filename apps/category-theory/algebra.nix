# Algebraic structures: Monoid and Category as dependent types.
#
# Types:
#   MonoidOf(A) — carrier A with op, e, assoc, lid, rid
#   CategoryTy  — small category: Obj, Hom, id, comp, lid, rid, assoc
#
# Instances:
#   natAddMonoid  : MonoidOf(Nat)       — (Nat, add, 0)
#   natCategory   : CategoryTy          — one-object category from the Nat monoid
#
# Theorem:
#   compComm : ∀(f g : Nat). add(g,f) = add(f,g)
#   Morphism composition in natCategory is commutative (the endomorphism
#   monoid is abelian). Follows directly from addComm.
{ prelude, arithmetic }:

let
  inherit (prelude) H verify Nat U0 Unit Eq Refl Pi Sig lam app pair;
  inherit (arithmetic)
    addImpl
    addAssocImpl addLeftZeroImpl addRightZeroImpl
    annAddRightZero annAddAssoc annAddComm;
  inherit (prelude) addHoas;

in rec {

  # -- Monoid(A) --
  #
  # Σ(op : A → A → A).
  # Σ(e  : A).
  # Σ(assoc : ∀x y z. op(op(x,y),z) = op(x,op(y,z))).
  # Σ(lid   : ∀x. op(e,x) = x).
  #   (rid   : ∀x. op(x,e) = x)
  MonoidOf = A:
    Sig "op" (Pi "_" A (_: Pi "_" A (_: A))) (op:
      Sig "e" A (e:
        Sig "assoc" (Pi "x" A (x: Pi "y" A (y: Pi "z" A (z:
          Eq A
            (app (app op (app (app op x) y)) z)
            (app (app op x) (app (app op y) z)))))) (_:
          Sig "lid" (Pi "x" A (x: Eq A (app (app op e) x) x)) (_:
            Pi "x" A (x: Eq A (app (app op x) e) x)))));

  natAddMonoidTy = MonoidOf Nat;

  natAddMonoidImpl =
    pair addImpl
      (pair H.zero
        (pair addAssocImpl
          (pair addLeftZeroImpl addRightZeroImpl)));

  natAddMonoid = verify natAddMonoidTy natAddMonoidImpl;

  # -- Category --
  #
  # Σ(Obj  : U₀).
  # Σ(Hom  : Obj → Obj → U₀).
  # Σ(id   : ∀a. Hom(a,a)).
  # Σ(comp : ∀a b c. Hom(b,c) → Hom(a,b) → Hom(a,c)).
  # Σ(lid  : ∀a b. ∀f:Hom(a,b). comp(a,a,b,f,id(a)) = f).
  # Σ(rid  : ∀a b. ∀f:Hom(a,b). comp(a,b,b,id(b),f) = f).
  #   (assoc: ∀a b c d. ∀f g h. comp(a,b,d,comp(b,c,d,h,g),f) = comp(a,c,d,h,comp(a,b,c,g,f)))
  CategoryTy =
    Sig "Obj" U0 (Obj:
      Sig "Hom" (Pi "_" Obj (_: Pi "_" Obj (_: U0))) (Hom:
        Sig "id" (Pi "a" Obj (a: app (app Hom a) a)) (id_:
          Sig "comp" (Pi "a" Obj (a: Pi "b" Obj (b: Pi "c" Obj (c:
            Pi "g" (app (app Hom b) c) (g:
              Pi "f" (app (app Hom a) b) (f:
                app (app Hom a) c)))))) (comp:
            Sig "lid" (Pi "a" Obj (a: Pi "b" Obj (b:
              Pi "f" (app (app Hom a) b) (f:
                Eq (app (app Hom a) b)
                  (app (app (app (app (app comp a) a) b) f) (app id_ a))
                  f)))) (_:
              Sig "rid" (Pi "a" Obj (a: Pi "b" Obj (b:
                Pi "f" (app (app Hom a) b) (f:
                  Eq (app (app Hom a) b)
                    (app (app (app (app (app comp a) b) b) (app id_ b)) f)
                    f)))) (_:
                Pi "a" Obj (a: Pi "b" Obj (b: Pi "c" Obj (c: Pi "d" Obj (d:
                  Pi "f" (app (app Hom a) b) (f:
                    Pi "g" (app (app Hom b) c) (g:
                      Pi "h" (app (app Hom c) d) (h:
                        Eq (app (app Hom a) d)
                          (app (app (app (app (app comp a) b) d)
                            (app (app (app (app (app comp b) c) d) h) g)) f)
                          (app (app (app (app (app comp a) c) d)
                            h)
                            (app (app (app (app (app comp a) b) c) g) f))
                      )))))))))))));

  # One-object category (Nat, add, 0).
  # Obj = Unit, Hom(_,_) = Nat, id(_) = 0, comp(_,_,_,g,f) = add(g,f).
  # Laws transfer from arithmetic proofs:
  #   lid:   add(f, 0) = f             (addRightZero)
  #   rid:   add(0, f) = f             (free by computation)
  #   assoc: add(add(h,g), f) = add(h, add(g, f))  (addAssoc)
  natCategoryImpl =
    pair Unit
      (pair (lam "_" Unit (_: lam "_" Unit (_: Nat)))
        (pair (lam "_" Unit (_: H.zero))
          (pair (lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_:
                  lam "g" Nat (g: lam "f" Nat (f: addHoas g f))))))
            (pair
              (lam "_" Unit (_: lam "_" Unit (_:
                lam "f" Nat (f: app annAddRightZero f))))
              (pair
                (lam "_" Unit (_: lam "_" Unit (_:
                  lam "f" Nat (_: Refl))))
                (lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_: lam "_" Unit (_:
                  lam "f" Nat (f: lam "g" Nat (g: lam "h" Nat (h:
                    app (app (app annAddAssoc h) g) f)))))))))))));

  natCategory = verify CategoryTy natCategoryImpl;

  # -- Theorem: composition is commutative --
  #
  # In our one-object category, comp(g,f) = add(g,f).
  # This theorem says add(g,f) = add(f,g) — the endomorphism monoid is abelian.
  compCommTy = Pi "f" Nat (f: Pi "g" Nat (g:
    Eq Nat (addHoas g f) (addHoas f g)));

  compCommImpl = lam "f" Nat (f: lam "g" Nat (g:
    app (app annAddComm g) f));

  compComm = verify compCommTy compCommImpl;
}
