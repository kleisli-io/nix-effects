# Category theory library — a guided tour of the MLTT kernel.
#
# Every theorem in this library is type-checked by the kernel at Nix
# evaluation time. If evaluation completes, the proofs are correct.
# Extracted functions are callable Nix values.
#
# The modules are arranged so that each chapter builds on the previous
# one. Read them in order:
#
#   1. combinators.nix — sym, trans, cong derived from J.
#   2. arithmetic.nix  — `add` on Nat with seven verified properties
#                        (left/right zero, assoc, succ shifts, comm).
#   3. algebra.nix     — Monoid and Category as macro-generated
#                        datatypes (single constructor, named fields,
#                        dependent law fields). Instances
#                        `natAddMonoid : MonoidOf Nat` and
#                        `natCategory : CategoryOf Unit natHom`.
#                        Closes with the theorem that composition in
#                        `natCategory` is commutative.
#   4. functor.nix     — MonoidHom and Functor as two more macro
#                        datatypes. The doubling map is packaged as
#                        `doubleHom` (a monoid homomorphism) and
#                        `doubleFunctor` (an endofunctor on
#                        `natCategory`) — the same map seen through two
#                        equivalent lenses.
#   5. yoneda.nix      — Yoneda's lemma in the types-as-groupoids form,
#                        with both the evaluate/lift round-trips.
#
# Test everything:
#   nix eval --impure --expr \
#     'let fx = import ./nix/nix-effects {};
#      in builtins.all (x: x)
#        (builtins.attrValues (import ./nix/nix-effects/apps/category-theory { inherit fx; }).tests)'
#
# Call the extracted add:
#   nix eval --impure --expr \
#     'let fx = import ./nix/nix-effects {};
#      in (import ./nix/nix-effects/apps/category-theory { inherit fx; }).api.add 3 5'
{ fx }:

let
  prelude = import ./prelude.nix { inherit fx; };
  combinators = import ./combinators.nix { inherit prelude; };
  arithmetic = import ./arithmetic.nix { inherit prelude; };
  algebra = import ./algebra.nix { inherit prelude arithmetic; };
  functor = import ./functor.nix { inherit prelude arithmetic algebra; };
  yoneda = import ./yoneda.nix { inherit prelude; };

  H = prelude.H;
  checkHoas = H.checkHoas;

  # true when impl type-checks at ty, false otherwise
  checks = ty: impl: !(checkHoas ty impl ? error);

in
rec {

  # -- Public API: extracted Nix functions --

  api = {
    # Proof combinators
    inherit (combinators) sym trans cong;

    # Arithmetic
    inherit (arithmetic) add addLeftZero addRightZero addSucc addAssoc
      addRightSucc addComm;

    # Algebraic structures (compComm is an extractable equality proof;
    # the instances themselves are packaged HOAS records exposed under
    # `.hoas.natAddMonoid` / `.hoas.natCategory`).
    inherit (algebra) compComm;

    # Functor
    inherit (functor) double preserveId preserveComp;

    # Yoneda
    inherit (yoneda) yonedaEval yonedaLift evalLift liftEval;
  };

  # -- HOAS types and implementations (for advanced use) --

  hoas = {
    inherit (combinators) symTy symImpl transTy transImpl congTy congImpl;
    inherit (arithmetic)
      addTy addImpl
      addLeftZeroTy addLeftZeroImpl
      addSuccTy addSuccImpl
      addRightZeroTy addRightZeroImpl
      addAssocTy addAssocImpl
      addRightSuccTy addRightSuccImpl
      addCommTy addCommImpl;
    inherit (algebra) MonoidOf CategoryOf natAddMonoid natCategory
      compCommTy compCommImpl;
    inherit (functor) MonoidHomOf FunctorOf doubleHom doubleFunctor
      doubleTy doubleImpl
      preserveIdTy preserveIdImpl
      preserveCompTy preserveCompImpl;
    inherit (yoneda) yonedaEvalTy yonedaEvalImpl
      yonedaLiftTy yonedaLiftImpl
      evalLiftTy evalLiftImpl
      liftEvalTy liftEvalImpl;
  };

  # -- Tests: each evaluates to true if the proof type-checks --

  tests = rec {

    # Proof combinators
    sym = checks combinators.symTy combinators.symImpl;
    trans = checks combinators.transTy combinators.transImpl;
    cong = checks combinators.congTy combinators.congImpl;

    # Arithmetic: computational lemmas (proved by refl)
    addLeftZero = checks arithmetic.addLeftZeroTy arithmetic.addLeftZeroImpl;
    addSucc = checks arithmetic.addSuccTy arithmetic.addSuccImpl;

    # Arithmetic: inductive proofs
    addRightZero = checks arithmetic.addRightZeroTy arithmetic.addRightZeroImpl;
    addAssoc = checks arithmetic.addAssocTy arithmetic.addAssocImpl;
    addRightSucc = checks arithmetic.addRightSuccTy arithmetic.addRightSuccImpl;
    addComm = checks arithmetic.addCommTy arithmetic.addCommImpl;

    # Algebraic structures
    natAddMonoid = checks algebra.natAddMonoid.ty algebra.natAddMonoid.impl;
    natCategory = checks algebra.natCategory.ty algebra.natCategory.impl;
    compComm = checks algebra.compCommTy algebra.compCommImpl;

    # Functor — the extracted map and its laws at raw arithmetic
    double = checks functor.doubleTy functor.doubleImpl;
    preserveId = checks functor.preserveIdTy functor.preserveIdImpl;
    preserveComp = checks functor.preserveCompTy functor.preserveCompImpl;

    # Functor — the same map packaged as a monoid homomorphism
    # and as a categorical endofunctor
    doubleHom = checks functor.doubleHom.ty functor.doubleHom.impl;
    doubleFunctor = checks functor.doubleFunctor.ty functor.doubleFunctor.impl;

    # Yoneda's lemma
    yonedaEval = checks yoneda.yonedaEvalTy yoneda.yonedaEvalImpl;
    yonedaLift = checks yoneda.yonedaLiftTy yoneda.yonedaLiftImpl;
    evalLift = checks yoneda.evalLiftTy yoneda.evalLiftImpl;
    liftEval = checks yoneda.liftEvalTy yoneda.liftEvalImpl;

    # Extracted functions compute correctly
    addComputes = api.add 3 5 == 8;
    addComm7_3 = api.add 7 3 == api.add 3 7;
    doubleComputes = api.double 4 == 8;
  };
}
