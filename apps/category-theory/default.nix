# Category theory library — verified proofs from the MLTT kernel
#
# Every theorem is type-checked at Nix eval time. If evaluation completes,
# the proofs are correct. Extracted functions are callable Nix values.
#
# Modules:
#   combinators  — sym, trans, cong (derived from J elimination)
#   arithmetic   — add with 7 verified properties including commutativity
#   algebra      — Monoid, Category types; (Nat,+,0) instances
#   functor      — doubling endofunctor with functoriality proof
#
# Test:
#   nix-instantiate --eval --strict --expr \
#     'let fx = import ./nix/nix-effects {}; in (import ./nix/nix-effects/apps/category-theory { inherit fx; }).tests.allPass'
#
# Use:
#   nix-instantiate --eval --strict --expr \
#     'let fx = import ./nix/nix-effects {}; in (import ./nix/nix-effects/apps/category-theory { inherit fx; }).api.add 3 5'
{ fx }:

let
  prelude     = import ./prelude.nix { inherit fx; };
  combinators = import ./combinators.nix { inherit prelude; };
  arithmetic  = import ./arithmetic.nix { inherit prelude; };
  algebra     = import ./algebra.nix { inherit prelude arithmetic; };
  functor     = import ./functor.nix { inherit prelude arithmetic; };

  H = prelude.H;
  checkHoas = H.checkHoas;

  # true when impl type-checks at ty, false otherwise
  checks = ty: impl: !(checkHoas ty impl ? error);

in rec {

  # -- Public API: extracted Nix functions --

  api = {
    # Proof combinators
    inherit (combinators) sym trans cong;

    # Arithmetic
    inherit (arithmetic) add addLeftZero addRightZero addSucc addAssoc
                         addRightSucc addComm;

    # Algebraic structures
    inherit (algebra) natAddMonoid natCategory compComm;

    # Functor
    inherit (functor) double preserveId preserveComp;
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
    inherit (algebra) MonoidOf natAddMonoidTy natAddMonoidImpl
                      CategoryTy natCategoryImpl
                      compCommTy compCommImpl;
    inherit (functor) doubleTy doubleImpl
                      preserveIdTy preserveIdImpl
                      preserveCompTy preserveCompImpl;
  };

  # -- Tests: each evaluates to true if the proof type-checks --

  tests = rec {

    # Proof combinators
    sym   = checks combinators.symTy combinators.symImpl;
    trans = checks combinators.transTy combinators.transImpl;
    cong  = checks combinators.congTy combinators.congImpl;

    # Arithmetic: computational lemmas (proved by refl)
    addLeftZero = checks arithmetic.addLeftZeroTy arithmetic.addLeftZeroImpl;
    addSucc     = checks arithmetic.addSuccTy arithmetic.addSuccImpl;

    # Arithmetic: inductive proofs
    addRightZero = checks arithmetic.addRightZeroTy arithmetic.addRightZeroImpl;
    addAssoc     = checks arithmetic.addAssocTy arithmetic.addAssocImpl;
    addRightSucc = checks arithmetic.addRightSuccTy arithmetic.addRightSuccImpl;
    addComm      = checks arithmetic.addCommTy arithmetic.addCommImpl;

    # Algebraic structures
    natAddMonoid = checks algebra.natAddMonoidTy algebra.natAddMonoidImpl;
    natCategory  = checks algebra.CategoryTy algebra.natCategoryImpl;
    compComm     = checks algebra.compCommTy algebra.compCommImpl;

    # Functor
    double       = checks functor.doubleTy functor.doubleImpl;
    preserveId   = checks functor.preserveIdTy functor.preserveIdImpl;
    preserveComp = checks functor.preserveCompTy functor.preserveCompImpl;

    # Extracted functions compute correctly
    addComputes      = api.add 3 5 == 8;
    addComm7_3       = api.add 7 3 == api.add 3 7;
    doubleComputes   = api.double 4 == 8;

    allPass =
      sym && trans && cong
      && addLeftZero && addSucc
      && addRightZero && addAssoc && addRightSucc && addComm
      && natAddMonoid && natCategory && compComm
      && double && preserveId && preserveComp
      && addComputes && addComm7_3 && doubleComputes;
  };
}
