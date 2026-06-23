# Flat predicate-stack datum for kernel-checkable refinement types. A code is a
# base carrier type paired with a finite list of predicates, all over that ONE
# carrier:
#
#   KType   := Sigma A:U_0. List (A -> Bool)        : U_1
#   beta t  := fst t                                : U_0   (carrier; ignores stack)
#   psi t   := \x. AND-fold of the stack at x       : beta t -> Bool
#   El t    := Sigma x:beta t. P (psi t x)          : U_0   (derived membership)
#   decide  := psi
#
# P : Bool -> U_0 with P true ~> Unit, P false ~> Void (the membership decoder).
# The base carrier is any U_0 type — a mu-encoded inductive (Record/Variant/Nat/
# Bool), a primitive (Int/String/any), or any other type — so a guard-free type
# of any carrier and a refinement whose predicate is a kernel decision over that
# carrier both internalize. The carrier is constant along refinement and the
# decider is the conjunction of the predicate stack, so a code at any nesting
# depth lives at the single universe U_1 and the decider is a single linear fold —
# no per-refinement universe rise.
#
# The decider is the LEFT (accumulator) fold: listElim with motive Bool->Bool,
# nil = identity, cons threading an accumulator conjoined on the left, seeded with
# true. This reduces in the same order a base-first stack accumulates, so the
# normal form is on the nose the conjunction (a right fold would leave a residual
# unit stuck on a neutral predicate). `refine` appends the new predicate at the
# TAIL so the accumulator conjoins it last.
#
# A predicate list stored inside the Sigma is annotated with its element type at
# construction so the polymorphic nil/cons specialise through the projection; the
# decider's eliminator and each top-level function carry their declared type via
# `ann` so applications in inference position resolve.
{ fx, api, ... }:

let
  H = fx.tc.hoas;
  app = H.app;

  # P : Bool -> U_0. Large elim into U_0 (motive codomain U_0 : U_1, K=1).
  P = b: H.boolElim 1 (H.lam "_" H.bool (_: H.u 0)) H.unit H.void b;

  # Boolean conjunction via the Bool eliminator (constant motive, K=0).
  andB = a: b: H.boolElim 0 (H.lam "_" H.bool (_: H.bool)) b H.false_ a;

  # The base is an arbitrary U_0 type; a predicate is a Bool decision over it.
  predTy = A: H.forall "_" A (_: H.bool);
  listP = A: H.listOf (predTy A);
  BB = H.forall "_" H.bool (_: H.bool);

  # KType : U_1. A base carrier type paired with a predicate stack over it.
  KType = H.sigma "A" (H.u 0) (A: listP A);

  # The accumulator AND-fold of a code's predicate stack at x. The eliminator is
  # annotated with its result type so the surrounding application checks.
  foldBody = t: x:
    let Pr = predTy (H.fst_ t); in
    app
      (H.ann
        (H.listElim 0 Pr (H.lam "_" (H.listOf Pr) (_: BB))
          (H.lam "acc" H.bool (acc: acc))
          (H.lam "p" Pr (p: H.lam "tl" (H.listOf Pr) (_: H.lam "ih" BB (ih:
            H.lam "acc" H.bool (acc: app ih (andB acc (app p x)))))))
          (H.snd_ t))
        BB)
      H.true_;

  betaTy = H.forall "t" KType (_: H.u 0);
  decideTy = H.forall "t" KType (t: H.forall "_" (H.fst_ t) (_: H.bool));
  elTy = H.forall "t" KType (_: H.u 0);

  # The internalized functions as closed kernel terms; each annotation carries the
  # declared type so applications infer it.
  betaFn = H.ann (H.lam "t" KType (t: H.fst_ t)) betaTy;
  decideFn = H.ann (H.lam "t" KType (t: H.lam "x" (H.fst_ t) (x: foldBody t x))) decideTy;
  psiFn = decideFn;
  ElFn = H.ann (H.lam "t" KType (t: H.sigma "x" (H.fst_ t) (x: P (app (app decideFn t) x)))) elTy;

  # Application wrappers.
  beta = t: app betaFn t;
  decide = t: app decideFn t;
  psi = decide;
  El = t: app ElFn t;

  # snoc: append a new outermost predicate at the tail of a stack.
  snocLE = A: xs: y:
    let Pr = predTy A; in
    H.listElim 0 Pr (H.lam "_" (H.listOf Pr) (_: H.listOf Pr))
      (H.cons y H.nil)
      (H.lam "h" Pr (h: H.lam "tl" (H.listOf Pr) (_: H.lam "ih" (H.listOf Pr) (ih: H.cons h ih))))
      xs;

  # Constructors. iota: a base carrier with the empty stack. refine: extend a
  # code's stack with a new predicate over its carrier. Each result carries its
  # KType type and each stored stack its element type, so projections and
  # applications resolve.
  #
  # refine reads its argument's fields through a TRUSTED annotation: t is a KType
  # by construction (an iota/refine result, each genuinely checked at its own
  # outer annotation), so re-checking it here would re-validate the whole inner
  # code at every layer — the redundant work that makes a depth-n chain quadratic.
  # The outer result annotation stays a genuine check, so `chk KType` of any code
  # is a real kernel judgment of that layer; deep well-typedness follows
  # compositionally from the per-layer judgments.
  #
  # The trusted code is bound ONCE via let_: the carrier and stack are read with
  # fst_/snd_ of that single binding, so the inner code is not replicated across
  # the projections. Substituting the projections instead (`A = fst_ ta` used at
  # three sites) copies the whole inner code per layer, making a deep chain's
  # normal form exponential; binding it keeps the chain linear.
  iota = A: H.ann (H.pair A (H.ann H.nil (listP A))) KType;
  refine = t: p:
    H.let_ "ta" KType (H.annTrusted t KType) (ta:
      H.ann (H.pair (H.fst_ ta) (H.ann (snocLE (H.fst_ ta) (H.snd_ ta) p) (listP (H.fst_ ta)))) KType);
in
{
  scope = {
    ktype = api.namespace {
      description = "fx.tc.kernel.ktype: flat predicate-stack datum — KType : U_1 (a base carrier type paired with a predicate stack over it), beta (the carrier), the accumulator-fold decider psi/decide, derived El, the membership decoder P, andB, and the iota/refine constructors.";
      value = {
        inherit P andB KType beta psi decide El betaFn decideFn psiFn ElFn betaTy decideTy elTy iota refine;
      };
    };
  };
}
