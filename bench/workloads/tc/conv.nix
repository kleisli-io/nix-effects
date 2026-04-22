# Conv-dominated whole-pipeline checks.
#
# The Nix evaluator offers no per-function profiling hook — every
# microbenchmark in this file is a whole-evaluation measurement of a
# workload whose cost is dominated by `fx.tc.conv`. Interpret results
# as "regression signal on the conv path", not as isolated conv
# timings.
#
# Representation note: the kernel follows named-de-Bruijn discipline —
# `mkLam`/`mkPi` carry a `name` string as a pretty-printing hint, but
# `conv` at VLam-vs-VLam (src/tc/conv.nix:62-64) instantiates both
# closures with a shared fresh variable and recurses on bodies without
# consulting `.name`. Two α-variant lambdas therefore remain attrset-
# distinct (Nix `==` differentiates them on `.name`) but conv equates
# them under binder instantiation. `alpha-equivalent` exercises that
# path; any `==`-keyed identity short-circuit added later in conv
# would not fire there, so the workload is the baseline against which
# such a short-circuit's coverage can be measured.
{ fx }:

let
  H = fx.types.hoas;

  # `datatype` with a long constructor list. Each entry is a nullary
  # constructor: checking any one against the type forces the elaborator
  # to build an n-deep plus-coproduct description, and conv walks that
  # plus-mu compound when unifying the ctor's codomain with the type.
  manyCtorDT = n:
    H.datatype "Big${toString n}"
      (builtins.genList (i: H.con "c${toString i}" [ ]) n);

  # β-distinct but equal-NF: `((λx:Nat. x) : Nat → Nat) 0`. The bare
  # lambda is checkable-only in the bidirectional kernel, so the app
  # head is wrapped in `ann` to pin a `Π(_:Nat).Nat` type the kernel
  # can infer; checking the application against `Nat` forces a β-step
  # inside the evaluator before conv can match the result.
  betaApp =
    let idAnn = H.ann (H.lam "x" H.nat (x: x))
                      (H.forall "_" H.nat (_: H.nat));
    in H.app idAnn H.zero;

in {
  # Minimal checkHoas: fixed-cost floor (elaborator + empty-ctx check)
  # against which deeper workloads can be read as delta.
  identical-shallow = (H.checkHoas H.nat H.zero).tag;

  # Deep desc-con chain of `Nat`. Checking walks a 5000-deep tree;
  # per-level conv compares the successor's payload against the
  # elaborated `Nat` description.
  identical-deep = (H.checkHoas H.nat (H.natLit 5000)).tag;

  # 20-constructor `datatype` whose description is a 20-deep
  # plus-coproduct. Checking the zeroth constructor against `.T`
  # forces conv to walk that plus-mu when unifying the ctor codomain.
  mu-heavy =
    let DT = manyCtorDT 20;
    in (H.checkHoas DT.T DT.c0).tag;

  # `Bool` is `μ ⊤ (plus (retI tt) (retI tt)) tt`. Every
  # `checkHoas H.bool …` traverses that plus-mu compound; a 10-deep
  # ann-wrap over `true_` fires 10 nested conv comparisons against
  # the compound. Depth-scaling beyond 10 does not add structural
  # signal — each ann level walks the same description.
  plus-heavy =
    let
      chain = builtins.foldl'
        (acc: _: H.ann acc H.bool)
        H.true_
        (builtins.genList (x: x) 10);
    in (H.checkHoas H.bool chain).tag;

  # β-distinct but NF-equal. checkHoas reduces the application before
  # conv matches the result against the declared `Nat`.
  beta-distinct = (H.checkHoas H.nat betaApp).tag;

  # α-equivalence via `refl : Eq (Nat → Nat) (λx.x) (λy.y)`. Checking
  # `refl` against an `Eq` type forces `conv d lhs rhs`, where both
  # sides elaborate to VLam values carrying the user-chosen binder
  # names ("x" vs "y") in their `.name` slot. Conv hits the
  # VLam-vs-VLam case and recurses under a fresh binder.
  alpha-equivalent =
    let
      piTy = H.forall "_" H.nat (_: H.nat);
      eqTy = H.eq piTy
        (H.lam "x" H.nat (x: x))
        (H.lam "y" H.nat (y: y));
    in (H.checkHoas eqTy H.refl).tag;
}
