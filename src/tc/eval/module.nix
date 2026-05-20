# fx.tc.eval — evaluator module head.
#
# Public export assembly for the evaluator. `self` is the disjoint-union
# fixpoint of `core.nix` and `desc.nix`; `partTests` is the aggregated
# test map from both parts.
{ self, partTests, partDocs, api, ... }:

api.mkModule {
  inherit partDocs;
  description = "fx.tc.eval: pure kernel evaluator (kernel-spec §4, §9) — `eval`/`evalF`/`instantiate` plus elimination helpers; zero effect-system imports, part of the TCB.";
  doc = ''
    # fx.tc.eval — Evaluator

    Pure evaluator: interprets kernel terms in an environment of
    values. Zero effect system imports — part of the trusted computing
    base (TCB).

    Spec reference: kernel-spec.md §4, §9.

    ## Core Functions

    - `eval : Env → Tm → Val` — evaluate with default fuel (10M steps)
    - `evalF : Int → Env → Tm → Val` — evaluate with explicit fuel budget
    - `instantiate : Closure → Val → Val` — apply a closure to an argument

    ## Elimination Helpers

    - `vApp : Val → Val → Val` — apply a function value (beta-reduces VLam, extends spine for VNe)
    - `vFst`, `vSnd` — pair projections
    - `vBootSumElim` — sum elimination
    - `vBootJ` — identity elimination (computes to base on VBootRefl)

    ## Trampolining (§11.3)

    Generated `desc-con` chains use `builtins.genericClosure` to flatten
    recursive structures iteratively, guaranteeing O(1) stack depth on
    deep generated recursive data.

    ## Fuel Mechanism (§9)

    Each `evalF` call decrements a fuel counter. When fuel reaches 0,
    evaluation throws `"normalization budget exceeded"`. This bounds
    total work and prevents unbounded computation in the Nix evaluator.
    Default budget: 10,000,000 steps.
  '';
  value = {
    inherit (self)
      eval evalF instantiate
      vApp vFst vSnd vBootSumElim vBootJ
      vLiftF vLiftIntroF vLiftElimF
      vDescInd descView linearProfile
      sumPayloadTmView sumPayloadValView
      vInterpD vAllD vEverywhereD
      mkDescDescAppV mkDescDescAppVF;

    _internal = api.mk {
      description = "fx.tc.eval._internal: cross-part evaluator helpers reachable from sibling parts via the self-fixpoint; not part of the stable consumer surface.";
      value = { inherit (self) mkCanonAppVF; };
    };
  };
  tests = partTests;
}
