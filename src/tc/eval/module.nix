# fx.tc.eval — evaluator module head.
#
# Public export assembly for the evaluator. `self` is the disjoint-union
# fixpoint of `core.nix` and `desc.nix`; `partTests` is the aggregated
# test map from both parts.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.eval: pure kernel evaluator for `eval`/`evalF`/`instantiate` plus elimination helpers; zero effect-system imports, part of the TCB.";
  doc = ''
    # fx.tc.eval — Evaluator

    Pure evaluator: interprets kernel terms in an environment of
    values. Zero effect system imports — part of the trusted computing
    base (TCB).

    ## Core Functions

    - `eval : Env → Tm → Val` — evaluate with default fuel (10M steps)
    - `evalF : Int → Env → Tm → Val` — evaluate with explicit fuel budget
    - `instantiate : Closure → Val → Val` — apply a closure to an argument

    ## Elimination Helpers

    - `vApp : Val → Val → Val` — apply a function value (beta-reduces VLam, extends spine for VNe)
    - `vFst`, `vSnd` — pair projections
    - `vBootSumElim` — sum elimination
    - `vBootJ` — identity elimination (computes to base on VBootRefl)

    ## Trampolining

    Generated `desc-con` chains use `builtins.genericClosure` to flatten
    recursive structures iteratively, guaranteeing O(1) stack depth on
    deep generated recursive data.

    ## Fuel Mechanism

    Each `evalF` call decrements a fuel counter. When fuel reaches 0,
    evaluation throws `"normalization budget exceeded"`. This bounds
    total work and prevents unbounded computation in the Nix evaluator.
    Default budget: 10,000,000 steps.
  '';
  value = {
    inherit (self)
      eval evalF instantiate mkValueF forceVal forceAndPeelChainV effLayers
      vApp vFst vSnd vBootSumElim vBootJ
      vLiftF vLiftIntroF vLiftElimF
      vDescInd descView linearProfile
      sumPayloadTmView sumPayloadValView
      vInterpD vAllD vEverywhereD
      mkDescDescAppV;

    machine = api.namespace {
      description = "fx.tc.eval.machine: CEK abstract machine. `runMachineF` is the defunctionalized form of `evalF`; `runQuoteF` is the symmetric read-back driver consumed by `tc/quote.nix`.";
      value = {
        inherit (self) runMachineF runQuoteF runConvF;
      };
    };

    dispatch = api.namespace {
      description = "fx.tc.eval.dispatch: full kernel evaluator self-fixpoint. Consumed by overlay constructions (notably `tc/elaborate/eval-overlay.nix`) that need to build a meta-aware self-table replacing selected dispatch attrs while inheriting the rest.";
      value = self;
    };

    _internal = api.namespace {
      description = "fx.tc.eval._internal: cross-part evaluator helpers reachable from sibling parts via the self-fixpoint; not part of the stable consumer surface.";
      value = {
        inherit (self) mkCanonAppVF mkDescDescAppVF;
      };
    };
  };
  tests = partTests;
}
