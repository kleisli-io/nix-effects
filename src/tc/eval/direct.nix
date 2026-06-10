# Depth-budgeted hybrid front end for the kernel evaluator.
#
# `evalHybridF` runs `mkValueF` (direct recursion — the same body the
# elaboration overlay instantiates) for structural terms, threading a
# depth budget through sub-evaluations via a memoized chain of
# self-tables. At budget exhaustion the remaining sub-problem enters
# `runMachineF`, so libnix stack depth stays O(budget) regardless of
# user-recursion depth. Precedent: `trampoline.nix` `applyQueue` /
# `effectRotate` (recursive to depth 500, iterative fallback beyond).
#
# The eliminator family (`desc-ind`, `interp-d`, `all-d`,
# `everywhere-d`) and chain construction (`desc-con`,
# `desc-con-chain`) always punt to the machine: the former preserves
# the VLazyDescIndAccLayer containment invariant (core.nix's
# eliminator helpers dispatch without a layer arm), the latter keeps
# chain-form Val construction and cert handling on the single
# maintained path. Running `desc-con` direct was measured and
# rejected: payloads whose evaluation reaches punted eliminators
# fragment one machine run into per-reduction entries, and each entry
# re-derives description values the single driver loop computes once
# and threads through frames (+120…+820‰ lookups on conv/elaboration-
# heavy workloads; cert-gating the split kills the wins too).
{ self, fx, ... }:

let
  val = fx.tc.value;
  inherit (val) vNeSnoc eApp envCons;
  T = fx.tc.term;
  H = fx.tc.hoas;

  directBudget = 128;

  # Tags that must evaluate through the machine regardless of budget.
  puntTags = {
    "desc-ind" = true;
    "interp-d" = true;
    "all-d" = true;
    "everywhere-d" = true;
    "desc-con" = true;
    "desc-con-chain" = true;
  };

  evalHybridAt = i: fuel: env: tm:
    if puntTags ? ${tm.tag} then self.runMachineF fuel env tm
    else self.mkValueF (tableAt i) fuel env tm;

  # tableAt i: dispatch table for sub-evaluations with i budget levels
  # remaining. Every level rebinds `evalF`/`instantiateF`/`vAppF` so
  # structural recursion AND beta descent decrement the budget; at
  # level 0 `evalF` is the machine, so both descent paths exhaust into
  # iterative evaluation. (`vAppF` must be rebound at level 0 too: the
  # fixpoint `vAppF` instantiates through `self.instantiateF`, which
  # re-enters at full budget — unbounded native recursion for app
  # chains deeper than the budget.) All other helpers stay
  # fixpoint-bound (they re-enter at full budget, like any external
  # caller).
  tableAt = i: builtins.elemAt tables i;
  tables = builtins.genList mkTable (directBudget + 1);
  mkTable = i:
    let
      s = self // {
        evalF = if i == 0 then self.runMachineF else evalHybridAt (i - 1);
        instantiateF = fuel: cl: arg:
          s.evalF fuel (envCons arg cl.env) cl.body;
        vAppF = fuel: fn0: arg:
          let fn = self.forceVal fn0; in
          if fn.tag == "VDescViewFn" then self.applyDescViewFnByKindF fuel fn arg
          else if fn.tag == "VLam" then s.instantiateF fuel fn.closure arg
          else if fn.tag == "VNe" then vNeSnoc fn (eApp arg)
          else throw "tc: vApp on non-function (tag=${fn.tag})";
      };
    in
    s;

  evalHybridF = evalHybridAt directBudget;

  encRet = H.elab (H.retI H.unit 0 H.tt);
  xUnit = T.mkLam "_" T.mkUnit T.mkUnit;

  # Elaborated `cons tt (cons tt … nil) : listOf unit` — a linear
  # desc-con chain of depth n with per-layer certs.
  consChainTm = n:
    H.elab (H.ann
      (builtins.foldl' (acc: _: H.cons H.tt acc) H.nil
        (builtins.genList (i: i) n))
      (H.listOf H.unit));

in
{
  scope = {
    inherit evalHybridF;
  };

  tests = {
    "hybrid-eval-tt" = {
      expr = (evalHybridF self.defaultFuel [ ] T.mkTt).tag;
      expected = "VTt";
    };
    "hybrid-eval-beta" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt)).tag;
      expected = "VTt";
    };

    # Punt tag: an `interp-d` Tm routes to the machine and lands the
    # same value the machine computes (cf. `desc.nix` "vInterpD-ret").
    "hybrid-eval-punt-interp-d" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (T.mkInterpD T.mkLevelZero T.mkUnit encRet xUnit T.mkTt)).tag;
      expected = "VBootEq";
    };

    # Structural descent deeper than the budget must hand off to the
    # machine instead of growing the libnix stack.
    "hybrid-eval-let-chain-10000" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkLet "x" T.mkUnit T.mkTt acc)
          (T.mkVar 0)
          (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };

    # Beta descent must decrement the budget through
    # `vAppF`/`instantiateF` — re-entering at full budget would
    # overflow the stack long before depth 10000.
    "hybrid-eval-beta-chain-10000" = {
      expr = (evalHybridF self.defaultFuel [ ]
        (builtins.foldl' (acc: _: T.mkApp (T.mkLam "x" T.mkUnit acc) T.mkTt)
          T.mkTt
          (builtins.genList (i: i) 10000))).tag;
      expected = "VTt";
    };

    # desc-con through evalHybridF dispatch lands the chain-form Val.
    "hybrid-eval-desc-con-chain-form" = {
      expr =
        let v = evalHybridF self.defaultFuel [ ] (consChainTm 5); in
        { shape = v._shape or null; layers = builtins.length (self.effLayers v); };
      expected = { shape = "linearChain"; layers = 5; };
    };

    # evalHybridF dispatch and a bare machine run must agree
    # definitionally on desc-con chains.
    "hybrid-eval-desc-con-machine-parity" = {
      expr =
        let
          tm = consChainTm 5;
          vH = evalHybridF self.defaultFuel [ ] tm;
          vM = self.runMachineF self.defaultFuel [ ] tm;
        in
        fx.tc.conv.conv 0 vH vM;
      expected = true;
    };

    # The chain peel is genericClosure-iterative — depth must not
    # consume native stack.
    "hybrid-eval-desc-con-chain-10000" = {
      expr =
        builtins.length
          (self.effLayers (evalHybridF self.defaultFuel [ ] (consChainTm 10000)));
      expected = 10000;
    };
  };
}
