# CEK step-count work-axis probes: exact machine-transition counts of the
# eval-depth-scaling terms (`runMachineCountedF`) and conv goal counts on
# structural value chains (`runConvCountedF`) at two depths. gate.nix stepAxis
# checks each slope against budgets.toml [stepSlopes].
#
# Conv probes use value chains, not the alloc conv workload's natLit terms:
# VDescCon chains are not cPeel arms, so the machine sees them as one base
# goal (count flat in n). The two chains exercise distinct cPeel arms — VPair
# (one sibling goal per layer) and VBootInl (two).
{ fx }:
let
  terms = import ./workloads/tc/eval-depth-terms.nix { inherit fx; };
  V = fx.src.tc.value;
  runCounted = fx.src.tc.eval.machine.runMachineCountedF;
  runConvCounted = fx.src.tc.eval.machine.runConvCountedF;

  # Any non-exhausting budget yields the same count: steps = startFuel − finalFuel.
  probeFuel = 10000000;
  at = n: tm: { inherit n; steps = (runCounted probeFuel [ ] tm).steps; };

  convAt = n: v: { inherit n; steps = (runConvCounted probeFuel 0 v v).steps; };
  pairChain = n: builtins.foldl' (acc: _: V.vPair V.vTt acc) V.vTt (builtins.genList (i: i) n);
  inlChain = n: builtins.foldl' (acc: _: V.vBootInl V.vUnit V.vUnit acc) V.vBootRefl (builtins.genList (i: i) n);
in
{
  "tc.vAppF" = {
    lo = at 1000 (terms.vAppElab 1000);
    hi = at 5000 (terms.vAppElab 5000);
  };
  "tc.descInd" = {
    lo = at 1000 (terms.descIndElab 1000);
    hi = at 5000 (terms.descIndElab 5000);
  };
  "tc.convPair" = {
    lo = convAt 1000 (pairChain 1000);
    hi = convAt 5000 (pairChain 5000);
  };
  "tc.convInl" = {
    lo = convAt 1000 (inlChain 1000);
    hi = convAt 5000 (inlChain 5000);
  };
}
