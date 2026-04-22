# Build simulator benchmarks — effect-based build planner over dependency graphs.
#
# `linear*`, `wide*`, `diamond*`, `tree*`, `mixed_*` — graph shape at scale N.
# `fail_*` — fail-fast semantics; capture the error string, not the value.
{ fx }:

let
  buildSim = import ../../../apps/build-sim { inherit fx; };
in {
  linear50  = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear50).value;
  linear100 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear100).value;
  linear200 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear200).value;
  linear500 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear500).value;

  wide50  = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide50).value;
  wide100 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide100).value;
  wide200 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide200).value;
  wide500 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide500).value;

  diamond5  = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond5).value;
  diamond8  = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond8).value;
  diamond10 = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond10).value;

  tree5 = (buildSim.evalQuiet buildSim.graphs.benchmarks.tree5).value;
  tree8 = (buildSim.evalQuiet buildSim.graphs.benchmarks.tree8).value;

  mixed_small  = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_small).value;
  mixed_medium = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_medium).value;
  mixed_large  = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_large).value;

  fail_early = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_early).error or "no error";
  fail_mid   = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_mid).error or "no error";
  fail_late  = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_late).error or "no error";
}
