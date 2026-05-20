# Effects-layer workloads: interpreter, build simulator, synthetic stress.
{ fx }:
{
  interp = import ./interp.nix { inherit fx; };
  buildSim = import ./build-sim.nix { inherit fx; };
  stress = import ./stress.nix { inherit fx; };
  stateChain = import ./state-chain.nix { inherit fx; };

  # The full test-suite run, treated as a single end-to-end workload.
  tests = builtins.deepSeq fx.tests.nix-unit true;
}
