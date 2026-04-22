# Bench runners — `writeShellApplication` derivations that exercise
# workloads and write to `bench/history/`. The pure pieces (measurement,
# gating, formatting) live in `bench/lib/`; this tree holds only the
# impure drivers.
#
# Runners default their `--bench-dir` to `$PWD/bench`, so iterative dev
# does not require rebuilding the runner after every workload edit.
{ lib, pkgs }:

{
  run              = import ./run.nix              { inherit lib pkgs; };
  compare          = import ./compare.nix          { inherit lib pkgs; };
  gate             = import ./gate.nix             { inherit lib pkgs; };
  calibrate        = import ./calibrate.nix        { inherit lib pkgs; };
  open-regressions = import ./open-regressions.nix { inherit lib pkgs; };
}
