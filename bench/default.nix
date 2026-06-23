# nix-effects benchmark entry point.
#
# Layout:
#   workloads/   pure expressions, keyed by dotted path
#     effects/   interp, buildSim, stress
#     tc/        conv, quote, check, infer, elaborate, e2e
#     meta.nix   per-workload tier assignments
#   lib/         pure measurement + gate + format helpers
#   history/     named-run JSON + markdown outputs
#
# Usage (pure evaluation):
#   nix eval --file ./bench workloads.effects.interp.fib15
#   nix eval --file ./bench meta.lookup \"effects.interp.fib15\"
{ pkgs ? (import ../pins.nix).nixpkgs { }, lib ? pkgs.lib }:

let
  fx = import ../. { inherit lib pkgs; exposeInternals = true; };

  benchLib = import ./lib { inherit lib; };
  workloads = import ./workloads { inherit fx; };
  stepProbes = import ./step-probes.nix { inherit fx; };
  meta = import ./workloads/meta.nix { };

  runner = import ./runner { inherit lib pkgs; };
in
{
  inherit workloads meta runner stepProbes;
  inherit (benchLib) measure gate format;
  tests = builtins.deepSeq fx.tests.nix-unit true;
}
