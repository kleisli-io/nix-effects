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
{ lib ? (import <nixpkgs> { }).lib, pkgs ? null }:

let
  fx = import ../. { inherit lib pkgs; };

  benchLib = import ./lib { inherit lib; };
  workloads = import ./workloads { inherit fx; };
  meta = import ./workloads/meta.nix { };

  # Runners depend on pkgs (they're `writeShellApplication` derivations).
  # When the caller passes `pkgs = null` — the default for pure-evaluation
  # tests of workloads + measure + gate — `runner` is a null sentinel.
  runner = if pkgs == null then null
           else import ./runner { inherit lib pkgs; };
in
{
  inherit workloads meta runner;
  inherit (benchLib) measure gate format;
  tests = fx.tests.allPass;
}
