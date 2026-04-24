# At .envrc:
#   use nix
#
# Provides the test runner (nix-unit), the task launcher (just), and the
# full bench toolchain as top-level commands so contributors can iterate
# without `nix build .#bench-run && ./result/bin/…`.
#
# The bench derivations install their binaries as `nix-effects-bench-*`
# (the flake-package name stem). For shell use we also expose shorter
# `bench-*` aliases via a symlink shim, since the CONTRIBUTING docs,
# handoffs, and error messages all refer to the short names.
{
  pkgs ? import ./nixpkgs.nix { },
}:
let
  nix-effects = import ./. { inherit pkgs; };
  bench = nix-effects.bench.runner;

  bench-shims = pkgs.runCommand "nix-effects-bench-shims" { } ''
    mkdir -p $out/bin
    ln -s ${bench.run}/bin/nix-effects-bench-run                           $out/bin/bench-run
    ln -s ${bench.compare}/bin/nix-effects-bench-compare                   $out/bin/bench-compare
    ln -s ${bench.gate}/bin/nix-effects-bench-gate                         $out/bin/bench-gate
    ln -s ${bench.calibrate}/bin/nix-effects-bench-calibrate               $out/bin/bench-calibrate
    ln -s ${bench.open-regressions}/bin/nix-effects-bench-open-regressions $out/bin/bench-open-regressions
    ln -s ${bench.lint-workloads}/bin/nix-effects-bench-lint-workloads     $out/bin/bench-lint-workloads
  '';
in
pkgs.mkShell {
  buildInputs = [
    pkgs.nix-unit
    pkgs.just

    # Bench harness — both long (nix-effects-bench-*) and short (bench-*)
    # names are on PATH. See CONTRIBUTING.md §"Performance gate" for the
    # CLI surface and the gating contract.
    bench.run
    bench.compare
    bench.gate
    bench.calibrate
    bench.open-regressions
    bench.lint-workloads
    bench-shims
  ];
}
