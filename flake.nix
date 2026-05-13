{
  description = "Pure Nix effects, typed validation, verified boundaries, and description-backed DSLs";

  inputs = {
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
    nix-unit.url = "github:nix-community/nix-unit";
    nix-unit.inputs = {
      nixpkgs.follows = "nixpkgs";
      nix-github-actions.follows = "";
      treefmt-nix.follows = "";
    };
  };

  outputs = { self, nixpkgs, nix-unit, ... }:
    let
      nix-effects = import ./. { lib = nixpkgs.lib; };
      forAllSystems = nixpkgs.lib.genAttrs nixpkgs.lib.systems.flakeExposed;
    in {
      lib = nix-effects;

      # Test attrset for nix-unit: inline tests ({ expr; expected; }) and
      # integration tests (booleans wrapped as { expr; expected = true; }).
      tests = nix-effects.tests.nix-unit;

      packages = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          lib = nixpkgs.lib;
          # Per-module API markdown generated from extractDocs mk wrappers.
          apiDocsSrc = import ./book/gen { inherit pkgs lib nix-effects; };
          # bench runners need pkgs at import time to produce shell
          # derivations. Re-import the root with pkgs here so `bench.runner`
          # resolves to the non-null attrset.
          nix-effects-with-pkgs = import ./. { inherit pkgs lib; };
        in {
          # Raw generated API markdown (one .md per module).
          api-docs-src = apiDocsSrc;

          # Content for kleisli-docs (docs.kleisli.io):
          # nix build .#kleisli-docs-content && ls result/nix-effects/
          kleisli-docs-content = import ./book/gen/kleisli-docs.nix {
            inherit pkgs lib nix-effects;
          };

          # Bench harness. Binary stem is `nix-effects-bench-*`; the
          # `apps` outputs below alias these for `nix run .#bench-* -- …`.
          bench-run              = nix-effects-with-pkgs.bench.runner.run;
          bench-compare          = nix-effects-with-pkgs.bench.runner.compare;
          bench-gate             = nix-effects-with-pkgs.bench.runner.gate;
          bench-calibrate        = nix-effects-with-pkgs.bench.runner.calibrate;
          bench-open-regressions = nix-effects-with-pkgs.bench.runner.open-regressions;
          bench-lint-workloads   = nix-effects-with-pkgs.bench.runner.lint-workloads;
        });

      # `nix run .#bench-* -- <args>`. The wrapped binary embeds the
      # flake-locked Nix; alloc counters match the bench-gate baseline.
      apps = forAllSystems (system:
        let
          benchPkgs = self.packages.${system};
          mkApp = pkg: stem: {
            type = "app";
            program = "${pkg}/bin/nix-effects-bench-${stem}";
          };
        in {
          bench-run              = mkApp benchPkgs.bench-run              "run";
          bench-compare          = mkApp benchPkgs.bench-compare          "compare";
          bench-gate             = mkApp benchPkgs.bench-gate             "gate";
          bench-calibrate        = mkApp benchPkgs.bench-calibrate        "calibrate";
          bench-open-regressions = mkApp benchPkgs.bench-open-regressions "open-regressions";
          bench-lint-workloads   = mkApp benchPkgs.bench-lint-workloads   "lint-workloads";
        });

      checks = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          nix-unit-pkg = nix-unit.packages.${system}.default;
        in {
          default = pkgs.runCommand "nix-effects-tests" {
            nativeBuildInputs = [ nix-unit-pkg ];
          } ''
            export HOME="$(realpath .)"
            nix-unit --eval-store "$HOME" \
              --extra-experimental-features flakes \
              --override-input nixpkgs ${nixpkgs} \
              --override-input nix-unit ${nix-unit} \
              --flake ${self}#tests
            touch $out
          '';
        });
    };
}
