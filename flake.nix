{
  description = "A freer-monad effect layer for pure Nix, with a dependent type checker built on top of it";

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
          bench = import ./bench { inherit lib pkgs; };
          # Per-module API markdown generated from extractDocs mk wrappers.
          apiDocsSrc = import ./book/gen { inherit pkgs lib nix-effects; };
        in {
          # Raw generated API markdown (one .md per module).
          api-docs-src = apiDocsSrc;

          # Content for kleisli-docs (docs.kleisli.io):
          # nix build .#kleisli-docs-content && ls result/nix-effects/
          kleisli-docs-content = import ./book/gen/kleisli-docs.nix {
            inherit pkgs lib nix-effects;
          };

          # Benchmark runner and comparison tool
          bench = bench.run;
          bench-compare = bench.compare;
        });

      apps = forAllSystems (system: {
        bench = {
          type = "app";
          program = "${self.packages.${system}.bench}/bin/nix-effects-bench";
        };
        bench-compare = {
          type = "app";
          program = "${self.packages.${system}.bench-compare}/bin/nix-effects-bench-compare";
        };
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
