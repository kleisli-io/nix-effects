{
  description = "A type-checking kernel, algebraic effects, and dependent types in pure Nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nix-unit.url = "github:nix-community/nix-unit";
    nix-unit.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, nix-unit, ... }:
    let
      nix-effects = import ./. { lib = nixpkgs.lib; };
      forAllSystems = nixpkgs.lib.genAttrs
        [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
    in {
      lib = nix-effects;

      # Test attrset for nix-unit: inline tests ({ expr; expected; }) and
      # integration tests (booleans wrapped as { expr; expected = true; }).
      tests = nix-effects.tests.nix-unit;

      # Showcase:
      #   nix build .#api-server  — valid config, proof-gated derivation builds
      #
      # To see the proof rejection for an invalid config:
      #   nix eval .#insecure-public  — fails: public bind + HTTP violates policy
      # (Not exposed as a package because it intentionally fails at eval time.)
      packages = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          lib = nixpkgs.lib;
          showcase = import ./examples/typed-derivation.nix {
            fx = nix-effects; inherit pkgs;
          };
          # Per-module API markdown generated from extractDocs mk wrappers.
          apiDocsSrc = import ./book/gen { inherit pkgs lib nix-effects; };
        in {
          inherit (showcase) api-server;

          # Raw generated API markdown (one .md per module).
          api-docs-src = apiDocsSrc;

          # Content for kleisli-docs (docs.kleisli.io):
          # nix build .#kleisli-docs-content && ls result/nix-effects/
          kleisli-docs-content = import ./book/gen/kleisli-docs.nix {
            inherit pkgs lib nix-effects;
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
