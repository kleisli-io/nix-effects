# At .envrc:
#   use nix
{
  pkgs ? import <nixpkgs> { },
}:
pkgs.mkShell { buildInputs = [ pkgs.nix-unit pkgs.just ]; }
