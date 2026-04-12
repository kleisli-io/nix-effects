#!/usr/bin/env nix-unit
{
  pkgs ? import ./nixpkgs.nix { },
  ...
}:
let
  nix-effects = import ./. { lib = pkgs.lib; };
in
nix-effects.tests.nix-unit
