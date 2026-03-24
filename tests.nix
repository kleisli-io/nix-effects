#!/usr/bin/env nix-unit
{
  pkgs ? import <nixpkgs> { },
  ...
}:
let
  nix-effects = import ./. { lib = pkgs.lib; };
in
nix-effects.tests.nix-unit
