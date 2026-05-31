# Pinned dependencies for non-flake (direct-import) builds.
#   nixpkgs  — resolved from flake.lock so flake and non-flake paths agree.
#   nix-unit — 2.34.0, built against nixComponents_2_34 (matches nix-unit's flake).
let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  fetchNode = node:
    let l = lock.nodes.${node}.locked;
    in builtins.fetchTarball { inherit (l) url; sha256 = l.narHash; };
in
{
  nixpkgs = import (fetchNode "nixpkgs");

  nix-unit = pkgs:
    pkgs.callPackage
      (builtins.fetchTarball {
        url = "https://github.com/nix-community/nix-unit/archive/c688955bf83c2bc66717186e0979656d812c057a.tar.gz";
        sha256 = "0m1p27lyncfwx1jcb1bym9i8xjjlx0xg2wssv7759x6221fd35xx";
      })
      { nixComponents = pkgs.nixVersions.nixComponents_2_34; };
}
