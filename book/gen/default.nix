# nix-effects API doc generator
#
# Produces a linkFarm of per-module markdown files from extractDocs.
{ pkgs, lib, nix-effects }:

let
  docsLib =
    if nix-effects ? docs
    then nix-effects.docs
    else import ../../src/docs.nix { api = import ../../src/api.nix { inherit lib; }; inherit lib; };
in
docsLib.mkApiDocsLinkFarm {
  inherit pkgs;
  name = "nix-effects-api-docs";
  docs = nix-effects.extractDocs;
}
