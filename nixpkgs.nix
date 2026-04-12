# Imports pinned nixpkgs from flake.lock on non-flake environments
let
  json = builtins.fromJSON (builtins.readFile ./flake.lock);
  nixpkgs = with json.nodes.nixpkgs.locked; builtins.fetchTarball {
    url = url;
    sha256 = narHash;
  };
in import nixpkgs
