# Definitional law proofs for the descInterp kernel. Each law is
# discharged via `deepEqualDesc` on the post-`T.run` carriers.
{ lib, fx }:

let
  stateTests = import ./state.nix { inherit lib fx; };
  errorTests = import ./error.nix { inherit lib fx; };
  bindAssocTests = import ./bind-assoc.nix { inherit lib fx; };
  composedTests = import ./composed.nix { inherit lib fx; };

in
{
  state = stateTests;
  error = errorTests;
  bindAssoc = bindAssocTests;
  composed = composedTests;
}
