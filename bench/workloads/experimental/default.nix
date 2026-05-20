{ fx }:
{
  descInterp = {
    bindChain = import ./desc-interp-bind-chain-100000.nix { inherit fx; };
    stateChain = import ./desc-interp-state-chain.nix { inherit fx; };
  };
}
