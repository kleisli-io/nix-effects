{ lib, fx }:

let
  stateTests    = import ./effects/state-test.nix    { inherit lib fx; };
  errorTests    = import ./effects/error-test.nix    { inherit lib fx; };
  composedTests = import ./effects/composed-test.nix { inherit lib fx; };

in {
  effects = {
    state    = stateTests;
    error    = errorTests;
    composed = composedTests;
  };

  allPass = stateTests.allPass && errorTests.allPass && composedTests.allPass;
}
