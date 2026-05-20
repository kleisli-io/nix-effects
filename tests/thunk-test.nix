# DerivationThunk integration tests
#
# Validates that the runtime carrier survives the trampoline's mandatory
# `builtins.deepSeq newState` (src/trampoline.nix:124) when handler state
# carries a self-referential derivation-shaped attrset. Without the carrier
# the trampoline would loop on the drv's cyclic structure and hang the
# evaluator (uncatchable by `tryEval`).
{ lib, fx }:

let
  inherit (fx) pure bind send run;
  inherit (fx.state) mkDerivationThunk forceDerivationThunk isDerivationThunk;

  # Self-referential drv-shaped attrset. Raw `deepSeq` on this loops; the
  # carrier shields it because closures are opaque to deepSeq.
  cyclicDrv = {
    type    = "derivation";
    name    = "cyclic";
    outPath = "/nix/store/cyclic-x";
    self    = cyclicDrv;
  };

  # Handler that accumulates carriers in state.packages — never raw drvs.
  registerHandler = {
    "demo.register" = { param, state }: {
      resume = null;
      state  = state // { packages = state.packages ++ [ param.package ]; };
    };
  };

  emit = drv: send "demo.register" { package = mkDerivationThunk drv; };

  # Chain three registrations of the cyclic drv.
  program = bind (emit cyclicDrv) (_:
            bind (emit cyclicDrv) (_:
            bind (emit cyclicDrv) (_:
            pure null)));

  result = run program registerHandler { packages = []; };

  # -- Test 1: trampoline run completes without infinite recursion --
  #
  # The success criterion is that the result is reachable at all; we use
  # `deepSeq result null` to force the entire value structure, which would
  # hang if any raw cyclic drv were threaded through state. Since
  # `result.state.packages` holds DerivationThunks (closures), deepSeq
  # stops at the lambda boundary and terminates.
  trampolineSurvivesCyclicDrv =
    (builtins.tryEval (builtins.deepSeq result null)).success;

  # -- Test 2: all three carriers survived end-to-end --
  threePackagesInState =
    builtins.length result.state.packages == 3;

  # -- Test 3: every stored value is a carrier, never a raw drv --
  allEntriesAreCarriers =
    lib.all isDerivationThunk result.state.packages;

  # -- Test 4: post-trampoline forcing recovers the original drv --
  recoveryReturnsOriginalDrv =
    let recovered = forceDerivationThunk (builtins.head result.state.packages);
    in recovered.outPath == "/nix/store/cyclic-x";

  # -- Test 5: round-trip identity through the trampoline --
  #
  # The drv that comes out is reference-equal to the one that went in. The
  # carrier never copies the drv; it only hides it behind a closure.
  roundTripIdentity =
    let recovered = forceDerivationThunk (builtins.head result.state.packages);
    in recovered == cyclicDrv;

  # -- Test 6: the effect-system validation rejects raw drvs against
  #            the DerivationThunk type, proving the type-system enforces
  #            the carrier discipline at the value-shape level --
  rawDrvRejectedByThunkType =
    !(fx.types.DerivationThunk.check cyclicDrv);

  # -- Test 7: the effect-system validation accepts carriers against
  #            the DerivationThunk type --
  carrierAcceptedByThunkType =
    fx.types.DerivationThunk.check (mkDerivationThunk cyclicDrv);

  # -- Test 8: carrier is rejected by the bare Derivation type
  #            (the two types are disjoint, no implicit subtyping) --
  carrierRejectedByDerivationType =
    !(fx.types.Derivation.check (mkDerivationThunk cyclicDrv));

in {
  inherit trampolineSurvivesCyclicDrv
          threePackagesInState
          allEntriesAreCarriers
          recoveryReturnsOriginalDrv
          roundTripIdentity
          rawDrvRejectedByThunkType
          carrierAcceptedByThunkType
          carrierRejectedByDerivationType;

  allPass = trampolineSurvivesCyclicDrv
         && threePackagesInState
         && allEntriesAreCarriers
         && recoveryReturnsOriginalDrv
         && roundTripIdentity
         && rawDrvRejectedByThunkType
         && carrierAcceptedByThunkType
         && carrierRejectedByDerivationType;
}
