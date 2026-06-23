# Thunk integration tests
#
# Validates that the runtime carrier survives the trampoline's mandatory
# `builtins.deepSeq newState` (src/trampoline.nix:124) when handler state
# carries a self-referential derivation-shaped attrset. Without the carrier
# the trampoline would loop on the drv's cyclic structure and hang the
# evaluator (uncatchable by `tryEval`).
{ lib, fx }:

let
  inherit (fx) pure bind send run;
  inherit (fx.state) mkThunk forceThunk isThunk;

  H = fx.types.hoas;
  ThunkDrvTy = H.thunk H.derivation;

  # Self-referential drv-shaped attrset. Raw `deepSeq` on this loops; the
  # carrier shields it because closures are opaque to deepSeq.
  cyclicDrv = {
    type = "derivation";
    name = "cyclic";
    outPath = "/nix/store/cyclic-x";
    self = cyclicDrv;
  };

  # Handler that accumulates carriers in state.packages — never raw drvs.
  registerHandler = {
    "demo.register" = { param, state }: {
      resume = null;
      state = state // { packages = state.packages ++ [ param.package ]; };
    };
  };

  emit = drv: send "demo.register" { package = mkThunk drv; };

  # Chain three registrations of the cyclic drv.
  program = bind (emit cyclicDrv) (_:
    bind (emit cyclicDrv) (_:
      bind (emit cyclicDrv) (_:
        pure null)));

  result = run program registerHandler { packages = [ ]; };

  # trampoline run completes; deepSeq stops at the lambda boundary
  trampolineSurvivesCyclicDrv =
    (builtins.tryEval (builtins.deepSeq result null)).success;

  # all three carriers survived end-to-end
  threePackagesInState =
    builtins.length result.state.packages == 3;

  # every stored value is a carrier, never a raw drv
  allEntriesAreCarriers =
    lib.all isThunk result.state.packages;

  # post-trampoline forcing recovers the original drv
  recoveryReturnsOriginalDrv =
    let recovered = forceThunk (builtins.head result.state.packages);
    in recovered.outPath == "/nix/store/cyclic-x";

  # round-trip identity: the drv out is reference-equal to the one in; the carrier never copies
  roundTripIdentity =
    let recovered = forceThunk (builtins.head result.state.packages);
    in recovered == cyclicDrv;

  # kernel walker rejects raw drvs against the `Thunk Derivation` shape
  rawDrvRejectedByThunkType =
    (fx.types.validateValue [ ] ThunkDrvTy cyclicDrv) != [ ];

  # kernel walker accepts carriers against the `Thunk Derivation` shape
  carrierAcceptedByThunkType =
    (fx.types.validateValue [ ] ThunkDrvTy (mkThunk cyclicDrv)) == [ ];

  # carrier is rejected by the bare Derivation type (the two types are disjoint, no implicit subtyping)
  carrierRejectedByDerivationType =
    !(fx.types.Derivation.check (mkThunk cyclicDrv));

in
{
  inherit trampolineSurvivesCyclicDrv
    threePackagesInState
    allEntriesAreCarriers
    recoveryReturnsOriginalDrv
    roundTripIdentity
    rawDrvRejectedByThunkType
    carrierAcceptedByThunkType
    carrierRejectedByDerivationType;
}
