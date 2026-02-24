# nix-effects integration tests for linear resource tracking
#
# Tests the full lifecycle: acquire/consume/release through the trampoline,
# composition with state and typecheck effects via adaptHandlers, error
# paths, stress tests, and type system integration.
{ lib, fx }:

let
  inherit (fx) pure bind handle adaptHandlers;
  inherit (fx.effects) linear state typecheck;
  inherit (fx.types) mkType check Linear Graded;
  H = fx.types.hoas;

  # =========================================================================
  # BASIC LIFECYCLE
  # =========================================================================

  linearHappyPath = {
    expr =
      let
        comp = bind (linear.acquireLinear "secret") (token:
          bind (linear.consume token) (val:
            pure "got:${val}"));
      in (linear.run comp).value;
    expected = "got:secret";
  };

  linearMultiResource = {
    expr =
      let
        comp = bind (linear.acquireLinear "db") (t1:
          bind (linear.acquireLinear "key") (t2:
            bind (linear.consume t1) (v1:
              bind (linear.consume t2) (v2:
                pure "${v1}+${v2}"))));
      in (linear.run comp).value;
    expected = "db+key";
  };

  linearAffineRelease = {
    expr =
      let
        comp = bind (linear.acquireLinear "optional") (token:
          bind (linear.release token) (_:
            pure "dropped"));
      in (linear.run comp).value;
    expected = "dropped";
  };

  linearGradedExact = {
    expr =
      let
        comp = bind (linear.acquireExact "multi" 3) (token:
          bind (linear.consume token) (v1:
            bind (linear.consume token) (v2:
              bind (linear.consume token) (v3:
                pure "${v1}+${v2}+${v3}"))));
      in (linear.run comp).value;
    expected = "multi+multi+multi";
  };

  linearUnlimited = {
    expr =
      let
        comp = bind (linear.acquireUnlimited "free") (token:
          builtins.foldl'
            (acc: _: bind acc (_: linear.consume token))
            (pure null)
            (lib.range 1 20));
      in !((linear.run comp).value ? _tag);
    expected = true;
  };

  # =========================================================================
  # ERROR PATHS
  # =========================================================================

  linearLeakDetected = {
    expr =
      let
        comp = bind (linear.acquireLinear "leaked") (_token:
          pure "forgot");
        result = linear.run comp;
      in result.value._tag == "LinearityError"
         && result.value.error == "usage-mismatch";
    expected = true;
  };

  linearDoubleConsumeAborts = {
    expr =
      let
        comp = bind (linear.acquireLinear "once") (token:
          bind (linear.consume token) (_:
            bind (linear.consume token) (_:
              pure "unreachable")));
        result = linear.run comp;
      in result.value._tag == "LinearityError"
         && result.value.error == "exceeded-bound";
    expected = true;
  };

  linearConsumeAfterReleaseAborts = {
    expr =
      let
        comp = bind (linear.acquireLinear "x") (token:
          bind (linear.release token) (_:
            bind (linear.consume token) (_:
              pure "unreachable")));
      in (linear.run comp).value.error;
    expected = "consume-after-release";
  };

  linearDoubleReleaseAborts = {
    expr =
      let
        comp = bind (linear.acquireLinear "x") (token:
          bind (linear.release token) (_:
            bind (linear.release token) (_:
              pure "unreachable")));
      in (linear.run comp).value.error;
    expected = "double-release";
  };

  linearMultiLeakReportsAll = {
    expr =
      let
        comp = bind (linear.acquireLinear "leak-1") (_:
          bind (linear.acquireLinear "leak-2") (_:
            bind (linear.acquireLinear "ok") (t:
              bind (linear.consume t) (_:
                pure "partial"))));
        result = linear.run comp;
      in result.value._tag == "LinearityError"
         && builtins.length result.value.details == 2;
    expected = true;
  };

  linearGradedUnderuseDetected = {
    expr =
      let
        comp = bind (linear.acquireExact "need-3" 3) (token:
          bind (linear.consume token) (_:
            pure "only-used-once"));
        result = linear.run comp;
      in result.value.error == "usage-mismatch"
         && (builtins.head result.value.details).expected == 3
         && (builtins.head result.value.details).actual == 1;
    expected = true;
  };

  linearGradedOveruseAborts = {
    expr =
      let
        comp = bind (linear.acquireExact "max-2" 2) (token:
          bind (linear.consume token) (_:
            bind (linear.consume token) (_:
              bind (linear.consume token) (_:
                pure "unreachable"))));
        result = linear.run comp;
      in result.value.error == "exceeded-bound"
         && result.value.maxUses == 2
         && result.value.attempted == 3;
    expected = true;
  };

  # =========================================================================
  # COMPOSITION VIA adaptHandlers
  # =========================================================================

  linearLens = {
    get = s: s.linear;
    set = s: v: s // { linear = v; };
  };
  typecheckLens = {
    get = s: s.typeErrors;
    set = s: v: s // { typeErrors = v; };
  };
  appStateLens = {
    get = s: s.appState;
    set = s: v: s // { appState = v; };
  };

  composedHandlers =
    (adaptHandlers linearLens linear.handler)
    // (adaptHandlers typecheckLens typecheck.collecting)
    // (adaptHandlers appStateLens state.handler);

  composedInitialState = {
    linear = linear.initialState;
    typeErrors = [];
    appState = 0;
  };

  # Return clause that checks for linear leaks in composed state
  composedReturn = value: st:
    let
      leakResult = linear.return value st.linear;
    in {
      value = leakResult.value;
      state = st // { linear = leakResult.state; };
    };

  compositionThreeEffects = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        comp =
          bind (IntT.validate 42) (_:
          bind (linear.acquireLinear "api-key") (token:
          bind (linear.consume token) (keyVal:
          bind (state.put 100) (_:
          bind state.get (s:
            pure { key = keyVal; stateVal = s; })))));
        result = handle {
          return = composedReturn;
          handlers = composedHandlers;
          state = composedInitialState;
        } comp;
      in result.value.key == "api-key"
         && result.value.stateVal == 100
         && result.state.typeErrors == [];
    expected = true;
  };

  compositionTypeErrorPlusLeak = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        comp =
          bind (IntT.validate "not-int") (_:
          bind (linear.acquireLinear "leaked") (_:
            pure "done"));
        result = handle {
          return = composedReturn;
          handlers = composedHandlers;
          state = composedInitialState;
        } comp;
      in result.value._tag == "LinearityError"
         && builtins.length result.state.typeErrors == 1;
    expected = true;
  };

  compositionStatePreservation = {
    expr =
      let
        comp =
          bind (state.put 10) (_:
          bind (linear.acquireLinear "r1") (t1:
          bind (state.modify (n: n + 5)) (_:
          bind (linear.consume t1) (_:
          bind (state.modify (n: n * 2)) (_:
            state.get)))));
        result = handle {
          return = composedReturn;
          handlers = composedHandlers;
          state = composedInitialState;
        } comp;
      in result.value;
    expected = 30;  # (10 + 5) * 2
  };

  compositionAbortPreservesState = {
    expr =
      let
        comp =
          bind (state.put 42) (_:
          bind (linear.acquireLinear "thing") (token:
          bind (linear.consume token) (_:
          bind (linear.consume token) (_:  # abort: exceeded-bound
            pure "unreachable"))));
        result = handle {
          return = composedReturn;
          handlers = composedHandlers;
          state = composedInitialState;
        } comp;
      in result.value._tag == "LinearityError"
         && result.state.appState == 42;
    expected = true;
  };

  # =========================================================================
  # STRESS TESTS
  # =========================================================================

  stressDeepSeq100Pairs = {
    expr =
      let
        mkPair = i:
          bind (linear.acquireLinear "r-${toString i}") (token:
            linear.consume token);
        comp = builtins.foldl'
          (acc: i: bind acc (_: mkPair i))
          (pure null)
          (lib.range 0 99);
        result = linear.run comp;
      in !((result.value ? _tag))
         && builtins.length (builtins.attrNames result.state.resources) == 100;
    expected = true;
  };

  stressComposed50Cycles = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        mkCycle = i:
          bind (IntT.validate i) (_:
          bind (linear.acquireLinear "r-${toString i}") (token:
          bind (state.modify (n: n + 1)) (_:
          bind (linear.consume token) (_:
            pure null))));
        comp = builtins.foldl'
          (acc: i: bind acc (_: mkCycle i))
          (pure null)
          (lib.range 0 49);
        result = handle {
          return = composedReturn;
          handlers = composedHandlers;
          state = composedInitialState;
        } comp;
      in result.state.appState == 50
         && result.state.typeErrors == [];
    expected = true;
  };

  # =========================================================================
  # TYPE SYSTEM INTEGRATION
  # =========================================================================

  typeLinearCheckValid = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        LIntT = Linear IntT;
      in check LIntT { _linear = true; id = 0; resource = 42; };
    expected = true;
  };

  typeLinearCheckInvalid = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        LIntT = Linear IntT;
      in check LIntT { _linear = true; id = 0; resource = "not-int"; };
    expected = false;
  };

  typeLinearCheckNonToken = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
      in check (Linear IntT) 42;
    expected = false;
  };

  typeGradedName = {
    expr = (Graded { maxUses = 5; innerType = mkType { name = "String"; kernelType = H.string; }; }).name;
    expected = "Graded(5, String)";
  };

  # Type + effect round-trip: acquire produces tokens that pass type check
  typeLinearRoundTrip = {
    expr =
      let
        IntT = mkType { name = "Int"; kernelType = H.int_; };
        LIntT = Linear IntT;
        comp = bind (linear.acquireLinear 42) (token:
          bind (linear.consume token) (_:
            pure (check LIntT token)));
        result = linear.run comp;
      in result.value;
    expected = true;
  };

  # =========================================================================
  # MIXED GRADED RESOURCES
  # =========================================================================

  mixedGradedResources = {
    expr =
      let
        comp =
          bind (linear.acquireLinear "once") (t1:
          bind (linear.acquireExact "twice" 2) (t2:
          bind (linear.acquireUnlimited "many") (t3:
          bind (linear.consume t1) (_:
          bind (linear.consume t2) (_:
          bind (linear.consume t2) (_:
          bind (linear.consume t3) (_:
          bind (linear.consume t3) (_:
          bind (linear.consume t3) (_:
            pure "all-correct")))))))));
      in (linear.run comp).value;
    expected = "all-correct";
  };

  allPass =
    linearHappyPath.expr == linearHappyPath.expected
    && linearMultiResource.expr == linearMultiResource.expected
    && linearAffineRelease.expr == linearAffineRelease.expected
    && linearGradedExact.expr == linearGradedExact.expected
    && linearUnlimited.expr == linearUnlimited.expected
    && linearLeakDetected.expr == linearLeakDetected.expected
    && linearDoubleConsumeAborts.expr == linearDoubleConsumeAborts.expected
    && linearConsumeAfterReleaseAborts.expr == linearConsumeAfterReleaseAborts.expected
    && linearDoubleReleaseAborts.expr == linearDoubleReleaseAborts.expected
    && linearMultiLeakReportsAll.expr == linearMultiLeakReportsAll.expected
    && linearGradedUnderuseDetected.expr == linearGradedUnderuseDetected.expected
    && linearGradedOveruseAborts.expr == linearGradedOveruseAborts.expected
    && compositionThreeEffects.expr == compositionThreeEffects.expected
    && compositionTypeErrorPlusLeak.expr == compositionTypeErrorPlusLeak.expected
    && compositionStatePreservation.expr == compositionStatePreservation.expected
    && compositionAbortPreservesState.expr == compositionAbortPreservesState.expected
    && stressDeepSeq100Pairs.expr == stressDeepSeq100Pairs.expected
    && stressComposed50Cycles.expr == stressComposed50Cycles.expected
    && typeLinearCheckValid.expr == typeLinearCheckValid.expected
    && typeLinearCheckInvalid.expr == typeLinearCheckInvalid.expected
    && typeLinearCheckNonToken.expr == typeLinearCheckNonToken.expected
    && typeGradedName.expr == typeGradedName.expected
    && typeLinearRoundTrip.expr == typeLinearRoundTrip.expected
    && mixedGradedResources.expr == mixedGradedResources.expected;

in {
  inherit linearHappyPath linearMultiResource linearAffineRelease
          linearGradedExact linearUnlimited
          linearLeakDetected linearDoubleConsumeAborts
          linearConsumeAfterReleaseAborts linearDoubleReleaseAborts
          linearMultiLeakReportsAll
          linearGradedUnderuseDetected linearGradedOveruseAborts
          compositionThreeEffects compositionTypeErrorPlusLeak
          compositionStatePreservation compositionAbortPreservesState
          stressDeepSeq100Pairs stressComposed50Cycles
          typeLinearCheckValid typeLinearCheckInvalid typeLinearCheckNonToken
          typeGradedName typeLinearRoundTrip
          mixedGradedResources
          allPass;
}
