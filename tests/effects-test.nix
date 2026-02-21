# nix-effects integration tests for effect modules
#
# Tests effects running through the trampoline, demonstrating:
# - State: counter increment/read through handler
# - Error: strict throw vs collecting accumulation
# - TypeCheck: reusable handlers with the type system
# - Conditions: CL-style signal/restart lifecycle
# - Composition: multiple effects in one computation
{ lib, fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) state error typecheck conditions;
  inherit (fx) types;

  # -- State effect tests --

  stateCounterTest = {
    expr =
      let
        comp = bind state.get (n:
          bind (state.put (n + 1)) (_:
            bind state.get (n2:
              pure n2)));
        result = handle {
          handlers = state.handler;
          state = 0;
        } comp;
      in result.value;
    expected = 1;
  };

  stateModifyTest = {
    expr =
      let
        comp = bind (state.modify (n: n * 3)) (_:
          bind (state.modify (n: n + 2)) (_:
            state.get));
        result = handle {
          handlers = state.handler;
          state = 10;
        } comp;
      in result.value;
    expected = 32;  # (10 * 3) + 2
  };

  stateGetsTest = {
    expr =
      let
        comp = bind (state.put { x = 42; y = 99; }) (_:
          state.gets (s: s.x));
        result = handle {
          handlers = state.handler;
          state = null;
        } comp;
      in result.value;
    expected = 42;
  };

  stateFinalStateTest = {
    expr =
      let
        comp = bind (state.modify (n: n + 5)) (_:
          bind (state.modify (n: n * 2)) (_:
            pure "done"));
        result = handle {
          handlers = state.handler;
          state = 10;
        } comp;
      in result.state;
    expected = 30;  # (10 + 5) * 2
  };

  # -- Error effect tests --

  errorCollectingTest = {
    expr =
      let
        comp = bind (error.raiseWith "parser" "unexpected token") (_:
          bind (error.raiseWith "parser" "missing semicolon") (_:
            pure "ok"));
        result = handle {
          handlers = error.collecting;
          state = [];
        } comp;
      in builtins.length result.state;
    expected = 2;
  };

  errorContextTest = {
    expr =
      let
        comp = error.raiseWith "validator" "field required";
        result = handle {
          handlers = error.collecting;
          state = [];
        } comp;
      in (builtins.head result.state).context;
    expected = "validator";
  };

  # -- TypeCheck effect tests (bridges type system) --

  typecheckStrictPassesTest = {
    expr =
      let
        piT = types.Pi { domain = types.Int; codomain = _: types.Int; name = "double"; universe = 0; };
        comp = piT.checkAt (x: x * 2) 21;
        result = handle {
          handlers = typecheck.strict;
          state = null;
        } comp;
      in result.value;
    expected = 42;
  };

  typecheckCollectingErrorsTest = {
    expr =
      let
        piT = types.Pi { domain = types.Int; codomain = _: types.String; name = "bad"; universe = 0; };
        # Domain ok (21 is Int), codomain fails (42 is not String)
        comp = piT.checkAt (x: x * 2) 21;
        result = handle {
          handlers = typecheck.collecting;
          state = [];
        } comp;
      in builtins.length result.state;
    expected = 1;
  };

  typecheckLoggingAllChecksTest = {
    expr =
      let
        piT = types.Pi { domain = types.Int; codomain = _: types.Int; name = "double"; universe = 0; };
        comp = piT.checkAt (x: x * 2) 21;
        result = handle {
          handlers = typecheck.logging;
          state = [];
        } comp;
      in builtins.length result.state;
    expected = 2;  # domain check + codomain check
  };

  typecheckLoggingAllPassTest = {
    expr =
      let
        piT = types.Pi { domain = types.Int; codomain = _: types.Int; name = "double"; universe = 0; };
        comp = piT.checkAt (x: x * 2) 21;
        result = handle {
          handlers = typecheck.logging;
          state = [];
        } comp;
      in builtins.all (e: e.passed) result.state;
    expected = true;
  };

  # -- Conditions tests --

  conditionsSignalRestartTest = {
    expr =
      let
        safeDivide = a: b:
          if b == 0
          then bind (conditions.signal "division-by-zero" { inherit a b; } ["use-value" "return-zero"]) (response:
            if response.restart == "use-value"
            then pure response.value
            else pure 0)
          else pure (a / b);
        comp = safeDivide 10 0;
        result = handle {
          handlers = conditions.withRestart "division-by-zero" "use-value" 999;
          state = null;
        } comp;
      in result.value;
    expected = 999;
  };

  conditionsCollectTest = {
    expr =
      let
        comp = bind (conditions.signal "warning" { msg = "deprecated"; } []) (_:
          bind (conditions.signal "warning" { msg = "slow path"; } []) (_:
            pure "done"));
        result = handle {
          handlers = conditions.collectConditions;
          state = [];
        } comp;
      in builtins.length result.state;
    expected = 2;
  };

  conditionsIgnoreTest = {
    expr =
      let
        comp = bind (conditions.signal "noise" {} []) (_:
          pure 42);
        result = handle {
          handlers = conditions.ignore;
          state = null;
        } comp;
      in result.value;
    expected = 42;
  };

  # -- Composition tests: multiple effects via adapt --
  composedWithAdaptTest = {
    expr =
      let
        adaptedState = fx.adaptHandlers {
          get = s: s.counter;
          set = s: c: s // { counter = c; };
        } state.handler;

        adaptedError = fx.adaptHandlers {
          get = s: s.errors;
          set = s: e: s // { errors = e; };
        } error.collecting;

        comp = bind (state.modify (n: n + 1)) (_:
          bind (error.raiseWith "step2" "bad value") (_:
            bind (state.modify (n: n + 10)) (_:
              state.get)));

        result = handle {
          handlers = adaptedState // adaptedError;
          state = { counter = 0; errors = []; };
        } comp;
      in { value = result.value; errors = result.state.errors; counter = result.state.counter; };
    expected = {
      value = 11;  # 0 + 1 + 10
      errors = [{ message = "bad value"; context = "step2"; }];
      counter = 11;
    };
  };

  allTests = {
    inherit stateCounterTest stateModifyTest stateGetsTest stateFinalStateTest
            errorCollectingTest errorContextTest
            typecheckStrictPassesTest typecheckCollectingErrorsTest
            typecheckLoggingAllChecksTest typecheckLoggingAllPassTest
            conditionsSignalRestartTest conditionsCollectTest conditionsIgnoreTest
            composedWithAdaptTest;
  };

  results = builtins.mapAttrs (_: test:
    let actual = test.expr; in
    { inherit actual; expected = test.expected; pass = actual == test.expected; }
  ) allTests;

  failed = lib.filterAttrs (_: r: !r.pass) results;

in allTests // {
  allPass = (builtins.length (builtins.attrNames failed)) == 0;
}
