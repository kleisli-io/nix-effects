# nix-effects scope: Computation-scoped handlers via effect rotation
#
# Provides computation-scoped handler installation without polluting
# user-visible state. Built on fx.rotate (Kyo-style handler rotation).
#
#
# scope.stateful - Install handlers for subcomputation, preserving state around rotation.
# scope.run    — run body with scoped handlers, hide scope state
# scope.runWith — run body with scoped handlers, expose scope state
# scope.handlersFromAttrs - helper for creating handlers from Nix attrsets
{ fx, api, lib, ... }:

let
  inherit (api) mk;
  inherit (fx.kernel) pure bind send;
  inherit (fx.trampoline) rotate handle;
  inherit (fx.effects) state;

  isHandler = f: lib.isFunction f && (lib.intersectAttrs { state = 1; param = 1; } (lib.functionArgs f)) != { };

  handlersFromAttrs = mk {
    doc = ''
    Helper to transform an attrset into named handlers.

    If attrValue is a function `{ param, state }` it is used directly as handler;
    If attrValue is a function, resume is `f param` and preserves state;
    Otherwise a constant handler always resumes with attrValue, preserving state.
    '';
    value = 
      lib.mapAttrs (name: value: 
      if isHandler value then value
      else if lib.isFunction value then { param, state }: { inherit state; resume = value param; }
      else { state, ... }: { inherit state; resume = value; });
    tests = {
      "preserves-handlers" = {
        expr = (handlersFromAttrs { foo = { param, state }: 22; }).foo { param = 1; state = 2; };
        expected = 22;
      };
      "constant" = {
        expr = (handlersFromAttrs { foo = 22; }).foo { param = 1; state = 2; };
        expected.resume = 22;
        expected.state = 2;
      };
      "function" = {
        expr = (handlersFromAttrs { foo = n: n * 2; }).foo { param = 11; state = 2; };
        expected.resume = 22;
        expected.state = 2;
      };
    };
  };


  stateful = mk {
    doc = ''
    Run a computation with scoped handlers while preserving
    state around effect rotation.

    ```
    scope : handlers -> Computation a -> Computation a
    ```
    '';

    value = handlers: body:
      state.update (state: rotate { inherit handlers state; } body);

    tests = {
      "preserves-state-around" = {
        expr = handle {
            handlers = state.handler;
            state = 11;
          } (stateful {
            foo = { param, state }: {
              state = state * 2;
              resume = state * 3;
            };
         } (send "foo" null));
        expected.state = 22;
        expected.value = 33;
      };
    };
  };

  run = mk {
    doc = ''
      Run a computation with scoped handlers. Effects matching `handlers`
      are handled inside the scope. Unknown effects rotate outward.
      The scope's internal state is hidden — caller sees only the body's value.

      ```
      scope.run : { handlers, state? } -> Computation a -> Computation a
      ```
    '';
    value = {
      handlers,
      state ? null,
    }:
      rotate {
        inherit handlers state;
        return = value: _state: value;
      };
    tests = {
      "scoped-handler-returns-value" = {
        expr =
          let
            comp = send "x" null;
            scoped = run {
              handlers.x = { state, ... }: { resume = 42; inherit state; };
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = 42;
      };
      "scope-hides-internal-state" = {
        expr =
          let
            comp = bind (send "inc" 1) (_: send "inc" 1);
            scoped = run {
              handlers.inc = { param, state }: { resume = null; state = state + param; };
              state = 0;
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = null;
      };
    };
  };

  runWith = mk {
    doc = ''
      Like scope.run but exposes the scope's final state alongside the value.

      ```
      scope.runWith : { handlers, state? } -> Computation a -> Computation { value, state }
      ```
    '';
    value = rotate;
    tests = {
      "runWith-exposes-state" = {
        expr =
          let
            comp = bind (send "inc" 1) (_: send "inc" 1);
            scoped = runWith {
              handlers.inc = { param, state }: { resume = null; state = state + param; };
              state = 0;
            } comp;
            result = handle { handlers = {}; } scoped;
          in result.value.state;
        expected = 2;
      };
    };
  };


in mk {
  doc = "Computation-scoped handlers via effect rotation.";
  value = { 
    inherit stateful run runWith handlersFromAttrs; 
  };
}
