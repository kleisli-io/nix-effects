# nix-effects scope: Computation-scoped handlers via effect rotation
#
# Provides computation-scoped handler installation without polluting
# user-visible state. Built on fx.rotate (Kyo-style handler rotation).
#
#
# scope.provide  — install handlers for subtree, no state interaction (reader/val pattern)
# scope.val      — convenience: provide constant values as named effects
# scope.stateful — install handlers for subcomputation, preserving state around rotation
# scope.run      — run body with scoped handlers, hide scope state
# scope.runWith  — run body with scoped handlers, expose scope state
# scope.handlersFromAttrs — helper for creating handlers from Nix attrsets
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

  provide = mk {
    doc = ''
      Install handlers for a computation's dynamic extent without
      touching state. Unhandled effects rotate outward; outer handler
      state mutations survive unaffected.

      This is the reader/val handler pattern (Koka's `val`, Haskell's
      `runReader`, Scheme's `parameterize`) — use it when handlers are
      stateless (resume with a constant, pass state through).
      For handlers that need their own state, use scope.run or
      scope.stateful instead.

      ```
      scope.provide : handlers -> Computation a -> Computation a
      ```
    '';
    value = handlers: body:
      rotate { inherit handlers; return = value: _: value; } body;
    tests = {
      "provide-resolves-effect" = {
        expr =
          let
            comp = send "x" null;
            result = handle { handlers = {}; }
              (provide {
                x = { state, ... }: { resume = 42; inherit state; };
              } comp);
          in result.value;
        expected = 42;
      };
      "provide-rotates-unhandled" = {
        expr =
          let
            comp = send "outer" 7;
            result = handle {
              handlers.outer = { param, state }: { resume = param * 2; inherit state; };
            } (provide {
              inner = { state, ... }: { resume = 99; inherit state; };
            } comp);
          in result.value;
        expected = 14;
      };
      "provide-preserves-outer-state" = {
        expr =
          let
            comp = bind (send "count" null) (_: send "count" null);
            result = handle {
              handlers = {
                count = { param, state }: {
                  resume = null;
                  state = state // { n = (state.n or 0) + 1; };
                };
              };
              state = {};
            } (provide {
              x = { state, ... }: { resume = 42; inherit state; };
            } comp);
          in result.state.n;
        expected = 2;
      };
      "provide-deep-semantics" = {
        expr =
          let
            comp = bind (send "outer" null) (_: send "inner" null);
            result = handle {
              handlers.outer = { param, state }: {
                resume = send "inner" null;
                inherit state;
              };
            } (provide {
              inner = { state, ... }: { resume = 42; inherit state; };
            } comp);
          in result.value;
        expected = 42;
      };
      "provide-nested-shadow" = {
        expr =
          let
            comp = send "x" null;
            result = handle { handlers = {}; }
              (provide {
                x = { state, ... }: { resume = 1; inherit state; };
              } (provide {
                x = { state, ... }: { resume = 2; inherit state; };
              } comp));
          in result.value;
        expected = 2;
      };
      "provide-empty-handlers" = {
        expr =
          let
            comp = send "x" 21;
            result = handle {
              handlers.x = { param, state }: { resume = param * 2; inherit state; };
            } (provide {} comp);
          in result.value;
        expected = 42;
      };
      # Deep semantics through bind chains: scope.provide inside a handler
      # resume that is wrapped in fx.bind. The bind chain causes queue.append
      # which must preserve __rawResume for deep handler routing.
      "provide-deep-through-bind-chain" = {
        expr =
          let
            # Outer handler for "work" resumes with a bind chain containing scope.provide.
            # Inner scope shadows "probe" at root. "emit" rotates out, root handler
            # resumes with "probe" — must route back through inner scope.
            body = send "work" null;
            result = handle {
              handlers = {
                probe = { state, ... }: { resume = "root"; inherit state; };
                emit = { param, state }: {
                  resume = send "probe" null;
                  inherit state;
                };
                work = { param, state }: {
                  # bind chain wraps scope.provide — exercises queue.append path
                  resume = bind (pure null) (_:
                    provide {
                      probe = { state, ... }: { resume = "inner"; inherit state; };
                    } (send "emit" null));
                  inherit state;
                };
              };
            } body;
          in result.value;
        expected = "inner";
      };
    };
  };

  val = mk {
    doc = ''
      Provide constant values as named effect handlers for a
      computation's dynamic extent. Each key in the bindings attrset
      becomes an effect that resumes with the corresponding value.
      Built on scope.provide via handlersFromAttrs.

      Named after Koka's `val` effect handler. For the traditional
      single-environment reader (ask/asks/local), see fx.effects.reader.

      ```
      scope.val : AttrSet -> Computation a -> Computation a
      ```
    '';
    value = bindings: body:
      provide (handlersFromAttrs bindings) body;
    tests = {
      "val-provides-values" = {
        expr =
          let
            comp = bind (send "host" null) (h: pure h.name);
            result = handle { handlers = {}; }
              (val { host = { name = "igloo"; }; } comp);
          in result.value;
        expected = "igloo";
      };
      "val-composes" = {
        expr =
          let
            comp = bind (send "host" null) (h:
              bind (send "user" null) (u:
                pure "${h.name}-${u.name}"));
            result = handle { handlers = {}; }
              (val { host = { name = "igloo"; }; }
                (val { user = { name = "tux"; }; } comp));
          in result.value;
        expected = "igloo-tux";
      };
      "val-state-transparent" = {
        expr =
          let
            comp = bind (send "inc" 1) (_:
              bind (send "host" null) (h:
                bind (send "inc" 1) (_:
                  pure h.name)));
            result = handle {
              handlers = {
                inc = { param, state }: {
                  resume = null;
                  state = state // { n = (state.n or 0) + param; };
                };
              };
              state = {};
            } (val { host = { name = "igloo"; }; } comp);
          in { n = result.state.n; value = result.value; };
        expected = { n = 2; value = "igloo"; };
      };
      "val-nested-shadow" = {
        expr =
          let
            comp = send "x" null;
            result = handle { handlers = {}; }
              (val { x = 1; }
                (val { x = 2; } comp));
          in result.value;
        expected = 2;
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
    inherit provide val stateful run runWith handlersFromAttrs;
  };
}
