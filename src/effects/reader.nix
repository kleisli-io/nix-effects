# nix-effects reader: Read-only environment effect
#
# Provides ask/asks operations for reading from a shared environment.
# The handler threads an immutable environment through the computation.
# Reader is the read-only restriction of state: no put, only get.
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  ask = mk {
    doc = ''
      Read the current environment.

      ask : Computation env
    '';
    value = send "ask" null;
    tests = {
      "ask-is-impure" = {
        expr = ask.value._tag;
        expected = "Impure";
      };
      "ask-effect-name" = {
        expr = ask.value.effect.name;
        expected = "ask";
      };
    };
  };

  asks = mk {
    doc = ''
      Read a projection of the environment.

      asks : (env -> a) -> Computation a
    '';
    value = f: bind (send "ask" null) (env: pure (f env));
    tests = {
      "asks-is-impure" = {
        expr = (asks.value (e: e.x))._tag;
        expected = "Impure";
      };
    };
  };

  local = mk {
    doc = ''
      Run a computation with a modified environment.
      Returns a new computation that transforms the environment
      before executing the inner computation.

      Since handlers are pure functions, local is implemented by
      wrapping the inner computation's ask effects with the modifier.
      In practice, use separate handler installation with the modified env.

      local : (env -> env) -> Computation a -> Computation a
    '';
    value = f: comp: bind (send "local" f) (_: comp);
    tests = {
      "local-is-impure" = {
        expr = (local.value (e: e) (pure 42))._tag;
        expected = "Impure";
      };
    };
  };

  handler = mk {
    doc = ''
      Standard reader handler. Interprets ask effects.
      The state IS the environment (immutable through the computation).

        handle { handlers = reader.handler; state = myEnv; } comp
    '';
    value = {
      ask = { state, ... }: { resume = state; inherit state; };
      local = { param, state }: { resume = null; state = param state; };
    };
    tests = {
      "ask-returns-env" = {
        expr = (handler.value.ask { param = null; state = { x = 42; }; }).resume;
        expected = { x = 42; };
      };
      "local-transforms-env" = {
        expr = (handler.value.local {
          param = e: e // { y = 1; };
          state = { x = 42; };
        }).state;
        expected = { x = 42; y = 1; };
      };
    };
  };

in mk {
  doc = "Read-only environment effect: ask/asks/local with standard handler.";
  value = {
    inherit ask asks local handler;
  };
}
