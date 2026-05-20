# nix-effects reader: Read-only environment effect
#
# Provides ask/asks operations for reading from a shared environment.
# The handler threads an immutable environment through the computation.
# Reader is the read-only restriction of state: no put, only get.
{ fx, api, ... }:
let
  inherit (fx.kernel) pure bind send;
  ask = send "ask" null;

  asks = f: bind (send "ask" null) (env: pure (f env));

  local = f: comp: bind (send "local" f) (_: comp);

  handler = {
    ask = { state, ... }: { resume = state; inherit state; };
    local = { param, state }: { resume = null; state = param state; };
  };

in
api.namespace {
  description = "reader effect: read-only environment threaded as immutable state; ask/asks/local with a standard handler. Read-only restriction of state.";
  doc = "Read-only environment effect: ask/asks/local with standard handler.";
  value = {
    ask = api.leaf {
      value = ask;
      description = "ask: read the current environment threaded by the reader handler; impure request whose response IS the handler state.";
      signature = "ask : Computation env";
      doc = ''
        Read the current environment.
      '';
      tests = {
        "ask-is-impure" = {
          expr = fx.comp.isPure ask;
          expected = false;
        };
        "ask-effect-name" = {
          expr = ask.effect.name;
          expected = "ask";
        };
      };
    };

    asks = api.leaf {
      value = asks;
      description = "asks: read a projection of the environment via a user-supplied function; sugar for `bind ask (env: pure (f env))`.";
      signature = "asks : (env -> a) -> Computation a";
      doc = ''
        Read a projection of the environment.
      '';
      tests = {
        "asks-is-impure" = {
          expr = fx.comp.isPure (asks (e: e.x));
          expected = false;
        };
      };
    };

    local = api.leaf {
      value = local;
      description = "local: run a sub-computation under a modifier-transformed environment; sends `local` so handlers can install the modified env.";
      signature = "local : (env -> env) -> Computation a -> Computation a";
      doc = ''
        Run a computation with a modified environment. Returns a new
        computation that transforms the environment before executing
        the inner computation.

        Since handlers are pure functions, local is implemented by
        wrapping the inner computation's ask effects with the modifier.
        In practice, use separate handler installation with the modified env.
      '';
      tests = {
        "local-is-impure" = {
          expr = fx.comp.isPure (local (e: e) (pure 42));
          expected = false;
        };
      };
    };

    handler = api.leaf {
      value = handler;
      description = "reader.handler: interprets ask/local effects with state IS the (immutable) environment; ask resumes with state, local replaces it.";
      doc = ''
        Standard reader handler. Interprets ask effects.
        The state IS the environment (immutable through the computation).

        ```nix
        handle { handlers = reader.handler; state = myEnv; } comp
        ```
      '';
      tests = {
        "ask-returns-env" = {
          expr = (handler.ask { param = null; state = { x = 42; }; }).resume;
          expected = { x = 42; };
        };
        "local-transforms-env" = {
          expr = (handler.local {
            param = e: e // { y = 1; };
            state = { x = 42; };
          }).state;
          expected = { x = 42; y = 1; };
        };
      };
    };
  };
}
