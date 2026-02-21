# nix-effects state: Mutable state effect
#
# The classic algebraic effect: get/put/modify on a single state value.
# Handler interprets these as state threading through the trampoline.
#
# Operations return Computation values (freer monad suspended at effects).
# The handler runs inside trampoline.handle and manages the state.
#
# References:
#   Plotkin & Power (2002) "Notions of Computation Determine Monads"
#   Kiselyov & Ishii (2015) "Freer Monads, More Extensible Effects"
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  get = mk {
    doc = ''
      Read the current state. Returns a Computation that, when handled,
      yields the current state value.

      get : Computation s
    '';
    value = send "get" null;
    tests = {
      "get-is-impure" = {
        expr = get.value._tag;
        expected = "Impure";
      };
      "get-effect-name" = {
        expr = get.value.effect.name;
        expected = "get";
      };
    };
  };

  put = mk {
    doc = ''
      Replace the current state. Returns a Computation that, when handled,
      sets the state to the given value and returns null.

      put : s -> Computation null
    '';
    value = s: send "put" s;
    tests = {
      "put-is-impure" = {
        expr = (put.value 42)._tag;
        expected = "Impure";
      };
      "put-carries-value" = {
        expr = (put.value 42).effect.param;
        expected = 42;
      };
    };
  };

  modify = mk {
    doc = ''
      Apply a function to the current state. Returns a Computation that,
      when handled, transforms the state via f and returns null.

      modify : (s -> s) -> Computation null
    '';
    value = f: send "modify" f;
    tests = {
      "modify-is-impure" = {
        expr = (modify.value (x: x + 1))._tag;
        expected = "Impure";
      };
    };
  };

  gets = mk {
    doc = ''
      Read a projection of the current state.

      gets : (s -> a) -> Computation a
    '';
    value = f: bind (send "get" null) (s: pure (f s));
    tests = {
      "gets-is-impure" = {
        expr = (gets.value (s: s.x))._tag;
        expected = "Impure";
      };
    };
  };

  handler = mk {
    doc = ''
      Standard state handler. Interprets get/put/modify effects.
      Use with trampoline.handle:

        handle { handlers = state.handler; state = initialState; } comp

      get: returns current state as value
      put: replaces state with param, returns null
      modify: applies param (a function) to state, returns null
    '';
    value = {
      get = { state, ... }: { resume = state; inherit state; };
      put = { param, ... }: { resume = null; state = param; };
      modify = { param, state }: { resume = null; state = param state; };
    };
    tests = {
      "get-returns-state" = {
        expr = (handler.value.get { param = null; state = 42; }).resume;
        expected = 42;
      };
      "put-sets-state" = {
        expr = (handler.value.put { param = 99; state = 42; }).state;
        expected = 99;
      };
      "modify-applies-fn" = {
        expr = (handler.value.modify { param = x: x * 2; state = 21; }).state;
        expected = 42;
      };
    };
  };

in mk {
  doc = "Mutable state effect: get/put/modify with standard handler.";
  value = {
    inherit get put modify gets handler;
  };
}
