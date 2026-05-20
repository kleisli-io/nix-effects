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
{ fx, ... }:
let
  inherit (fx.kernel) pure bind send;
  get = send "get" null;

  put = s: send "put" s;

  update = f:
    bind get (state: bind (f state) ({ state, value }: bind (put state) (_: pure value)));

  modify = f: send "modify" f;

  gets = f: bind (send "get" null) (s: pure (f s));

  handler = {
    get = { state, ... }: { resume = state; inherit state; };
    put = { param, ... }: { resume = null; state = param; };
    modify = { param, state }: { resume = null; state = param state; };
  };

in {
  inherit get put modify update gets handler;



  __docs = {
    _self = {
      description = "state effect: mutable state threaded by the handler; get/put/modify with update/gets sugar and a standard handler.";
      doc = "Mutable state effect: get/put/modify with standard handler.";
    };

    get = {
      description = "get: read the current state threaded by the state handler; impure request whose response IS the handler state.";
      signature = "get : Computation s";
      doc = ''
        Read the current state. Returns a Computation that, when handled,
        yields the current state value.
      '';
      tests = {
        "get-is-impure" = {
          expr = fx.comp.isPure get;
          expected = false;
        };
        "get-effect-name" = {
          expr = get.effect.name;
          expected = "get";
        };
      };
    };

    put = {
      description = "put: replace the current state with the supplied value; impure request resuming with null.";
      signature = "put : s -> Computation null";
      doc = ''
        Replace the current state. Returns a Computation that, when handled,
        sets the state to the given value and returns null.
      '';
      tests = {
        "put-is-impure" = {
          expr = fx.comp.isPure (put 42);
          expected = false;
        };
        "put-carries-value" = {
          expr = (put 42).effect.param;
          expected = 42;
        };
      };
    };

    update = {
      description = "update: read the state, run a user computation against it to produce `{ state, value }`, put the new state, return the value.";
      signature = "update : (s -> Computation { state, value }) -> Computation value";
      doc = ''
        Apply a computation to the current state. Returns a Computation that,
        when handled, updates the state and returns value.
      '';
      tests = {
        "update-is-impure" = {
          expr = fx.comp.isPure (update (x: pure {
            value = x + 1;
            state = 99;
          }));
          expected = false;
        };
        "update-reads-and-updates" = {
          expr =
            fx.trampoline.handle { handlers = handler; state = 11; }
              (update (s: pure { state = s * 2; value = s * 3; }));
          expected.state = 22;
          expected.value = 33;
        };
      };
    };

    modify = {
      description = "modify: apply a function to the current state in place; impure request resuming with null after the handler runs the transformer.";
      signature = "modify : (s -> s) -> Computation null";
      doc = ''
        Apply a function to the current state. Returns a Computation that,
        when handled, transforms the state via f and returns null.
      '';
      tests = {
        "modify-is-impure" = {
          expr = fx.comp.isPure (modify (x: x + 1));
          expected = false;
        };
      };
    };

    gets = {
      description = "gets: read a projection of the current state via a user function; sugar for `bind get (s: pure (f s))`.";
      signature = "gets : (s -> a) -> Computation a";
      doc = ''
        Read a projection of the current state.
      '';
      tests = {
        "gets-is-impure" = {
          expr = fx.comp.isPure (gets (s: s.x));
          expected = false;
        };
      };
    };

    handler = {
      description = "state.handler: interprets get/put/modify over a single state value; pair with `trampoline.handle` and the initial state.";
      doc = ''
        Standard state handler. Interprets get/put/modify effects.
        Use with `trampoline.handle`:

        ```nix
        handle { handlers = state.handler; state = initialState; } comp
        ```

        - `get`: returns current state as value
        - `put`: replaces state with param, returns null
        - `modify`: applies param (a function) to state, returns null
      '';
      tests = {
        "get-returns-state" = {
          expr = (handler.get { param = null; state = 42; }).resume;
          expected = 42;
        };
        "put-sets-state" = {
          expr = (handler.put { param = 99; state = 42; }).state;
          expected = 99;
        };
        "modify-applies-fn" = {
          expr = (handler.modify { param = x: x * 2; state = 21; }).state;
          expected = 42;
        };
      };
    };

  };
}
