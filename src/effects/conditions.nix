# nix-effects conditions: Common Lisp-style condition system
#
# Implements signal/handler/restart semantics in the algebraic effects framework.
# In CL, conditions are a superset of exceptions: signals don't unwind the stack,
# handlers can invoke restarts to recover, and multiple restarts can be offered.
#
# In our freer monad encoding:
#   signal  → sends a "condition" effect with name + data + available restarts
#   handler → decides which restart to invoke (by returning its name)
#   restart → the continuation receives the restart name and acts accordingly
#
# This is the correct algebraic effects encoding of CL conditions:
# the handler IS the algebra that chooses between restarts.
#
# References:
#   Pitman (1990) "Condition Handling in the Lisp Language Family"
#   Kent (2001) "Common Lisp HyperSpec" §9 Conditions
#   Plotkin & Pretnar (2009) "Handlers of Algebraic Effects"
{ fx, ... }:
let
  inherit (fx.kernel) pure bind send;
  signal = name: data: restarts:
    send "condition" { inherit name data restarts; };

  warn = name: data:
    bind (send "condition" { inherit name data; restarts = ["muffle-warning"]; }) (response:
      if builtins.isAttrs response && response.restart or "" == "muffle-warning"
      then pure null
      else pure null);

  # Handler strategies

  fail = {
    condition = { param, ... }:
      builtins.throw "Unhandled condition '${param.name}': ${builtins.toJSON param.data}";
  };

  ignore = {
    condition = { state, ... }: {
      resume = { restart = "continue"; value = null; };
      inherit state;
    };
  };

  collectConditions = {
    condition = { param, state }: {
      resume = { restart = "continue"; value = null; };
      state = state ++ [{ inherit (param) name data; }];
    };
  };

  withRestart = condName: restartName: restartVal: {
    condition = { param, state }:
      if param.name == condName
      then {
        resume = { restart = restartName; value = restartVal; };
        inherit state;
      }
      else builtins.throw "Unhandled condition '${param.name}'";
  };

in {
  inherit signal warn fail ignore collectConditions withRestart;



  __docs = {
    _self = {
      description = "conditions effect: Common-Lisp-style signal/warn with restart-based recovery; handler IS the algebra choosing among offered restarts.";
      doc = "CL-style condition system: signal/warn with restart-based recovery.";
    };

    signal = {
      description = "signal: raise a CL-style condition with name, data, and available restart names; the handler returns `{ restart, value }` to choose recovery.";
      signature = "signal : string -> any -> [string] -> Computation any";
      doc = ''
        Signal a condition. The handler chooses a restart strategy.

        **Arguments:**
        - `name` — condition name (e.g. `"division-by-zero"`, `"file-not-found"`)
        - `data` — condition data (error details, context)
        - `restarts` — list of available restart names

        The handler receives `{ name, data, restarts }` and returns a
        `{ restart, value }` attrset. The continuation receives this choice.
      '';
      tests = {
        "signal-is-impure" = {
          expr = fx.comp.isPure (signal "test" {} ["use-value" "abort"]);
          expected = false;
        };
        "signal-carries-name" = {
          expr = (signal "division-by-zero" { divisor = 0; } ["use-value" "abort"]).effect.param.name;
          expected = "division-by-zero";
        };
        "signal-carries-restarts" = {
          expr = builtins.length (signal "test" {} ["a" "b" "c"]).effect.param.restarts;
          expected = 3;
        };
      };
    };

    warn = {
      description = "warn: raise a warning condition with the conventional `muffle-warning` restart; if the handler doesn't muffle, computation continues.";
      signature = "warn : string -> any -> Computation null";
      doc = ''
        Signal a warning condition. Like signal but with a conventional
        `"muffle-warning"` restart. If the handler doesn't muffle, the
        computation continues normally.
      '';
      tests = {
        "warn-is-impure" = {
          expr = fx.comp.isPure (warn "deprecation" { feature = "old-api"; });
          expected = false;
        };
      };
    };

    fail = {
      description = "conditions.fail: last-resort handler that throws on any condition (via `builtins.throw`); ignores available restarts.";
      doc = ''
        Fail handler: throws on any condition. Ignores available restarts.
        Use as a last-resort handler.
      '';
    };

    ignore = {
      description = "conditions.ignore: handler that silently discards every condition by resuming with `{ restart = \"continue\"; value = null; }`.";
      doc = ''
        Ignore handler: resumes with null for any condition.
        All conditions are silently discarded.
      '';
    };

    collectConditions = {
      description = "conditions.collectConditions: handler that accumulates each condition into state as `{ name, data }` and resumes with `continue`.";
      doc = ''
        Collecting handler: accumulates conditions in state, resumes with continue.
        State shape: list of { name, data }
        Initial state: []
      '';
      tests = {
        "collects-condition" = {
          expr =
            let r = collectConditions.condition {
              param = { name = "test"; data = { x = 1; }; restarts = []; };
              state = [];
            };
            in builtins.length r.state;
          expected = 1;
        };
      };
    };

    withRestart = {
      description = "withRestart: handler factory invoking a named restart with a given value for one matched condition; throws on every other condition.";
      signature = "withRestart : string -> string -> any -> handler";
      doc = ''
        Create a handler that invokes a specific restart for a named condition.
        For all other conditions, falls through (throws).

        **Arguments:**
        - `condName` — condition name to match
        - `restartName` — restart to invoke
        - `restartVal` — value to pass via the restart
      '';
      tests = {
        "matches-condition" = {
          expr =
            let
              h = withRestart "division-by-zero" "use-value" 0;
              r = h.condition { param = { name = "division-by-zero"; data = {}; restarts = ["use-value"]; }; state = null; };
            in r.resume.restart;
          expected = "use-value";
        };
      };
    };

  };
}
