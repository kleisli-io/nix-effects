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
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  signal = mk {
    doc = ''
      Signal a condition. The handler chooses a restart strategy.

      signal : string -> any -> list string -> Computation any

      Arguments:
        name     — condition name (e.g. "division-by-zero", "file-not-found")
        data     — condition data (error details, context)
        restarts — list of available restart names

      The handler receives { name, data, restarts } and returns a
      { restart, value } attrset. The continuation receives this choice.
    '';
    value = name: data: restarts:
      send "condition" { inherit name data restarts; };
    tests = {
      "signal-is-impure" = {
        expr = (signal.value "test" {} ["use-value" "abort"])._tag;
        expected = "Impure";
      };
      "signal-carries-name" = {
        expr = (signal.value "division-by-zero" { divisor = 0; } ["use-value" "abort"]).effect.param.name;
        expected = "division-by-zero";
      };
      "signal-carries-restarts" = {
        expr = builtins.length (signal.value "test" {} ["a" "b" "c"]).effect.param.restarts;
        expected = 3;
      };
    };
  };

  warn = mk {
    doc = ''
      Signal a warning condition. Like signal but with a conventional
      "muffle-warning" restart. If the handler doesn't muffle, the
      computation continues normally.

      warn : string -> any -> Computation null
    '';
    value = name: data:
      bind (send "condition" { inherit name data; restarts = ["muffle-warning"]; }) (response:
        if builtins.isAttrs response && response.restart or "" == "muffle-warning"
        then pure null
        else pure null);
    tests = {
      "warn-is-impure" = {
        expr = (warn.value "deprecation" { feature = "old-api"; })._tag;
        expected = "Impure";
      };
    };
  };

  # Handler strategies

  fail = mk {
    doc = ''
      Fail handler: throws on any condition. Ignores available restarts.
      Use as a last-resort handler.
    '';
    value = {
      condition = { param, ... }:
        builtins.throw "Unhandled condition '${param.name}': ${builtins.toJSON param.data}";
    };
  };

  ignore = mk {
    doc = ''
      Ignore handler: resumes with null for any condition.
      All conditions are silently discarded.
    '';
    value = {
      condition = { state, ... }: {
        resume = { restart = "continue"; value = null; };
        inherit state;
      };
    };
  };

  collectConditions = mk {
    doc = ''
      Collecting handler: accumulates conditions in state, resumes with continue.
      State shape: list of { name, data }
      Initial state: []
    '';
    value = {
      condition = { param, state }: {
        resume = { restart = "continue"; value = null; };
        state = state ++ [{ inherit (param) name data; }];
      };
    };
    tests = {
      "collects-condition" = {
        expr =
          let r = collectConditions.value.condition {
            param = { name = "test"; data = { x = 1; }; restarts = []; };
            state = [];
          };
          in builtins.length r.state;
        expected = 1;
      };
    };
  };

  withRestart = mk {
    doc = ''
      Create a handler that invokes a specific restart for a named condition.
      For all other conditions, falls through (throws).

      withRestart : string -> string -> any -> handler

      Arguments:
        condName    — condition name to match
        restartName — restart to invoke
        restartVal  — value to pass via the restart
    '';
    value = condName: restartName: restartVal: {
      condition = { param, state }:
        if param.name == condName
        then {
          resume = { restart = restartName; value = restartVal; };
          inherit state;
        }
        else builtins.throw "Unhandled condition '${param.name}'";
    };
    tests = {
      "matches-condition" = {
        expr =
          let
            h = withRestart.value "division-by-zero" "use-value" 0;
            r = h.condition { param = { name = "division-by-zero"; data = {}; restarts = ["use-value"]; }; state = null; };
          in r.resume.restart;
        expected = "use-value";
      };
    };
  };

in mk {
  doc = "CL-style condition system: signal/warn with restart-based recovery.";
  value = {
    inherit signal warn fail ignore collectConditions withRestart;
  };
}
