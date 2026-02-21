# nix-effects typecheck: Reusable typeCheck effect handlers
#
# Bridges the type system (Phase 3) with the effect system (Phase 4).
# Type validation sends typeCheck effects; these handlers interpret them.
#
# The typeCheck effect carries: { type, context, value }
#   type    — a nix-effects type (has .name, .check)
#   context — string describing where in the type structure (e.g. "Π domain")
#   value   — the value being checked
#
# Three standard strategies, following the algebraic effects paradigm:
# same computation, different handler, different behavior.
#
# Fire Triangle (Pedrot & Tabareau 2020): types are pure values,
# type checking is effectful computation. The handler IS the algebra.
{ api, ... }:

let
  inherit (api) mk;

  strict = mk {
    doc = ''
      Strict typeCheck handler: throws on first type error.
      Resumes with true on success (check passed).

      Use when type errors should halt evaluation immediately.
      State: unused (pass null).
    '';
    value = {
      typeCheck = { param, state }:
        if param.type.check param.value
        then { resume = true; inherit state; }
        else builtins.throw
          "Type error in ${param.context}: expected ${param.type.name}, got ${builtins.typeOf param.value}";
    };
  };

  collecting = mk {
    doc = ''
      Collecting typeCheck handler: accumulates errors in state.
      Resumes with true on success, false on failure (computation continues).

      State shape: list of { context, typeName, actual, message }
      Initial state: []
    '';
    value = {
      typeCheck = { param, state }:
        if param.type.check param.value
        then { resume = true; inherit state; }
        else {
          resume = false;
          state = state ++ [{
            context = param.context;
            typeName = param.type.name;
            actual = builtins.typeOf param.value;
            message = "Expected ${param.type.name}, got ${builtins.typeOf param.value}";
          }];
        };
    };
    tests = {
      "passes-good-value" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = collecting.value.typeCheck { param = { type = IntT; context = "test"; value = 42; }; state = []; };
          in r.resume;
        expected = true;
      };
      "collects-bad-value" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = collecting.value.typeCheck { param = { type = IntT; context = "test"; value = "nope"; }; state = []; };
          in builtins.length r.state;
        expected = 1;
      };
    };
  };

  logging = mk {
    doc = ''
      Logging typeCheck handler: records every check (pass or fail) in state.
      Always resumes with the actual check result (boolean).

      State shape: list of { context, typeName, passed }
      Initial state: []
    '';
    value = {
      typeCheck = { param, state }:
        let passed = param.type.check param.value;
        in {
          resume = passed;
          state = state ++ [{
            context = param.context;
            typeName = param.type.name;
            inherit passed;
          }];
        };
    };
    tests = {
      "logs-passing-check" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = logging.value.typeCheck { param = { type = IntT; context = "test"; value = 42; }; state = []; };
          in (builtins.head r.state).passed;
        expected = true;
      };
      "logs-failing-check" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = logging.value.typeCheck { param = { type = IntT; context = "test"; value = "no"; }; state = []; };
          in (builtins.head r.state).passed;
        expected = false;
      };
    };
  };

in mk {
  doc = "Reusable typeCheck handlers: strict (throw), collecting (accumulate), logging (record all).";
  value = {
    inherit strict collecting logging;
  };
}
