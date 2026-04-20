# nix-effects typecheck: Reusable typeCheck effect handlers
#
# Bridges the type system with the effect system.
# Type validation sends typeCheck effects; these handlers interpret them.
#
# The typeCheck effect carries: { type, context, value, path }
#   type    — a nix-effects type (has .name, .check)
#   context — string describing the local type structure (e.g. "Π domain")
#   value   — the value being checked
#   path    — list of string segments giving the structural descent from
#             the validation root (e.g. [ "a" "b" "c" ] or [ "[0]" "mtu" ]).
#             Empty for top-level validate v; accumulated by Record/ListOf/
#             Variant as they recurse via validateAt.
#
# Three standard strategies, following the algebraic effects paradigm:
# same computation, different handler, different behavior.
#
# Handler pattern follows Plotkin & Pretnar (2009) "Handlers of Algebraic
# Effects"; the freer-monad encoding is Kiselyov & Ishii (2015) "Freer
# Monads, More Extensible Effects". Types stay pure values and type
# checking is effectful computation, so the handler is the algebra.
{ api, ... }:

let
  inherit (api) mk;

  # Render the blame location: prefer path (structural descent from root)
  # when non-empty, otherwise fall back to context (local type name).
  blameLocation = param:
    let path = param.path or []; in
    if path == [] then param.context
    else builtins.concatStringsSep "." path;

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
          "Type error at ${blameLocation param}: expected ${param.type.name}, got ${builtins.typeOf param.value}";
    };
  };

  collecting = mk {
    doc = ''
      Collecting typeCheck handler: accumulates errors in state.
      Resumes with `true` on success, `false` on failure (computation continues).

      State shape: list of `{ context, typeName, actual, message, path }`
      Initial state: `[]`
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
            path = param.path or [];
            message = "Expected ${param.type.name} at ${blameLocation param}, got ${builtins.typeOf param.value}";
          }];
        };
    };
    tests = {
      "passes-good-value" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = collecting.value.typeCheck {
              param = { type = IntT; context = "test"; value = 42; path = []; };
              state = [];
            };
          in r.resume;
        expected = true;
      };
      "collects-bad-value" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = collecting.value.typeCheck {
              param = { type = IntT; context = "test"; value = "nope"; path = []; };
              state = [];
            };
          in builtins.length r.state;
        expected = 1;
      };
      "carries-path-in-state" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = collecting.value.typeCheck {
              param = { type = IntT; context = "Int"; value = "nope"; path = [ "a" "b" "c" ]; };
              state = [];
            };
          in (builtins.head r.state).path;
        expected = [ "a" "b" "c" ];
      };
    };
  };

  logging = mk {
    doc = ''
      Logging typeCheck handler: records every check (pass or fail) in state.
      Always resumes with the actual check result (boolean).

      State shape: list of `{ context, typeName, passed, path }`
      Initial state: `[]`
    '';
    value = {
      typeCheck = { param, state }:
        let passed = param.type.check param.value;
        in {
          resume = passed;
          state = state ++ [{
            context = param.context;
            typeName = param.type.name;
            path = param.path or [];
            inherit passed;
          }];
        };
    };
    tests = {
      "logs-passing-check" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = logging.value.typeCheck {
              param = { type = IntT; context = "test"; value = 42; path = []; };
              state = [];
            };
          in (builtins.head r.state).passed;
        expected = true;
      };
      "logs-failing-check" = {
        expr =
          let
            IntT = { name = "Int"; check = builtins.isInt; };
            r = logging.value.typeCheck {
              param = { type = IntT; context = "test"; value = "no"; path = []; };
              state = [];
            };
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
