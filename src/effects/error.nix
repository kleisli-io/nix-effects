# nix-effects error: Error effect with contextual stack traces
#
# Provides raise/raiseWith operations that send error effects.
# Multiple handler strategies: strict (throws), collecting (accumulates),
# and a result-based handler that wraps in Success/Error.
#
# The contextual stack trace is built by handlers accumulating context
# from nested effect operations — each raise carries a context string
# that handlers can collect.
{ fx, api, ... }:
let
  inherit (fx.kernel) send;
  raise = message: send "error" { inherit message; context = ""; };

  raiseWith = context: message: send "error" { inherit message context; };

  # Handler strategies

  strict = {
    error = { param, ... }:
      let
        prefix =
          if param.context != ""
          then "[${param.context}] "
          else "";
      in
      builtins.throw "${prefix}Error: ${param.message}";
  };

  collecting = {
    error = { param, state }: {
      resume = null;
      state = state ++ [ param ];
    };
  };

  result = {
    error = { param, state }: {
      abort = { _tag = "Error"; inherit (param) message context; };
      inherit state;
    };
  };

in
api.namespace {
  description = "error effect: raise/raiseWith with three handler strategies — strict (throw), collecting (accumulate list), and result (tagged abort).";
  doc = "Error effect with contextual messages and multiple handler strategies.";
  value = {
    raise = api.leaf {
      value = raise;
      description = "raise: send an `error` effect carrying a message and empty context; the handler decides whether to throw, collect, or recover.";
      signature = "raise : string -> Computation a";
      doc = ''
        Raise an error. Returns a Computation that sends an "error" effect.
        The handler determines what happens: throw, collect, or recover.
      '';
      tests = {
        "raise-is-impure" = {
          expr = fx.comp.isPure (raise "boom");
          expected = false;
        };
        "raise-effect-name" = {
          expr = (raise "boom").effect.name;
          expected = "error";
        };
        "raise-carries-message" = {
          expr = (raise "boom").effect.param.message;
          expected = "boom";
        };
      };
    };

    raiseWith = api.leaf {
      value = raiseWith;
      description = "raiseWith: raise an error with a context string; handlers can collect contexts to assemble stack-trace-style reports.";
      signature = "raiseWith : string -> string -> Computation a";
      doc = ''
        Raise an error with context. The context string describes where
        in the computation the error occurred, enabling stack-trace-like
        error reports when used with the collecting handler.
      '';
      tests = {
        "raiseWith-carries-context" = {
          expr = (raiseWith "parser" "unexpected token").effect.param.context;
          expected = "parser";
        };
      };
    };

    strict = api.leaf {
      value = strict;
      description = "error.strict: handler that throws on the first error via `builtins.throw`, prefixing context when present; halts evaluation immediately.";
      doc = ''
        Strict error handler: throws on first error via builtins.throw.
        Use when errors should halt evaluation immediately.

        Includes context in the thrown message when available.
      '';
    };

    collecting = api.leaf {
      value = collecting;
      description = "error.collecting: handler that accumulates every error into state as a list of `{ message, context }` and resumes computation with null.";
      doc = ''
        Collecting error handler: accumulates errors in state as a list.
        Resumes computation with null so subsequent effects still execute.
        Use when you want all errors, not just the first.

        State shape: list of { message, context }
      '';
      tests = {
        "collects-error" = {
          expr =
            let r = collecting.error { param = { message = "bad"; context = "test"; }; state = [ ]; };
            in builtins.length r.state;
          expected = 1;
        };
        "preserves-existing" = {
          expr =
            let
              r = collecting.error {
                param = { message = "second"; context = ""; };
                state = [{ message = "first"; context = ""; }];
              };
            in
            builtins.length r.state;
          expected = 2;
        };
      };
    };

    result = api.leaf {
      value = result;
      description = "error.result: handler that aborts with a tagged `{ _tag = \"Error\"; message; context; }` value; uses the non-resumption protocol.";
      doc = ''
        Result error handler: aborts computation with tagged Error value.
        Uses the non-resumption protocol to discard the continuation.

        Returns `{ _tag = "Error"; message; context; }` on error.
      '';
      tests = {
        "aborts-with-error-tag" = {
          expr =
            let r = result.error { param = { message = "boom"; context = "test"; }; state = null; };
            in r.abort._tag;
          expected = "Error";
        };
        "carries-message" = {
          expr =
            let r = result.error { param = { message = "boom"; context = "test"; }; state = null; };
            in r.abort.message;
          expected = "boom";
        };
      };
    };

  };
}
