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
  inherit (api) mk;

  raise = mk {
    doc = ''
      Raise an error. Returns a Computation that sends an "error" effect.
      The handler determines what happens: throw, collect, or recover.

      ```
      raise : string -> Computation a
      ```
    '';
    value = message: send "error" { inherit message; context = ""; };
    tests = {
      "raise-is-impure" = {
        expr = (raise.value "boom")._tag;
        expected = "Impure";
      };
      "raise-effect-name" = {
        expr = (raise.value "boom").effect.name;
        expected = "error";
      };
      "raise-carries-message" = {
        expr = (raise.value "boom").effect.param.message;
        expected = "boom";
      };
    };
  };

  raiseWith = mk {
    doc = ''
      Raise an error with context. The context string describes where
      in the computation the error occurred, enabling stack-trace-like
      error reports when used with the collecting handler.

      ```
      raiseWith : string -> string -> Computation a
      ```
    '';
    value = context: message: send "error" { inherit message context; };
    tests = {
      "raiseWith-carries-context" = {
        expr = (raiseWith.value "parser" "unexpected token").effect.param.context;
        expected = "parser";
      };
    };
  };

  # Handler strategies

  strict = mk {
    doc = ''
      Strict error handler: throws on first error via builtins.throw.
      Use when errors should halt evaluation immediately.

      Includes context in the thrown message when available.
    '';
    value = {
      error = { param, ... }:
        let
          prefix = if param.context != ""
                   then "[${param.context}] "
                   else "";
        in builtins.throw "${prefix}Error: ${param.message}";
    };
  };

  collecting = mk {
    doc = ''
      Collecting error handler: accumulates errors in state as a list.
      Resumes computation with null so subsequent effects still execute.
      Use when you want all errors, not just the first.

      State shape: list of { message, context }
    '';
    value = {
      error = { param, state }: {
        resume = null;
        state = state ++ [param];
      };
    };
    tests = {
      "collects-error" = {
        expr =
          let result = collecting.value.error { param = { message = "bad"; context = "test"; }; state = []; };
          in builtins.length result.state;
        expected = 1;
      };
      "preserves-existing" = {
        expr =
          let result = collecting.value.error {
            param = { message = "second"; context = ""; };
            state = [{ message = "first"; context = ""; }];
          };
          in builtins.length result.state;
        expected = 2;
      };
    };
  };

  result = mk {
    doc = ''
      Result error handler: aborts computation with tagged Error value.
      Uses the non-resumption protocol to discard the continuation.

      Returns `{ _tag = "Error"; message; context; }` on error.
    '';
    value = {
      error = { param, state }: {
        abort = { _tag = "Error"; inherit (param) message context; };
        inherit state;
      };
    };
    tests = {
      "aborts-with-error-tag" = {
        expr =
          let r = result.value.error { param = { message = "boom"; context = "test"; }; state = null; };
          in r.abort._tag;
        expected = "Error";
      };
      "carries-message" = {
        expr =
          let r = result.value.error { param = { message = "boom"; context = "test"; }; state = null; };
          in r.abort.message;
        expected = "boom";
      };
    };
  };

in mk {
  doc = "Error effect with contextual messages and multiple handler strategies.";
  value = {
    inherit raise raiseWith strict collecting result;
  };
}
