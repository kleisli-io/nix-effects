# nix-effects writer: Append-only output effect
#
# Provides tell/listen operations for accumulating output.
# The handler collects output into a list via state threading.
# Writer is the append-only restriction of state: no get, only accumulate.
{ fx, ... }:
let
  inherit (fx.kernel) pure bind send;
  tell = w: send "tell" w;

  tellAll = ws: send "tellAll" ws;

  handler = {
    tell = { param, state }: { resume = null; state = state ++ [ param ]; };
    tellAll = { param, state }: { resume = null; state = state ++ param; };
  };

in {
  inherit tell tellAll handler;



  __docs = {
    _self = {
      description = "writer effect: append-only output via tell/tellAll with a list-collecting handler. Append-only restriction of state.";
      doc = "Append-only output effect: tell/tellAll with list-collecting handler.";
    };

    tell = {
      description = "tell: append a single value to the writer effect's output log; impure request resuming with null.";
      signature = "tell : w -> Computation null";
      doc = ''
        Append a value to the output log.
      '';
      tests = {
        "tell-is-impure" = {
          expr = fx.comp.isPure (tell "hello");
          expected = false;
        };
        "tell-effect-name" = {
          expr = (tell "hello").effect.name;
          expected = "tell";
        };
      };
    };

    tellAll = {
      description = "tellAll: append a list of values to the writer effect's output log in a single impure request; one bind instead of N from mapping tell.";
      signature = "tellAll : [w] -> Computation null";
      doc = ''
        Append a list of values to the output log.
      '';
      tests = {
        "tellAll-is-impure" = {
          expr = fx.comp.isPure (tellAll [ 1 2 3 ]);
          expected = false;
        };
      };
    };

    handler = {
      description = "writer.handler: collects tell/tellAll output as a list in handler state, starting at `[]`; pair with `trampoline.handle`.";
      doc = ''
        Standard writer handler. Collects tell output in state as a list.
        Initial state: `[]`

        ```nix
        handle { handlers = writer.handler; state = []; } comp
        ```
      '';
      tests = {
        "tell-appends" = {
          expr = (handler.tell { param = "hi"; state = [ "a" ]; }).state;
          expected = [ "a" "hi" ];
        };
        "tellAll-appends-list" = {
          expr = (handler.tellAll { param = [ 1 2 ]; state = [ 0 ]; }).state;
          expected = [ 0 1 2 ];
        };
      };
    };

  };
}
