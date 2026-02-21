# nix-effects writer: Append-only output effect
#
# Provides tell/listen operations for accumulating output.
# The handler collects output into a list via state threading.
# Writer is the append-only restriction of state: no get, only accumulate.
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  tell = mk {
    doc = ''
      Append a value to the output log.

      tell : w -> Computation null
    '';
    value = w: send "tell" w;
    tests = {
      "tell-is-impure" = {
        expr = (tell.value "hello")._tag;
        expected = "Impure";
      };
      "tell-effect-name" = {
        expr = (tell.value "hello").effect.name;
        expected = "tell";
      };
    };
  };

  tellAll = mk {
    doc = ''
      Append a list of values to the output log.

      tellAll : [w] -> Computation null
    '';
    value = ws: send "tellAll" ws;
    tests = {
      "tellAll-is-impure" = {
        expr = (tellAll.value [ 1 2 3 ])._tag;
        expected = "Impure";
      };
    };
  };

  handler = mk {
    doc = ''
      Standard writer handler. Collects tell output in state as a list.
      Initial state: []

        handle { handlers = writer.handler; state = []; } comp
    '';
    value = {
      tell = { param, state }: { resume = null; state = state ++ [ param ]; };
      tellAll = { param, state }: { resume = null; state = state ++ param; };
    };
    tests = {
      "tell-appends" = {
        expr = (handler.value.tell { param = "hi"; state = [ "a" ]; }).state;
        expected = [ "a" "hi" ];
      };
      "tellAll-appends-list" = {
        expr = (handler.value.tellAll { param = [ 1 2 ]; state = [ 0 ]; }).state;
        expected = [ 0 1 2 ];
      };
    };
  };

in mk {
  doc = "Append-only output effect: tell/tellAll with list-collecting handler.";
  value = {
    inherit tell tellAll handler;
  };
}
