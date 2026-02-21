# nix-effects acc: Accumulator effect
#
# Specialized state for list accumulation. Provides emit/emitAll for
# appending items, and collect for reading accumulated items.
# Useful for building result lists incrementally through effects.
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  emit = mk {
    doc = ''
      Append a single item to the accumulator.

      emit : a -> Computation null
    '';
    value = item: send "emit" item;
    tests = {
      "emit-is-impure" = {
        expr = (emit.value 42)._tag;
        expected = "Impure";
      };
      "emit-effect-name" = {
        expr = (emit.value 42).effect.name;
        expected = "emit";
      };
    };
  };

  emitAll = mk {
    doc = ''
      Append a list of items to the accumulator.

      emitAll : [a] -> Computation null
    '';
    value = items: send "emitAll" items;
    tests = {
      "emitAll-is-impure" = {
        expr = (emitAll.value [ 1 2 ])._tag;
        expected = "Impure";
      };
    };
  };

  collect = mk {
    doc = ''
      Read the current accumulated items.

      collect : Computation [a]
    '';
    value = send "collect" null;
    tests = {
      "collect-is-impure" = {
        expr = collect.value._tag;
        expected = "Impure";
      };
    };
  };

  handler = mk {
    doc = ''
      Standard accumulator handler. State is a list of accumulated items.
      Initial state: []

        handle { handlers = acc.handler; state = []; } comp
    '';
    value = {
      emit = { param, state }: { resume = null; state = state ++ [ param ]; };
      emitAll = { param, state }: { resume = null; state = state ++ param; };
      collect = { state, ... }: { resume = state; inherit state; };
    };
    tests = {
      "emit-appends" = {
        expr = (handler.value.emit { param = 42; state = [ 1 ]; }).state;
        expected = [ 1 42 ];
      };
      "collect-returns-state" = {
        expr = (handler.value.collect { param = null; state = [ 1 2 3 ]; }).resume;
        expected = [ 1 2 3 ];
      };
    };
  };

in mk {
  doc = "Accumulator effect: emit/emitAll/collect for incremental list building.";
  value = {
    inherit emit emitAll collect handler;
  };
}
