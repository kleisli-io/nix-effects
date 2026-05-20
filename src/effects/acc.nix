# nix-effects acc: Accumulator effect
#
# Specialized state for list accumulation. Provides emit/emitAll for
# appending items, and collect for reading accumulated items.
# Useful for building result lists incrementally through effects.
{ fx, api, ... }:
let
  inherit (fx.kernel) pure bind send;
  emit = item: send "emit" item;

  emitAll = items: send "emitAll" items;

  collect = send "collect" null;

  handler = {
    emit = { param, state }: { resume = null; state = state ++ [ param ]; };
    emitAll = { param, state }: { resume = null; state = state ++ param; };
    collect = { state, ... }: { resume = state; inherit state; };
  };

in
api.namespace {
  description = "acc effect: incremental list building via emit/emitAll/collect with a default handler that appends to a list state.";
  doc = "Accumulator effect: emit/emitAll/collect for incremental list building.";
  value = {
    emit = api.leaf {
      value = emit;
      description = "emit: append a single item to the acc effect's accumulator; issues an impure effect request whose result is null.";
      signature = "emit : a -> Computation null";
      doc = ''
        Append a single item to the accumulator. Pairs with `collect` to read
        back all items emitted within the surrounding handled scope.
      '';
      tests = {
        "emit-is-impure" = {
          expr = fx.comp.isPure (emit 42);
          expected = false;
        };
        "emit-effect-name" = {
          expr = (emit 42).effect.name;
          expected = "emit";
        };
      };
    };

    emitAll = api.leaf {
      value = emitAll;
      description = "emitAll: append a list of items to the acc effect's accumulator in a single impure request; one bind instead of N from mapping emit.";
      signature = "emitAll : [a] -> Computation null";
      doc = ''
        Append a list of items to the accumulator in a single effect request.
        Equivalent to mapping `emit` over the list but cheaper at runtime.
      '';
      tests = {
        "emitAll-is-impure" = {
          expr = fx.comp.isPure (emitAll [ 1 2 ]);
          expected = false;
        };
      };
    };

    collect = api.leaf {
      value = collect;
      description = "collect: read the acc effect's currently accumulated items as a list; impure request returning the contents captured so far.";
      signature = "collect : Computation [a]";
      doc = ''
        Read the current accumulated items as a list. Returns whatever has been
        emitted within the surrounding handled scope.
      '';
      tests = {
        "collect-is-impure" = {
          expr = fx.comp.isPure collect;
          expected = false;
        };
      };
    };

    handler = api.leaf {
      value = handler;
      description = "acc.handler: standard accumulator handler implementing emit/emitAll/collect over a list state with `[]` as the initial value.";
      doc = ''
        Standard accumulator handler. State is the list of accumulated items,
        starting at `[]`.

        ```nix
        handle { handlers = acc.handler; state = []; } comp
        ```
      '';
      tests = {
        "emit-appends" = {
          expr = (handler.emit { param = 42; state = [ 1 ]; }).state;
          expected = [ 1 42 ];
        };
        "collect-returns-state" = {
          expr = (handler.collect { param = null; state = [ 1 2 3 ]; }).resume;
          expected = [ 1 2 3 ];
        };
      };
    };

  };
}
