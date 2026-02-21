# nix-effects stream/transform: Stream transformation combinators
#
# Pure transformations on streams: map and filter.
# These produce new streams by transforming or selecting elements.
{ fx, api, ... }:

let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  inherit (api) mk;

  smap = mk {
    doc = ''
      Map a function over each element of a stream.

      smap : (a -> b) -> Computation (Step r a) -> Computation (Step r b)
    '';
    value = f: stream:
      bind stream (step:
        if step._tag == "Done" then pure step
        else pure { _tag = "More"; head = f step.head; tail = smap.value f step.tail; });
    tests = {
      "map-done" = {
        expr = let s = smap.value (x: x * 2) (core.done null);
               in (bind s (step: pure step._tag)).value;
        expected = "Done";
      };
    };
  };

  sfilter = mk {
    doc = ''
      Keep only elements satisfying a predicate.

      sfilter : (a -> bool) -> Computation (Step r a) -> Computation (Step r a)
    '';
    value = pred: stream:
      bind stream (step:
        if step._tag == "Done" then pure step
        else if pred step.head
          then pure { _tag = "More"; inherit (step) head; tail = sfilter.value pred step.tail; }
          else sfilter.value pred step.tail);
    tests = {
      "filter-done" = {
        expr = let s = sfilter.value (x: x > 0) (core.done null);
               in (bind s (step: pure step._tag)).value;
        expected = "Done";
      };
    };
  };

  scanl = mk {
    doc = ''
      Accumulate a running fold over the stream, yielding each intermediate value.

      scanl : (b -> a -> b) -> b -> Computation (Step r a) -> Computation (Step r b)
    '';
    value = f: z: stream:
      bind stream (step:
        if step._tag == "Done" then core.more z (core.done null)
        else
          let next = f z step.head;
          in pure { _tag = "More"; head = z; tail = scanl.value f next step.tail; });
  };

in mk {
  doc = "Stream transformations: map, filter, scanl.";
  value = {
    map = smap;
    filter = sfilter;
    inherit scanl;
  };
}
