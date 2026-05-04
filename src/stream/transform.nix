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

      ```
      smap : (a -> b) -> Computation (Step r a) -> Computation (Step r b)
      ```
    '';
    value = f: stream:
      bind stream (step:
        if step._tag == "Done" then pure step
        else pure { _tag = "More"; head = f step.head; tail = smap f step.tail; });
    tests = {
      "map-done" = {
        expr = let s = smap (x: x * 2) (core.done null);
               in (bind s (step: pure step._tag)).value;
        expected = "Done";
      };
    };
  };

  sfilter = mk {
    doc = ''
      Keep only elements satisfying a predicate.

      ```
      sfilter : (a -> bool) -> Computation (Step r a) -> Computation (Step r a)
      ```
    '';
    value = pred: stream:
      bind stream (step:
        if step._tag == "Done" then pure step
        else if pred step.head
          then pure { _tag = "More"; inherit (step) head; tail = sfilter pred step.tail; }
          else sfilter pred step.tail);
    tests = {
      "filter-done" = {
        expr = let s = sfilter (x: x > 0) (core.done null);
               in (bind s (step: pure step._tag)).value;
        expected = "Done";
      };
    };
  };

  mapTo = mk {
    doc = ''
      Replace every element of a stream with a constant value.

      ```
      mapTo : a -> Computation (Step r b) -> Computation (Step r a)
      ```
    '';
    value = v: stream: bind stream (step:
      if step._tag == "Done" then pure step
      else pure { _tag = "More"; head = v; tail = mapTo v step.tail; });
    tests = {
      "mapTo-drops-values" = {
        expr = let s = mapTo 42 (core.fromList [ 1 2 3 ]);
               in (bind s (step: if step._tag == "Done" then pure step._tag else pure step.head)).value;
        expected = 42;
      };
    };
  };

  startWith = mk {
    doc = ''
      Prepend a seed value to a stream.

      ```
      startWith : a -> Computation (Step r a) -> Computation (Step r a)
      ```
    '';
    value = v: stream: fx.stream.combine.concat (core.fromList [ v ]) stream;
    tests = {
      "startWith-first-element" = {
        expr = let s = startWith "init" (core.fromList [ "a" "b" ]);
               in (fx.stream.reduce.toList s).value;
        expected = [ "init" "a" "b" ];
      };
    };
  };

  scanl = mk {
    doc = ''
      Accumulate a running fold over the stream, yielding each intermediate value.

      ```
      scanl : (b -> a -> b) -> b -> Computation (Step r a) -> Computation (Step r b)
      ```
    '';
    value = f: z: stream:
      bind stream (step:
        if step._tag == "Done" then core.more z (core.done null)
        else
          let next = f z step.head;
          in pure { _tag = "More"; head = z; tail = scanl f next step.tail; });
  };

in mk {
  doc = "Stream transformations: map, filter, scanl, mapTo, startWith.";
  value = {
    map = smap;
    filter = sfilter;
    mapTo = mapTo;
    startWith = startWith;
    inherit scanl;
  };
}
