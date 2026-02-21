# nix-effects stream/limit: Stream limiting combinators
#
# Take a prefix of a stream by count or predicate.
{ fx, api, ... }:

let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  inherit (api) mk;

  take = mk {
    doc = ''
      Take the first n elements of a stream.

      take : int -> Computation (Step r a) -> Computation (Step null a)
    '';
    value = n: stream:
      if n <= 0 then core.done null
      else bind stream (step:
        if step._tag == "Done" then pure step
        else pure { _tag = "More"; inherit (step) head; tail = take.value (n - 1) step.tail; });
    tests = {
      "take-zero" = {
        expr = (take.value 0 (core.fromList [ 1 2 3 ])).value._tag;
        expected = "Done";
      };
    };
  };

  takeWhile = mk {
    doc = ''
      Take elements while a predicate holds.

      takeWhile : (a -> bool) -> Computation (Step r a) -> Computation (Step null a)
    '';
    value = pred: stream:
      bind stream (step:
        if step._tag == "Done" then pure step
        else if pred step.head
          then pure { _tag = "More"; inherit (step) head; tail = takeWhile.value pred step.tail; }
          else core.done null);
    tests = {
      "takeWhile-false-immediately" = {
        expr = let s = takeWhile.value (_: false) (core.fromList [ 1 2 3 ]);
               in (bind s (step: pure step._tag)).value;
        expected = "Done";
      };
    };
  };

  drop = mk {
    doc = ''
      Skip the first n elements of a stream.

      drop : int -> Computation (Step r a) -> Computation (Step r a)
    '';
    value = n: stream:
      if n <= 0 then stream
      else bind stream (step:
        if step._tag == "Done" then pure step
        else drop.value (n - 1) step.tail);
    tests = {
      "drop-zero-passthrough" = {
        expr = (drop.value 0 (core.fromList [ 42 ])).value.head;
        expected = 42;
      };
    };
  };

in mk {
  doc = "Stream limiting: take, takeWhile, drop.";
  value = {
    inherit take takeWhile drop;
  };
}
