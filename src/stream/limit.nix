# nix-effects stream/limit: Stream limiting combinators
#
# Take a prefix of a stream by count or predicate.
{ fx, api, ... }:
let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  take = n: stream:
    if n <= 0 then core.done null
    else
      bind stream (step:
        if step._tag == "Done" then pure step
        else pure { _tag = "More"; inherit (step) head; tail = take (n - 1) step.tail; });

  takeWhile = pred: stream:
    bind stream (step:
      if step._tag == "Done" then pure step
      else if pred step.head
      then pure { _tag = "More"; inherit (step) head; tail = takeWhile pred step.tail; }
      else core.done null);

  drop = n: stream:
    if n <= 0 then stream
    else
      bind stream (step:
        if step._tag == "Done" then pure step
        else drop (n - 1) step.tail);

in
api.namespace {
  description = "Stream limiting: `take`/`takeWhile`/`drop` — bound stream length by count or predicate.";
  doc = "Stream limiting: take, takeWhile, drop.";
  value = {
    take = api.leaf {
      value = take;
      description = "take: yield at most the first `n` elements of a stream, then `Done null`; non-positive `n` yields the empty stream immediately.";
      signature = "take : Int -> Computation (Step r a) -> Computation (Step null a)";
      doc = ''
        Take the first `n` elements of a stream. Non-positive `n` yields
        the empty stream.
      '';
      tests = {
        "take-zero" = {
          expr = (take 0 (core.fromList [ 1 2 3 ])).value._tag;
          expected = "Done";
        };
      };
    };

    takeWhile = api.leaf {
      value = takeWhile;
      description = "takeWhile: yield prefix elements while the predicate holds; terminates on the first element that fails the predicate.";
      signature = "takeWhile : (a -> Bool) -> Computation (Step r a) -> Computation (Step null a)";
      doc = ''
        Take elements while a predicate holds. The first element that
        fails the predicate is discarded along with everything after.
      '';
      tests = {
        "takeWhile-false-immediately" = {
          expr =
            let s = takeWhile (_: false) (core.fromList [ 1 2 3 ]);
            in (bind s (step: pure step._tag)).value;
          expected = "Done";
        };
      };
    };

    drop = api.leaf {
      value = drop;
      description = "drop: skip the first `n` elements and forward the remainder unchanged; non-positive `n` is a no-op.";
      signature = "drop : Int -> Computation (Step r a) -> Computation (Step r a)";
      doc = ''
        Skip the first `n` elements of a stream. Non-positive `n` is a no-op.
      '';
      tests = {
        "drop-zero-passthrough" = {
          expr = (drop 0 (core.fromList [ 42 ])).value.head;
          expected = 42;
        };
      };
    };

  };
}
