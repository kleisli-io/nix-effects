# nix-effects stream/core: Effectful stream primitives
#
# Streams are computations that produce a sequence of values on demand.
# Each step yields either:
#   { _tag = "Done"; value = finalValue; }
#   { _tag = "More"; head = item; tail = nextComputation; }
#
# This is the standard encoding from iteratee/conduit/streaming libraries,
# adapted for the freer monad framework. Streams are lazy — each step is
# a Computation that must be interpreted to advance.
{ fx, api, ... }:
let
  inherit (fx.kernel) pure bind send;
  done = v: pure { _tag = "Done"; value = v; };

  more = head: tail: pure { _tag = "More"; inherit head tail; };

  fromList = xs:
    if xs == [ ] then done null
    else more (builtins.head xs) (fromList (builtins.tail xs));

  iterate = f: x: more x (iterate f (f x));

  range = start: end:
    if start >= end then done null
    else more start (range (start + 1) end);

  replicate = n: x:
    if n <= 0 then done null
    else more x (replicate (n - 1) x);

in
api.namespace {
  description = "Stream primitives: `done`/`more`/`fromList`/`iterate`/`range`/`replicate` — constructors for lazy `Step`-tagged streams composed via bind.";
  doc = "Stream primitives: done/more/fromList/iterate/range/replicate.";
  value = {
    done = api.leaf {
      value = done;
      description = "done: terminate a stream with a final value; produces a pure `Step` tagged `Done` carrying that value as the stream's result.";
      signature = "done : a -> Computation (Step a b)";
      doc = ''
        Terminate a stream with a final value. Returns a pure Computation
        whose `_tag` is `"Done"` and whose `value` is the supplied result.
      '';
      tests = {
        "done-is-pure" = {
          expr = fx.comp.isPure (done null);
          expected = true;
        };
        "done-value-tag" = {
          expr = (done null).value._tag;
          expected = "Done";
        };
      };
    };

    more = api.leaf {
      value = more;
      description = "more: yield one head element followed by a continuation stream; produces a pure `Step` tagged `More` with `head` and `tail` fields.";
      signature = "more : a -> Computation (Step r a) -> Computation (Step r a)";
      doc = ''
        Yield an element and a continuation stream. The `tail` argument is
        a Computation, so the rest of the stream stays lazy.
      '';
      tests = {
        "more-is-pure" = {
          expr = fx.comp.isPure (more 1 (done null));
          expected = true;
        };
        "more-head" = {
          expr = (more 42 (done null)).value.head;
          expected = 42;
        };
      };
    };

    fromList = api.leaf {
      value = fromList;
      description = "fromList: convert a Nix list into a stream; emits each element as `More` and terminates with `Done null`.";
      signature = "fromList : [a] -> Computation (Step null a)";
      doc = ''
        Create a stream from a list. The empty list collapses to `done null`.
      '';
      tests = {
        "empty-list-is-done" = {
          expr = (fromList [ ]).value._tag;
          expected = "Done";
        };
        "singleton-head" = {
          expr = (fromList [ 42 ]).value.head;
          expected = 42;
        };
      };
    };

    iterate = api.leaf {
      value = iterate;
      description = "iterate: build an infinite stream by repeated application: `[x, f x, f (f x), ...]`; must be paired with a limiting combinator to terminate.";
      signature = "iterate : (a -> a) -> a -> Computation (Step r a)";
      doc = ''
        Create an infinite stream by repeated application:

        ```
        iterate f x = [x, f(x), f(f(x)), ...]
        ```

        Must be consumed with a limiting combinator (`take`, `takeWhile`).
      '';
      tests = {
        "iterate-first" = {
          expr = (iterate (x: x + 1) 0).value.head;
          expected = 0;
        };
      };
    };

    range = api.leaf {
      value = range;
      description = "range: build a stream of integers from `start` inclusive to `end` exclusive; empty when `start >= end`.";
      signature = "range : Int -> Int -> Computation (Step null Int)";
      doc = ''
        Create a stream of integers from `start` (inclusive) to `end`
        (exclusive). Empty when `start >= end`.
      '';
      tests = {
        "range-empty" = {
          expr = (range 5 5).value._tag;
          expected = "Done";
        };
        "range-first" = {
          expr = (range 0 3).value.head;
          expected = 0;
        };
      };
    };

    replicate = api.leaf {
      value = replicate;
      description = "replicate: build a stream of `n` copies of value `x`; empty when `n <= 0`, otherwise emits `n` `More` steps then `Done null`.";
      signature = "replicate : Int -> a -> Computation (Step null a)";
      doc = ''
        Create a stream of `n` copies of a value. Empty when `n <= 0`.
      '';
      tests = {
        "replicate-zero" = {
          expr = (replicate 0 "x").value._tag;
          expected = "Done";
        };
        "replicate-head" = {
          expr = (replicate 3 "x").value.head;
          expected = "x";
        };
      };
    };

  };
}
