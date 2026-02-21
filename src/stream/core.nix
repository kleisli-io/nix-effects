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
  inherit (api) mk;

  done = mk {
    doc = ''
      Terminate a stream with a final value.

      ```
      done : a -> Computation (Step a b)
      ```
    '';
    value = v: pure { _tag = "Done"; value = v; };
    tests = {
      "done-is-pure" = {
        expr = (done.value null)._tag;
        expected = "Pure";
      };
      "done-value-tag" = {
        expr = (done.value null).value._tag;
        expected = "Done";
      };
    };
  };

  more = mk {
    doc = ''
      Yield an element and a continuation stream.

      ```
      more : a -> Computation (Step r a) -> Computation (Step r a)
      ```
    '';
    value = head: tail: pure { _tag = "More"; inherit head tail; };
    tests = {
      "more-is-pure" = {
        expr = (more.value 1 (done.value null))._tag;
        expected = "Pure";
      };
      "more-head" = {
        expr = (more.value 42 (done.value null)).value.head;
        expected = 42;
      };
    };
  };

  fromList = mk {
    doc = ''
      Create a stream from a list.

      ```
      fromList : [a] -> Computation (Step null a)
      ```
    '';
    value = xs:
      if xs == [] then done.value null
      else more.value (builtins.head xs) (fromList.value (builtins.tail xs));
    tests = {
      "empty-list-is-done" = {
        expr = (fromList.value []).value._tag;
        expected = "Done";
      };
      "singleton-head" = {
        expr = (fromList.value [ 42 ]).value.head;
        expected = 42;
      };
    };
  };

  iterate = mk {
    doc = ''
      Create an infinite stream by repeated application.

      ```
      iterate f x = [x, f(x), f(f(x)), ...]
      ```

      Must be consumed with a limiting combinator (take, takeWhile).

      ```
      iterate : (a -> a) -> a -> Computation (Step r a)
      ```
    '';
    value = f: x: more.value x (iterate.value f (f x));
    tests = {
      "iterate-first" = {
        expr = (iterate.value (x: x + 1) 0).value.head;
        expected = 0;
      };
    };
  };

  range = mk {
    doc = ''
      Create a stream of integers from start (inclusive) to end (exclusive).

      ```
      range : int -> int -> Computation (Step null int)
      ```
    '';
    value = start: end:
      if start >= end then done.value null
      else more.value start (range.value (start + 1) end);
    tests = {
      "range-empty" = {
        expr = (range.value 5 5).value._tag;
        expected = "Done";
      };
      "range-first" = {
        expr = (range.value 0 3).value.head;
        expected = 0;
      };
    };
  };

  replicate = mk {
    doc = ''
      Create a stream of n copies of a value.

      ```
      replicate : int -> a -> Computation (Step null a)
      ```
    '';
    value = n: x:
      if n <= 0 then done.value null
      else more.value x (replicate.value (n - 1) x);
    tests = {
      "replicate-zero" = {
        expr = (replicate.value 0 "x").value._tag;
        expected = "Done";
      };
      "replicate-head" = {
        expr = (replicate.value 3 "x").value.head;
        expected = "x";
      };
    };
  };

in mk {
  doc = "Stream primitives: done/more/fromList/iterate/range/replicate.";
  value = {
    inherit done more fromList iterate range replicate;
  };
}
