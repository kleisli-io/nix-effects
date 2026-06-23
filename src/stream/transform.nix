# nix-effects stream/transform: Stream transformation combinators
#
# Pure transformations on streams: map and filter.
# These produce new streams by transforming or selecting elements.
{ fx, api, ... }:
let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  smap = f: stream:
    bind stream (step:
      if step._tag == "Done" then pure step
      else pure { _tag = "More"; head = f step.head; tail = smap f step.tail; });

  # advanceUntil: iterative (stack-safe) skip via genericClosure.
  # Walks the stream until pred is satisfied or the stream is exhausted.
  # Returns { done = true; rest = <Done computation>; } | { done = false; head = h; tail = t; }
  # Precondition: stream is Pure-encoded (every stream source here produces Pure nodes);
  # advanceUntil reads `.value` to advance iteratively without interpretation.
  advanceUntil = pred: stream:
    let
      walked = builtins.genericClosure {
        startSet = [ { key = 0; cur = stream; out = null; } ];
        operator = st:
          if st.out != null then [ ]
          else
            let step = st.cur.value; in
            if step._tag == "Done"
            then [ { key = st.key + 1; cur = st.cur; out = { done = true; rest = st.cur; }; } ]
            else if pred step.head
            then [ { key = st.key + 1; cur = st.cur; out = { done = false; head = step.head; tail = step.tail; }; } ]
            else [ { key = st.key + 1; cur = step.tail; out = null; } ];
      };
      final = builtins.elemAt walked (builtins.length walked - 1);
    in
    final.out;

  sfilter = pred: stream:
    let r = advanceUntil pred stream; in
    if r.done
    then r.rest
    else pure { _tag = "More"; head = r.head; tail = sfilter pred r.tail; };

  scanl = f: z: stream:
    bind stream (step:
      if step._tag == "Done" then core.more z (core.done null)
      else
        let next = f z step.head;
        in pure { _tag = "More"; head = z; tail = scanl f next step.tail; });

  flatMap = f: stream:
    # advanceUntil iteratively skips elements whose inner stream f(x) is empty
    # (Done), consuming no stack.  Once a non-empty inner is found, concat is
    # lazy (stack-safe) and the recursive flatMap sits under its lazy tail →
    # O(1) stack per non-empty inner.  f is evaluated twice per emitted head
    # (once in isEmpty pred, once in concat) — acceptable.
    let
      isEmpty = s: s.value._tag == "Done";
      r = advanceUntil (x: !(isEmpty (f x))) stream;
    in
    if r.done
    then r.rest
    else fx.stream.combine.concat (f r.head) (flatMap f r.tail);

in
api.namespace {
  description = "Stream transformations: `map`/`filter` plus `scanl`/`flatMap` — pure rewrites that produce new streams from existing ones.";
  doc = "Stream transformations: map, filter, scanl, flatMap.";
  value = {
    map = api.leaf {
      value = smap;
      description = "smap (exported as `map`): map a function over each element of a stream; the structure of `More`/`Done` steps is preserved.";
      signature = "smap : (a -> b) -> Computation (Step r a) -> Computation (Step r b)";
      doc = ''
        Map a function over each element of a stream. Exposed as `map` at
        the module's top-level.
      '';
      tests = {
        "map-done" = {
          expr =
            let s = smap (x: x * 2) (core.done null);
            in (bind s (step: pure step._tag)).value;
          expected = "Done";
        };
      };
    };

    filter = api.leaf {
      value = sfilter;
      description = "sfilter (exported as `filter`): keep only elements that satisfy the predicate; failing elements are dropped silently with no blame.";
      signature = "sfilter : (a -> Bool) -> Computation (Step r a) -> Computation (Step r a)";
      doc = ''
        Keep only elements satisfying a predicate. Exposed as `filter` at
        the module's top-level.
      '';
      tests = {
        "filter-done" = {
          expr =
            let s = sfilter (x: x > 0) (core.done null);
            in (bind s (step: pure step._tag)).value;
          expected = "Done";
        };
      };
    };

    scanl = api.leaf {
      value = scanl;
      description = "scanl: emit a running left-fold; for each input element, emit the accumulator before combining with the element to advance.";
      signature = "scanl : (b -> a -> b) -> b -> Computation (Step r a) -> Computation (Step r b)";
      doc = ''
        Accumulate a running fold over the stream, yielding each
        intermediate accumulator value.
      '';
    };

    flatMap = api.leaf {
      value = flatMap;
      description = "flatMap: apply `f` returning a stream to each element and flatten via `concat`; expands one input element into zero or more outputs.";
      signature = "flatMap : (a -> Computation (Step r b)) -> Computation (Step r a) -> Computation (Step r b)";
      doc = ''
        Apply a function that returns a stream to each element, then
        flatten the resulting streams with `concat`.
      '';
      tests = {
        "flatMap-expands-elements" = {
          expr =
            let s = flatMap (x: core.fromList [ x (x + 1) ]) (core.fromList [ 1 3 ]);
            in (fx.stream.reduce.toList s).value;
          expected = [ 1 2 3 4 ];
        };
        "flatMap-done" = {
          expr =
            let s = flatMap (x: core.fromList [ x ]) (core.done null);
            in (bind s (step: pure step._tag)).value;
          expected = "Done";
        };
      };
    };

  };
}
