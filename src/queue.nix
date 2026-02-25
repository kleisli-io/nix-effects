# nix-effects FTCQueue: Fast Type-aligned Catenable Queue
#
# Note: "Type-aligned" is a static property from the Haskell original
# (types in the queue enforce input/output agreement via GADTs).
# In Nix, this is a plain catenable queue of untyped functions.
#
# From Kiselyov & Ishii (2015), Section 3.1. A tree-structured queue of
# continuation functions, giving O(1) singleton, snoc, and append, with
# amortized O(1) left-edge deconstruction (viewl).
#
# This replaces naive continuation composition in bind, turning
# left-nested bind chains from O(n²) to O(n) total.
#
#   data FTCQueue a b = Leaf (a -> Comp b)
#                     | Node (FTCQueue a x) (FTCQueue x b)
{ api, ... }:

let
  inherit (api) mk;

  # -- Constructors --

  leaf = mk {
    doc = "Create a singleton queue containing one continuation function.";
    value = fn: { _tag = "FTCQueue"; _variant = "Leaf"; inherit fn; };
    tests = {
      "creates-leaf" = {
        expr = (leaf.value (x: x))._variant;
        expected = "Leaf";
      };
    };
  };

  node = mk {
    doc = "Join two queues. O(1) — just creates a tree node.";
    value = left: right: { _tag = "FTCQueue"; _variant = "Node"; inherit left right; };
    tests = {
      "creates-node" = {
        expr = (node.value (leaf.value (x: x)) (leaf.value (x: x)))._variant;
        expected = "Node";
      };
    };
  };

  # -- Operations --

  singleton = mk {
    doc = "Create a queue with a single continuation. O(1).";
    value = fn: leaf.value fn;
  };

  snoc = mk {
    doc = "Append a continuation to the right of the queue. O(1).";
    value = q: fn: node.value q (leaf.value fn);
  };

  append = mk {
    doc = "Concatenate two queues. O(1).";
    value = q1: q2: node.value q1 q2;
  };

  # -- Deconstruction --

  viewl = mk {
    doc = ''
      Extract the leftmost continuation from the queue. Amortized O(1).

      ```
      Returns { head = fn; tail = queue | null; }
      ```

      `tail` is null if the queue had only one element.
    '';
    value = q:
      if q._variant == "Leaf"
      then { head = q.fn; tail = null; }
      else viewlGo q.left q.right;
    tests = {
      "viewl-singleton" = {
        expr = (viewl.value (leaf.value (x: x + 1))).tail;
        expected = null;
      };
      "viewl-node-extracts-left" = {
        expr =
          let
            q = node.value (leaf.value (x: x + 10)) (leaf.value (x: x + 20));
            vl = viewl.value q;
          in vl.head 0;
        expected = 10;
      };
      "viewl-node-has-tail" = {
        expr =
          let
            q = node.value (leaf.value (x: x + 10)) (leaf.value (x: x + 20));
            vl = viewl.value q;
          in vl.tail != null;
        expected = true;
      };
    };
  };

  # Internal helper for viewl tree rotation (trampolined via genericClosure)
  viewlGo = left: right:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _left = left; _right = right; }];
        operator = state:
          if state._left._variant == "Leaf"
          then []
          else [{ key = state.key + 1; _left = state._left.left; _right = node.value state._left.right state._right; }];
      };
      last = builtins.elemAt steps (builtins.length steps - 1);
    in { head = last._left.fn; tail = last._right; };

  # -- Queue application --

  qApp = mk {
    doc = ''
      Apply a queue of continuations to a value. Processes continuations
      left-to-right: if a continuation returns Pure, feed the value to the
      next continuation. If it returns Impure, append the remaining queue
      to the effect's own queue and return.
    '';
    value = q: x:
      let
        # Iteratively apply Pure-returning continuations (trampoline via genericClosure)
        steps = builtins.genericClosure {
          startSet = [{ key = 0; _queue = q; _val = x; }];
          operator = state:
            let
              vl = viewl.value state._queue;
              result = vl.head state._val;
            in
            if vl.tail != null && result._tag == "Pure"
            then [{ key = builtins.seq result.value (state.key + 1); _queue = vl.tail; _val = result.value; }]
            else [];
        };
        last = builtins.elemAt steps (builtins.length steps - 1);
        vl = viewl.value last._queue;
        result = vl.head last._val;
      in
      if vl.tail == null
      then result
      else {
        _tag = "Impure";
        inherit (result) effect;
        queue = append.value result.queue vl.tail;
      };
    tests = {
      "qApp-singleton-pure" = {
        expr = (qApp.value (leaf.value (x: { _tag = "Pure"; value = x + 1; })) 41).value;
        expected = 42;
      };
      "qApp-chains-pure" = {
        expr =
          let
            q = node.value
              (leaf.value (x: { _tag = "Pure"; value = x + 10; }))
              (leaf.value (x: { _tag = "Pure"; value = x * 2; }));
          in (qApp.value q 1).value;
        expected = 22;  # (1 + 10) * 2
      };
      "qApp-deep-pure-10000" = {
        expr =
          let
            n = 10000;
            q = builtins.foldl' (acc: _:
              snoc.value acc (x: { _tag = "Pure"; value = x + 1; })
            ) (leaf.value (x: { _tag = "Pure"; value = x + 1; })) (builtins.genList (_: null) (n - 1));
          in (qApp.value q 0).value;
        expected = 10000;
      };
      "qApp-impure-after-pure-chain" = {
        expr =
          let
            pureQ = builtins.foldl' (acc: _:
              snoc.value acc (x: { _tag = "Pure"; value = x + 1; })
            ) (leaf.value (x: { _tag = "Pure"; value = x + 1; })) (builtins.genList (_: null) 99);
            impureK = x: { _tag = "Impure"; effect = { tag = "test"; payload = x; }; queue = leaf.value (y: { _tag = "Pure"; value = y; }); };
            q = snoc.value pureQ impureK;
          in (qApp.value q 0).effect.payload;
        expected = 100;
      };
    };
  };

in mk {
  doc = "FTCQueue (catenable queue, after Kiselyov & Ishii 2015). O(1) snoc/append, amortized O(1) viewl.";
  value = {
    inherit leaf node singleton snoc append viewl qApp;
  };
}
