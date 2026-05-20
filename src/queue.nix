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
#                     | Identity            -- pure/id continuation (skipped by trampoline)
{ fx, ... }:

let
  leaf = fn: { _tag = "FTCQueue"; _variant = "Leaf"; inherit fn; };

  node = left: right: { _tag = "FTCQueue"; _variant = "Node"; inherit left right; };

  # Identity: a queue containing only the identity (pure) continuation.
  # The trampoline recognizes this variant and produces `pure resumeValue`
  # directly, skipping queue application entirely.
  identity = { _tag = "FTCQueue"; _variant = "Identity"; };

  singleton = fn: leaf fn;

  snoc = q: fn:
    if q._variant == "Identity" then leaf fn
    # Preserve __rawResume flag through queue extension. Mirrors append:
    # effectRotate tags rotation continuations with __rawResume so the
    # outer interpreter routes effectful resumes back through inner
    # scope handlers. kernel.bind snocs onto the rotation continuation
    # queue when a bind chain follows a rotating subcomputation; without
    # this, the flag is lost and deep semantics silently break.
    else if q.__rawResume or false
    then (node q (leaf fn)) // { __rawResume = true; }
    else node q (leaf fn);

  append = q1: q2:
    if q1._variant == "Identity" then q2
    else if q2._variant == "Identity" then q1
    # Preserve __rawResume flag through queue concatenation.
    # effectRotate tags rotation continuations with __rawResume
    # so the outer interpreter routes effectful resumes back
    # through inner scope handlers (deep handler semantics).
    # Without this, fx.bind chains around scope.provide lose
    # the flag and deep semantics silently break.
    else if q1.__rawResume or false
    then (node q1 q2) // { __rawResume = true; }
    else node q1 q2;

  viewl = q:
    if q._variant == "Leaf"
    then { head = q.fn; tail = null; }
    else viewlGo q.left q.right;

  # Rotate the tree leftward to find the leftmost Leaf (amortized O(1)).
  # Fast-path: if left is already a Leaf, return immediately without
  # entering genericClosure. This handles the common case (queues built
  # by a single snoc) with zero overhead.
  # For deeper trees, genericClosure provides stack-safe iteration.
  viewlGo = left: right:
    if left._variant == "Leaf"
    then { head = left.fn; tail = right; }
    else
      let
        steps = builtins.genericClosure {
          startSet = [{ key = 0; _left = left; _right = right; }];
          operator = state:
            if state._left._variant == "Leaf" then []
            else [{ key = state.key + 1;
                    _left = state._left.left;
                    _right = { _tag = "FTCQueue"; _variant = "Node";
                               left = state._left.right; right = state._right; }; }];
        };
        last = builtins.elemAt steps (builtins.length steps - 1);
      in { head = last._left.fn; tail = last._right; };

  qApp = q: x:
    let
      # Iteratively apply Pure-returning continuations (trampoline via genericClosure)
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _queue = q; _val = x; }];
        operator = state:
          let
            vl = viewl state._queue;
            result = vl.head state._val;
          in
          if vl.tail != null && fx.comp.isPure result
          then [{ key = builtins.seq result.value (state.key + 1); _queue = vl.tail; _val = result.value; }]
          else [];
      };
      last = builtins.elemAt steps (builtins.length steps - 1);
      vl = viewl last._queue;
      result = vl.head last._val;
    in
    if vl.tail == null
    then result
    else fx.comp.impure result.effect (append result.queue vl.tail);

in {
  inherit leaf node identity singleton snoc append viewl qApp;

  __docs = {
    _self = {
      description = "FTCQueue (catenable queue, Kiselyov & Ishii 2015): `leaf`/`node`/`singleton`/`snoc`/`append`/`viewl`/`qApp` — O(1) bind on linearly nested computation chains.";
      doc = "FTCQueue (catenable queue, after Kiselyov & Ishii 2015). O(1) `snoc`/`append`, amortized O(1) `viewl`.";
    };

    leaf = {
      description = "leaf: build a singleton FTCQueue containing one continuation; the leaf of the catenable-tree representation.";
      signature = "leaf : (a -> Computation b) -> FTCQueue a b";
      doc = "Create a singleton queue containing one continuation function.";
      tests = {
        "creates-leaf" = {
          expr = (leaf (x: x))._variant;
          expected = "Leaf";
        };
      };
    };

    node = {
      description = "node: join two FTCQueues into a balanced tree node; O(1) concatenation that defers traversal cost to `viewl`.";
      signature = "node : FTCQueue a x -> FTCQueue x b -> FTCQueue a b";
      doc = "Join two queues. O(1) — just creates a tree node; the cost is amortised by `viewl` during deconstruction.";
      tests = {
        "creates-node" = {
          expr = (node (leaf (x: x)) (leaf (x: x)))._variant;
          expected = "Node";
        };
      };
    };

    singleton = {
      description = "singleton: alias for `leaf`; build an FTCQueue from a single continuation function with no nesting.";
      signature = "singleton : (a -> Computation b) -> FTCQueue a b";
      doc = "Create a queue with a single continuation. O(1). Synonym for `leaf`.";
    };

    snoc = {
      description = "snoc: append one continuation to the right end of a queue in O(1); preserves the `__rawResume` rotation flag for deep-handler semantics.";
      signature = "snoc : FTCQueue a b -> (b -> Computation c) -> FTCQueue a c";
      doc = ''
        Append a continuation to the right of the queue. O(1).

        Preserves the `__rawResume` flag through extension so deep-handler
        rotation continuations keep routing effectful resumes back through
        inner-scope handlers.
      '';
    };

    append = {
      description = "append: concatenate two queues in O(1); identity queues short-circuit and the `__rawResume` rotation flag is propagated when present.";
      signature = "append : FTCQueue a b -> FTCQueue b c -> FTCQueue a c";
      doc = ''
        Concatenate two queues. O(1).

        Identity queues short-circuit (return the other side untouched).
        The `__rawResume` flag is preserved so `fx.bind` chains around
        `scope.provide` retain deep-handler semantics.
      '';
    };

    viewl = {
      description = "viewl: extract the leftmost continuation from a queue with amortised O(1) cost via `viewlGo` rotation; returns `{ head, tail }`, `tail = null` for singletons.";
      signature = "viewl : FTCQueue a b -> { head : (a -> Computation b), tail : FTCQueue a b | null }";
      doc = ''
        Extract the leftmost continuation from the queue. Amortized O(1).

        Returns `{ head = fn; tail = queue | null; }` — `tail` is `null`
        when the queue had only one element.
      '';
      tests = {
        "viewl-singleton" = {
          expr = (viewl (leaf (x: x + 1))).tail;
          expected = null;
        };
        "viewl-node-extracts-left" = {
          expr =
            let
              q = node (leaf (x: x + 10)) (leaf (x: x + 20));
              vl = viewl q;
            in vl.head 0;
          expected = 10;
        };
        "viewl-node-has-tail" = {
          expr =
            let
              q = node (leaf (x: x + 10)) (leaf (x: x + 20));
              vl = viewl q;
            in vl.tail != null;
          expected = true;
        };
      };
    };

    qApp = {
      description = "qApp: apply a queue of continuations to a starting value; trampolines pure continuations via `genericClosure` and halts at the first `Impure` result.";
      signature = "qApp : FTCQueue a b -> a -> Computation b";
      doc = ''
        Apply a queue of continuations to a value. Processes continuations
        left-to-right: if a continuation returns `Pure`, feed the value
        to the next continuation. If it returns `Impure`, append the
        remaining queue to the effect's own queue and return.
      '';
      tests = {
        "qApp-singleton-pure" = {
          expr = (qApp (leaf (x: fx.comp.pure (x + 1))) 41).value;
          expected = 42;
        };
        "qApp-chains-pure" = {
          expr =
            let
              q = node
                (leaf (x: fx.comp.pure (x + 10)))
                (leaf (x: fx.comp.pure (x * 2)));
            in (qApp q 1).value;
          expected = 22;  # (1 + 10) * 2
        };
        "qApp-deep-pure-10000" = {
          expr =
            let
              n = 10000;
              q = builtins.foldl' (acc: _:
                snoc acc (x: fx.comp.pure (x + 1))
              ) (leaf (x: fx.comp.pure (x + 1))) (builtins.genList (_: null) (n - 1));
            in (qApp q 0).value;
          expected = 10000;
        };
        "qApp-impure-after-pure-chain" = {
          expr =
            let
              pureQ = builtins.foldl' (acc: _:
                snoc acc (x: fx.comp.pure (x + 1))
              ) (leaf (x: fx.comp.pure (x + 1))) (builtins.genList (_: null) 99);
              impureK = x: fx.comp.impure { tag = "test"; payload = x; } (leaf (y: fx.comp.pure y));
              q = snoc pureQ impureK;
            in (qApp q 0).effect.payload;
          expected = 100;
        };
      };
    };
  };
}
