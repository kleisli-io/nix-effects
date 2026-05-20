{ fx, lib, api, ... }:

let
  inherit (fx.binds) bindAttrs;
  inherit (fx.comp) isComp;
  inherit (fx.kernel) pure bind;

  # steps : [null -> M a] -> M a
  #
  # Sequences a list of effectful steps, discarding intermediate values.
  # Each step is called with the previous result; the seed is `pure null`,
  # so the first step receives `null`.
  #
  # Use when only the side effects matter — analogous to Haskell's
  # `sequence_`. This is the original `do` behavior, renamed to free the
  # `do` name for the composable Kleisli pipeline below.
  steps = list: lib.foldl' (acc: step: bind acc step) (pure null) list;

  # do : [a -> b | a -> M b] -> (a -> M b)
  #
  # A composable, lift-aware Kleisli pipeline.
  #
  # Returns a KLEISLI ARROW (a -> M b), not a Computation. This single
  # design choice gives three properties that `steps` and `pipe` lack:
  #
  # 1. COMPOSABLE: the result is itself a Kleisli arrow, so pipelines
  #    combine without re-wrapping:
  #      kleisli (do [f g]) (do [h i])  ==  do [f g h i]
  #
  # 2. DATA-LAST: the input value is the last argument, enabling point-free
  #    style:
  #      map (do [validate enrich]) userIds
  #
  # 3. AUTO-LIFTING: plain functions (a -> b) are promoted to Kleisli
  #    arrows (a -> M b) via `pure`. Monadic functions pass through
  #    unchanged. `isComp` dispatch makes this seamless — callers do not
  #    need to know whether a step is pure or effectful.
  #
  # Relation to existing primitives:
  #   do []        = x: pure x                     (identity Kleisli arrow)
  #   do steps x   = pipe (pure x) (map lift steps)
  #   kleisli f g  = do [f g]                       (when f, g are arrows)
  do_ = list:
    let
      # liftStep promotes a plain (a -> b) into a Kleisli arrow (a -> M b)
      # by inspecting the result: Computations pass through, plain values
      # are wrapped in `pure`. Plain Nix values never carry `_tag`, so the
      # check has no false positives.
      liftStep = f: x:
        let result = f x;
        in if isComp result then result else pure result;
      arrows = builtins.map liftStep list;
    in
    x: builtins.foldl' (acc: f: bind acc f) (pure x) arrows;

  letM_ = attrs: k: bind (bindAttrs attrs) k;

  reexport = src: name: description:
    api.leaf {
      inherit description;
      value = src.${name};
    };
in
{
  scope = {
    steps = api.leaf {
      description = "steps: sequence a list of `Comp` steps left-to-right via `bind`, returning a single composed `Comp`; each step receives the previous result, the seed is `pure null`.";
      signature = "steps : [a -> Comp b] -> Comp b";
      doc = ''
        Use when only the side effects of each step matter — analogous to
        Haskell's `sequence_`. The seed value is `pure null`, so the
        first step's argument is `null`; discard it if the first step is
        producer-shaped (`_: pure x`). An empty list returns `pure null`.

        Prefer `do` for composable, point-free Kleisli pipelines that
        thread values. Prefer `kleisli` when composing two Kleisli
        arrows without an initial value, and `pipe` when threading a
        non-monadic seed through effectful transforms.
      '';
      value = steps;
    };

    do = api.leaf {
      description = "do: build a composable Kleisli arrow `(a -> M b)` from a list of steps; plain functions `(a -> b)` are auto-lifted via `pure`, monadic functions `(a -> M b)` pass through. Apply the result to a seed to obtain a `Comp b`.";
      signature = "do : [a -> b | a -> M b] -> (a -> M b)";
      doc = ''
        Use when steps form a linear pipeline that should remain
        point-free and composable. Because `do` returns a Kleisli arrow,
        two pipelines glue without lambdas:
        `kleisli (do [f g]) (do [h i]) == do [f g h i]`. Data-last
        argument order makes `map (do [validate enrich]) xs` natural.

        Auto-lifting lets pure and effectful steps mix freely — runtime
        dispatch via `isComp` decides whether to thread through `map` or
        `bind`. An empty list gives the identity arrow `x: pure x`.

        Prefer `steps` when discarding intermediate values is intentional
        (effect sequencing). Prefer `kleisli` for a single binary
        composition. Use `letM` when bound values are siblings rather
        than a left-to-right pipeline.
      '';
      value = do_;
    };

    letM = api.leaf {
      description = "letM: `attrs`-based monadic binding — runs `bindAttrs attrs` to gather a record of results, then passes the record to continuation `k` for the next step.";
      signature = "letM : { name = Comp a } -> ({ name = a } -> Comp b) -> Comp b";
      doc = ''
        Use when several independent computations must complete before a
        single dependent step runs — `letM { a = ca; b = cb; } ({ a, b }: ...)`
        replaces a nested `bind ca (a: bind cb (b: ...))` chain with a
        flat record. Field order in the resulting record is unspecified;
        ordering of side effects across fields is determined by
        `bindAttrs`, not by the caller's attribute layout.

        Prefer over `do` when the bound values are siblings rather than a
        left-to-right pipeline. For a single bind, plain `bind` is
        clearer.
      '';
      value = letM_;
    };

    pure = reexport fx.kernel "pure" "Re-export of fx.kernel.pure. See fx.kernel for details.";
    bind = reexport fx.kernel "bind" "Re-export of fx.kernel.bind. See fx.kernel for details.";
    map = reexport fx.kernel "map" "Re-export of fx.kernel.map. See fx.kernel for details.";
    seq = reexport fx.kernel "seq" "Re-export of fx.kernel.seq. See fx.kernel for details.";
    pipe = reexport fx.kernel "pipe" "Re-export of fx.kernel.pipe. See fx.kernel for details.";
    kleisli = reexport fx.kernel "kleisli" "Re-export of fx.kernel.kleisli. See fx.kernel for details.";
    run = reexport fx.trampoline "run" "Re-export of fx.trampoline.run. See fx.trampoline for details.";
    handle = reexport fx.trampoline "handle" "Re-export of fx.trampoline.handle. See fx.trampoline for details.";
  };

  tests = { };
}
