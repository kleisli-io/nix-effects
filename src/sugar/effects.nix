{ fx, lib, ... }:
let
  inherit (fx.binds) bindAttrs;
  inherit (fx.comp) isComp;
  inherit (fx.kernel) pure bind map;

  # steps : [null -> M a] -> M a
  #
  # Sequences a list of effectful steps, discarding intermediate values.
  # Each step is called with `null`; the previous result is ignored.
  # Starts from `pure null` and threads through bind.
  #
  # Use this when you only care about the side-effects of each step,
  # not the values they produce — analogous to Haskell's `sequence_`.
  #
  # Renamed from `do` to free that name for the composable pipeline below.
  # The semantics are identical to the old `do`.
  steps = list: lib.foldl' (acc: step: bind acc step) (pure null) list;

  # do : [a -> b | a -> M b] -> (a -> M b)
  #
  # A composable, lift-aware Kleisli pipeline.
  #
  # Returns a KLEISLI ARROW (a -> M b), not a Computation. This single
  # design choice gives three properties that the old `do` (now `steps`)
  # and `pipe` both lack:
  #
  # 1. COMPOSABLE
  #    The result is itself a Kleisli arrow, so pipelines combine with
  #    `kleisli` or nest inside other `do` calls without re-wrapping:
  #
  #      kleisli (do [f g]) (do [h i])  ==  do [f g h i]
  #
  # 2. DATA-LAST
  #    Unlike `pipe` (init-first) and `lib.pipe` (data-first), the input
  #    value is the last argument, enabling point-free style:
  #
  #      map (do [validate enrich]) userIds   # no lambda needed
  #
  #    Contrast with `pipe` which forces: x: pipe (pure x) [validate enrich]
  #
  # 3. AUTO-LIFTING (the Scala for-comprehension / Haskell do-notation analogy)
  #    Plain functions (a -> b) are silently promoted to Kleisli arrows
  #    (a -> M b) via `pure`. Monadic functions pass through unchanged.
  #    The caller does not need to know whether a step is pure or effectful —
  #    the machinery decides whether to `.map` (plain) or `.flatMap` (monadic):
  #
  #      do [
  #        (x: x + 1)           # plain:   auto-lifted to a -> pure (a + 1)
  #        (x: send "log" x)    # monadic: Kleisli arrow, passes through
  #        (x: pure (x * 2))    # monadic: already in M, passes through
  #      ]
  #
  # Relation to existing primitives:
  #   do []        =  x: pure x        (identity Kleisli arrow, same as `pure`)
  #   do steps x   =  pipe (pure x) (map liftStep steps)
  #   kleisli f g  =  do [f g]         (when f, g are already Kleisli arrows)
  #   steps effs   =  do (map (e: _: e null) effs) null  (old `do` is a special case)
  do = list:
    let
      # liftStep promotes a plain (a -> b) into a Kleisli arrow (a -> M b).
      # It evaluates f x and inspects the result:
      #   - Computation (Pure/Impure _tag present) -> use as-is (flatMap path)
      #   - plain Nix value                        -> wrap in pure (map path)
      # Plain Nix values never carry _tag, so this check has no false positives.
      liftStep = f: x:
        let result = f x;
        in if isComp result then result else pure result;

      # Build arrows list by manually lifting each step.
      # This avoids dependency on `map` which may not be in scope yet.
      arrows = builtins.map liftStep list;
    in
    # The returned lambda IS the Kleisli arrow: a -> M b.
    # builtins.foldl' (strict) avoids building a chain of unevaluated thunks.
    # Starting from `pure x` seeds the fold with the input value in M,
    # matching exactly what `pipe (pure x) arrows` would do.
    x: builtins.foldl' (acc: f: bind acc f) (pure x) arrows;

  letM = attrs: k: bind (bindAttrs attrs) k;

in {
  scope = { 
    inherit steps do letM;
    inherit (fx.kernel) pure bind map seq pipe kleisli;
    inherit (fx.trampoline) run handle;
  };
  tests = {};
}
