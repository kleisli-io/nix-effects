# Synthetic microbenchmarks for diagnosing effect-layer bottlenecks.
#
# Each workload is a pure Nix expression that forces a computation of bounded
# size. `s10k` = 10 000 iterations (quick tier), `s100k` = 100 000 iterations
# (standard tier), `s1m` = 1 000 000 iterations (heavy tier).
{ fx }:

let
  inherit (fx) pure bind send handle;

  mkEffectHeavy = n:
    let
      loop = i: if i >= n then pure i else bind (send "inc" null) (_: loop (i + 1));
      handlers = { inc = { param, state }: { resume = null; state = state + 1; }; };
    in (handle { inherit handlers; state = 0; } (loop 0)).state;

  mkBindHeavy = n:
    let
      comp = builtins.foldl' (acc: _: bind acc (x: pure (x + 1))) (send "init" null) (builtins.genList (x: x) n);
      handlers = { init = { param, state }: { resume = 0; inherit state; }; };
    in (handle { inherit handlers; state = null; } comp).value;

  mkMixed = n:
    let
      loop = i: if i >= n then pure i
        else bind (send "get" null) (x: bind (pure (x + 1)) (y: bind (send "put" y) (_: loop (i + 1))));
      handlers = {
        get = { param, state }: { resume = state; inherit state; };
        put = { param, state }: { resume = null; state = param; };
      };
    in (handle { inherit handlers; state = 0; } (loop 0)).state;

  mkNestedHandlers = depth: iterations:
    let
      comp = builtins.foldl' (acc: _: bind acc (x: bind (send "count" null) (_: pure (x + 1)))) (pure 0) (builtins.genList (x: x) iterations);
      wrapHandler = level: innerComp: handle {
        handlers.count = { param, state }: { resume = null; state = state + 1; };
        state = 0;
        return = value: state: pure { inherit value; level = level; count = state; };
      } innerComp;
      wrapped = builtins.foldl' (acc: level: wrapHandler level acc) comp (builtins.genList (x: x) depth);
    in (handle { handlers = {}; state = null; } wrapped).value;

  mkDeepChains = n:
    let comp = builtins.foldl' (acc: _: bind acc (x: pure (x + 1))) (pure 0) (builtins.genList (x: x) n);
    in comp.value;

  mkRawGC = n:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; value = 0; }];
        operator = step: if step.key >= n then []
          else let newValue = step.value + 1; in [{ key = builtins.deepSeq newValue (step.key + 1); value = newValue; }];
      };
    in (builtins.elemAt steps (builtins.length steps - 1)).value;

in {
  effectHeavy = {
    s10k  = mkEffectHeavy 10000;
    s100k = mkEffectHeavy 100000;
    s1m   = mkEffectHeavy 1000000;
  };
  bindHeavy = {
    s10k  = mkBindHeavy 10000;
    s100k = mkBindHeavy 100000;
    s1m   = mkBindHeavy 1000000;
  };
  mixed = {
    s10k  = mkMixed 10000;
    s100k = mkMixed 100000;
    s1m   = mkMixed 1000000;
  };
  nestedHandlers = {
    d3_i1k   = mkNestedHandlers 3 1000;
    d5_i1k   = mkNestedHandlers 5 1000;
    d10_i100 = mkNestedHandlers 10 100;
  };
  deepChains = {
    s10k = mkDeepChains 10000;
    s50k = mkDeepChains 50000;
  };
  rawGC = {
    s10k  = mkRawGC 10000;
    s100k = mkRawGC 100000;
    s1m   = mkRawGC 1000000;
  };
}
