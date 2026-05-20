# Dependency graph evaluator using nix-effects.
# Demonstrates memoization (State), configuration (Reader), and failure (Error).
{ fx }:

let
  inherit (fx) pure bind send handle;

  getCache = key: send "getCache" key;
  setCache = key: value: send "setCache" { inherit key value; };
  getConfig = send "getConfig" null;
  fail = msg: send "fail" msg;
  log = msg: send "log" msg;

  buildNode = node:
    bind (getCache node.name) (cached:
      if cached != null then pure cached
      else
        bind (log "building: ${node.name}") (_:
          bind (buildDeps node.deps) (depResults:
            bind (getConfig) (config:
              let result = node.builder { deps = depResults; inherit config; };
              in if result ? _error
              then fail "build failed: ${node.name}: ${result._error}"
              else bind (setCache node.name result) (_: pure result)))));

  buildDeps = deps:
    let
      go = remaining: acc:
        if remaining == [ ] then pure acc
        else
          let dep = builtins.head remaining; rest = builtins.tail remaining;
          in bind (buildNode dep) (result: go rest (acc // { ${dep.name} = result; }));
    in
    go deps { };

  handlersWithLogging = {
    getCache = { param, state }: { resume = state.cache.${param} or null; inherit state; };
    setCache = { param, state }: { resume = null; state = state // { cache = state.cache // { ${param.key} = param.value; }; }; };
    getConfig = { param, state }: { resume = state.config; inherit state; };
    fail = { param, state }: { abort = { error = param; cache = state.cache; logs = state.logs; }; inherit state; };
    log = { param, state }: { resume = null; state = state // { logs = state.logs ++ [ param ]; }; };
  };

  handlersQuiet = {
    getCache = { param, state }: { resume = state.cache.${param} or null; inherit state; };
    setCache = { param, state }: { resume = null; state = state // { cache = state.cache // { ${param.key} = param.value; }; }; };
    getConfig = { param, state }: { resume = state.config; inherit state; };
    fail = { param, state }: { abort = { error = param; cache = state.cache; }; inherit state; };
    log = { param, state }: { resume = null; inherit state; };
  };

  mkState = graph: { cache = { }; logs = [ ]; config = graph.config or { }; };

  eval = graph: handle { handlers = handlersWithLogging; state = mkState graph; } (buildNode graph.root);
  evalQuiet = graph: handle { handlers = handlersQuiet; state = mkState graph; } (buildNode graph.root);

in
{
  inherit eval evalQuiet buildNode buildDeps;
  graphs = import ./graphs.nix { };
}
