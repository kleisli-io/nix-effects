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
rec {
  __example = {
    title = "Build Simulator";
    description = "A dependency-graph evaluator with cache, configuration, logging, and failure effects.";
    introduction = ''
      This example models a small build planner. Nodes depend on other nodes,
      builders consume dependency outputs, and handlers provide cache,
      configuration, logging, and failure behavior.

      The graph generators produce the scalable workloads used by the
      benchmark suite.
    '';
    sections = [
      {
        title = "Graph nodes";
        prose = ''
          Nodes are plain Nix records. A builder receives the evaluated
          dependency results and configuration, then returns either a value or
          an error marker.
        '';
        code = ''
          leaf = name: value: {
            inherit name;
            deps = [ ];
            builder = { deps, config }: value;
          };

          sumBuilder = { deps, config }:
            builtins.foldl' (acc: v: acc + v) (config.base or 0)
              (builtins.attrValues deps);
        '';
        tests = [
          "linearGraphBuilds"
          "wideGraphBuilds"
        ];
      }
      {
        title = "Effectful evaluation";
        prose = ''
          The evaluator requests cache reads, cache writes, configuration,
          logging, and failure through effects. Swapping the handler changes
          observability without changing graph traversal.
        '';
        code = ''
          eval = graph:
            handle { handlers = handlersWithLogging; state = mkState graph; }
              (buildNode graph.root);

          evalQuiet = graph:
            handle { handlers = handlersQuiet; state = mkState graph; }
              (buildNode graph.root);
        '';
        tests = [
          "failureReturnsError"
        ];
      }
      {
        title = "Benchmark generators";
        prose = ''
          `graphs.nix` generates linear, wide, diamond, tree, mixed, and
          failing graphs. The benchmark suite imports them from
          `examples/build-sim`.
        '';
        code = ''
          buildSim.graphs.benchmarks.linear500
          buildSim.graphs.benchmarks.diamond10
          buildSim.graphs.benchmarks.mixed_large
        '';
        tests = [ ];
      }
    ];
  };

  inherit eval evalQuiet buildNode buildDeps;
  graphs = import ./graphs.nix { };

  linearGraphBuilds =
    (evalQuiet graphs.benchmarks.linear50).value == 1;

  wideGraphBuilds =
    (evalQuiet graphs.benchmarks.wide50).value == 50;

  failureReturnsError =
    (evalQuiet graphs.benchmarks.linear_fail_early).value.error
      == "build failed: n10: intentional failure at node 10";
}
