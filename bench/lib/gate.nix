# Pure regression-gate function.
#
# `gate { baseline, current, budgets, trailers }` classifies each workload
# present in both runs as pass / hard-fail-allocs / hard-fail-cpu / soft-warn.
# Trailers (Perf-regression: <workload>, <reason>) suppress the matching
# workload's hard-fail into an "overridden" bucket; soft warnings are always
# informational.
#
# Policy:
#   alloc delta > allocTolerancePermille → hard fail  (default 5‰ = 0.5%)
#   cpu.p50 regressed by > budget AND current.cpu.p95 > baseline.cpu.p95
#     → hard fail  (cpu p95 non-overlap is the noise-rejection guard)
#   cpu.p50 regressed in (2%, budget]  → soft warn
#   otherwise → pass
#
# Alloc checks only fire when both baseline.alloc_deterministic and
# current.alloc_deterministic. Non-deterministic workloads gate only on cpu.
{ lib }:

let
  measure = import ./measure.nix { inherit lib; };
  inherit (measure) permilleDelta pctDelta;

  # Max permille delta across every alloc field in `current.allocs` relative
  # to `baseline.allocs` with the same key.
  maxAllocDeltaPermille = baselineAllocs: currentAllocs:
    let
      keys = builtins.attrNames currentAllocs;
      deltas = map
        (k: permilleDelta (baselineAllocs.${k} or 0) currentAllocs.${k})
        keys;
    in
      if builtins.length deltas == 0 then 0
      else builtins.foldl' (acc: d: if d > acc then d else acc) (builtins.head deltas) (builtins.tail deltas);

  # Which alloc fields regressed past tolerance, and by how much. For blame.
  allocRegressions = tolerance: baselineAllocs: currentAllocs:
    let
      keys = builtins.attrNames currentAllocs;
      entries = map
        (k:
          let d = permilleDelta (baselineAllocs.${k} or 0) currentAllocs.${k};
          in { field = k; deltaPermille = d; baseline = baselineAllocs.${k} or 0; current = currentAllocs.${k}; })
        keys;
    in builtins.filter (e: e.deltaPermille > tolerance) entries;

  classify = {
    workload,
    baseline,
    current,
    cpuBudgetPct,                 # Int or null. Null = alloc-only gating.
    allocTolerancePermille,
    allocGated ? true             # When false, alloc regressions are silently
                                  # passed. Used for workloads whose alloc
                                  # count scales with unrelated work (e.g.
                                  # test-count-monotonic suites).
  }:
    let
      bothDeterministic = (baseline.alloc_deterministic or false) && (current.alloc_deterministic or false);
      allocDelta = if bothDeterministic
                   then maxAllocDeltaPermille baseline.allocs current.allocs
                   else 0;
      allocBlame = if bothDeterministic
                   then allocRegressions allocTolerancePermille baseline.allocs current.allocs
                   else [ ];

      cpuDelta = pctDelta baseline.cpu.p50 current.cpu.p50;
      cpuP95NonOverlap = current.cpu.p95 > baseline.cpu.p95;

      allocFailed = allocGated && bothDeterministic && allocDelta > allocTolerancePermille;
      cpuFailed   = cpuBudgetPct != null && cpuDelta > cpuBudgetPct && cpuP95NonOverlap;
      cpuWarn     = cpuBudgetPct != null && cpuDelta > 2 && cpuDelta <= cpuBudgetPct;
    in
      if allocFailed then {
        inherit workload;
        status = "fail_allocs";
        reason = "alloc-count regressed by ${toString allocDelta}‰ (tolerance ${toString allocTolerancePermille}‰)";
        allocDelta_permille = allocDelta;
        blame = allocBlame;
      }
      else if cpuFailed then {
        inherit workload;
        status = "fail_cpu";
        reason = "cpu.p50 regressed by ${toString cpuDelta}% (budget ${toString cpuBudgetPct}%); p95 non-overlapping baseline";
        cpuDelta_pct = cpuDelta;
      }
      else if cpuWarn then {
        inherit workload;
        status = "warn_cpu";
        reason = "cpu.p50 regressed by ${toString cpuDelta}% (under budget but past 2% warn threshold)";
        cpuDelta_pct = cpuDelta;
      }
      else {
        inherit workload;
        status = "pass";
        reason = "";
      };

  gate = {
    baseline,         # { results = { <workload> = <WorkloadSummary>; }; meta ? {}; }
    current,
    budgets,          # { cpu = { <workload> = Int; ... }; allocTolerancePermille = Int; }
    trailers ? [ ],   # [{ workload, reason }]. See gate.nix runner for syntax.
    allocNoiseLimited ? [ ],      # Workloads excluded from alloc gating.
  }:
    let
      overrideMap = builtins.listToAttrs
        (map (t: { name = t.workload; value = t; }) trailers);

      allocNoiseLimitedSet = builtins.listToAttrs
        (map (w: { name = w; value = true; }) allocNoiseLimited);

      currentNames = builtins.attrNames current.results;
      baselineNames = builtins.attrNames baseline.results;
      commonNames = builtins.filter (n: baseline.results ? ${n}) currentNames;

      classifications = map
        (w: classify {
          workload = w;
          baseline = baseline.results.${w};
          current = current.results.${w};
          cpuBudgetPct = budgets.cpu.${w} or null;
          allocTolerancePermille = budgets.allocTolerancePermille or 5;
          allocGated = ! (allocNoiseLimitedSet ? ${w});
        })
        commonNames;

      failures = builtins.filter
        (c: c.status == "fail_allocs" || c.status == "fail_cpu")
        classifications;

      hardFails = builtins.filter
        (c: ! (overrideMap ? ${c.workload}))
        failures;

      overridden = builtins.filter
        (c: overrideMap ? ${c.workload})
        failures;

      softWarns = builtins.filter (c: c.status == "warn_cpu") classifications;

      missingWorkloads = builtins.filter (n: ! (baseline.results ? ${n})) currentNames;
      newWorkloads = missingWorkloads;
      retiredWorkloads = builtins.filter (n: ! (current.results ? ${n})) baselineNames;
    in {
      pass = builtins.length hardFails == 0;
      inherit hardFails softWarns overridden classifications;
      inherit newWorkloads retiredWorkloads;
    };

in { inherit gate classify maxAllocDeltaPermille allocRegressions; }
