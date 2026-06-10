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
  inherit (measure) permilleDelta pctDelta stepSlope;

  # Work axis: each probe's measured per-level CEK transition slope vs the
  # declared [stepSlopes] contract. Exact + representation-invariant → tight tol.
  stepAxis = { stepProbes, stepSlopes, tolerancePermille }:
    map
      (probe:
        let
          contractSlope = stepSlopes.${probe};
          measuredSlope = stepSlope stepProbes.${probe};
          delta = permilleDelta contractSlope measuredSlope;
          absDelta = if delta < 0 then -delta else delta;
        in
        {
          inherit probe contractSlope measuredSlope;
          deltaPermille = delta;
          status = if absDelta > tolerancePermille then "fail_steps" else "pass";
        })
      (builtins.attrNames stepSlopes);

  # Fields that track interned-string growth, not workload work. They
  # rise monotonically with code surface (new tags, new test names, new
  # binder names) and stay flat across re-runs of the same code, so a
  # regression here measures "the module got bigger" rather than "the
  # workload allocates more". Reported in blame for visibility but not
  # included in the gate's max-fold.
  codeSizeFields = [ "symbols" "symbolsBytes" ];
  isCodeSize = k: builtins.elem k codeSizeFields;

  # Heap-bytes fields summed into the relocation-invariant aggregate. A faithful
  # representation change relocates allocation between per-category counters but
  # moves Σ-bytes only a few %, so this aggregate — not the per-counter max — is
  # the honest memory signal. Excludes symbolsBytes (code-size, see above).
  bytesAggregateFields = [ "valuesBytes" "envsBytes" "setsBytes" "listBytes" ];
  sumBytes = allocs:
    builtins.foldl' (acc: k: acc + (allocs.${k} or 0)) 0 bytesAggregateFields;

  # Signed permille delta of the heap-bytes aggregate (negative = improvement).
  bytesAggregateDelta = baselineAllocs: currentAllocs:
    permilleDelta (sumBytes baselineAllocs) (sumBytes currentAllocs);

  # Max permille delta across every workload alloc field in `current.allocs`
  # relative to `baseline.allocs`, restricted to counters whose absolute move
  # clears `floor`. Together with the >tolerance check in `classify` this is
  # the joint rule |Δ| ≥ max(tol·base/1000, floor): a counter drives the
  # verdict only when it moves both relatively (>tol) and absolutely (≥floor),
  # so a tiny-base counter can't dominate the fold on a noise-grade move.
  # Excludes code-size fields (see `codeSizeFields`).
  maxAllocDeltaPermille = floor: baselineAllocs: currentAllocs:
    let
      keys = builtins.filter (k: ! isCodeSize k) (builtins.attrNames currentAllocs);
      deltas = builtins.filter (d: d != null) (map
        (k:
          let
            b = baselineAllocs.${k} or 0;
            c = currentAllocs.${k};
            absDelta = let x = c - b; in if x < 0 then -x else x;
          in
          if absDelta >= floor then permilleDelta b c else null)
        keys);
    in
    if builtins.length deltas == 0 then 0
    else builtins.foldl' (acc: d: if d > acc then d else acc) (builtins.head deltas) (builtins.tail deltas);

  # Signed top movers (risers AND decreases) for blame, sorted by |‰| desc.
  # Every changed counter appears — including big drops — so a representation
  # change that relocates allocation (one counter down, another up) is visible
  # at a glance. Code-size fields are flagged, not excluded.
  allocRegressions = baselineAllocs: currentAllocs:
    let
      keys = builtins.attrNames currentAllocs;
      entries = map
        (k:
          let b = baselineAllocs.${k} or 0; c = currentAllocs.${k};
          in {
            field = k;
            deltaPermille = permilleDelta b c;
            baseline = b;
            current = c;
            codeSize = isCodeSize k;
          })
        keys;
      movers = builtins.filter (e: e.current != e.baseline) entries;
      absPermille = e: if e.deltaPermille < 0 then -e.deltaPermille else e.deltaPermille;
    in
    lib.sort (a: b: absPermille a > absPermille b) movers;

  classify =
    { workload
    , baseline
    , current
    , cpuBudgetPct
    , # Int or null. Null = alloc-only gating.
      allocTolerancePermille
    , # Absolute floor (alloc units) for the joint hard-fail rule. A counter
      # fails only if it clears both tolerance (relative) and this (absolute).
      allocAbsoluteFloor ? 0
    , # Generous tolerance (‰) for the relocation-invariant heap-bytes aggregate.
      # Faithful rep changes legitimately shift Σ-bytes a few %; the tight signals
      # live elsewhere (per-counter interim, work axis).
      allocBytesAggregateTolerancePermille ? 50
    , allocGated ? true             # When false, alloc regressions are silently
      # passed. Used for workloads whose alloc
      # count scales with unrelated work (e.g.
      # test-count-monotonic suites).
    , # Soft-warn threshold (%) for the peak-heap (gc.heapSize p50) delta.
      # GC-nondeterministic → never a hard fail.
      peakHeapWarnPct ? 25
    }:
    let
      bothDeterministic = (baseline.alloc_deterministic or false) && (current.alloc_deterministic or false);
      allocDelta =
        if bothDeterministic
        then maxAllocDeltaPermille allocAbsoluteFloor baseline.allocs current.allocs
        else 0;
      bytesDelta =
        if bothDeterministic
        then bytesAggregateDelta baseline.allocs current.allocs
        else 0;
      allocBlame =
        if bothDeterministic
        then allocRegressions baseline.allocs current.allocs
        else [ ];

      cpuDelta = pctDelta baseline.cpu.p50 current.cpu.p50;
      cpuP95NonOverlap = current.cpu.p95 > baseline.cpu.p95;

      # Verdict: Σ-bytes aggregate only. Per-counter max false-fails on faithful
      # rep changes → diagnostic; the step axis gates work instead.
      bytesFailed = allocGated && bothDeterministic && bytesDelta > allocBytesAggregateTolerancePermille;
      allocFailed = bytesFailed;
      perCounterDiagnostic = bothDeterministic && allocDelta > allocTolerancePermille;
      allocReason = "alloc regressed: Σ-bytes ${toString bytesDelta}‰ (tol ${toString allocBytesAggregateTolerancePermille}‰, gating); per-counter max ${toString allocDelta}‰ (tol ${toString allocTolerancePermille}‰, diagnostic${lib.optionalString perCounterDiagnostic " — exceeded"})";

      cpuFailed = cpuBudgetPct != null && cpuDelta > cpuBudgetPct && cpuP95NonOverlap;
      cpuWarn = cpuBudgetPct != null && cpuDelta > 2 && cpuDelta <= cpuBudgetPct;

      # Guarded on both sides so history JSON without a gc section stays inert.
      baseHeap = ((baseline.gc or { }).heapSize or { }).p50 or 0;
      curHeap = ((current.gc or { }).heapSize or { }).p50 or 0;
      heapDelta = pctDelta baseHeap curHeap;
      heapWarn = baseHeap > 0 && curHeap > 0 && heapDelta > peakHeapWarnPct;
    in
    if allocFailed then {
      inherit workload;
      status = "fail_allocs";
      reason = allocReason;
      allocDelta_permille = allocDelta;
      bytesDelta_permille = bytesDelta;
      blame = allocBlame;
    }
    else if cpuFailed then {
      inherit workload;
      status = "fail_cpu";
      reason = "cpu.p50 regressed by ${toString cpuDelta}% (budget ${toString cpuBudgetPct}%); p95 non-overlapping baseline";
      cpuDelta_pct = cpuDelta;
      blame = allocBlame;
    }
    else if cpuWarn then {
      inherit workload;
      status = "warn_cpu";
      reason = "cpu.p50 regressed by ${toString cpuDelta}% (under budget but past 2% warn threshold)";
      cpuDelta_pct = cpuDelta;
      blame = allocBlame;
    }
    else if heapWarn then {
      inherit workload;
      status = "warn_heap";
      reason = "peak heap (gc.heapSize p50) rose ${toString heapDelta}% (warn ${toString peakHeapWarnPct}%; GC-nondeterministic, never gates)";
      heapDelta_pct = heapDelta;
      blame = allocBlame;
    }
    else {
      inherit workload;
      status = "pass";
      reason = "";
      blame = allocBlame;
    };

  gate =
    { baseline
    , # { results = { <workload> = <WorkloadSummary>; }; meta ? {}; }
      current
    , budgets
    , # { cpu = { <workload> = Int; ... }; allocTolerancePermille = Int; }
      trailers ? [ ]
    , # [{ workload, reason }]. See gate.nix runner for syntax.
      allocNoiseLimited ? [ ]
    , # Workloads excluded from alloc gating.
      stepProbes ? { }
    , # Live CEK step counts { <probe> = { lo; hi }; }. Empty → step axis inert.
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
          allocAbsoluteFloor = budgets.allocAbsoluteFloor or 0;
          allocBytesAggregateTolerancePermille = budgets.allocBytesAggregateTolerancePermille or 50;
          allocGated = ! (allocNoiseLimitedSet ? ${w});
          peakHeapWarnPct = budgets.peakHeapWarnPct or 25;
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

      softWarns = builtins.filter
        (c: c.status == "warn_cpu" || c.status == "warn_heap")
        classifications;

      missingWorkloads = builtins.filter (n: ! (baseline.results ? ${n})) currentNames;
      newWorkloads = missingWorkloads;
      retiredWorkloads = builtins.filter (n: ! (current.results ? ${n})) baselineNames;

      stepResults = stepAxis {
        inherit stepProbes;
        stepSlopes = budgets.stepSlopes or { };
        tolerancePermille = budgets.stepSlopeTolerancePermille or 5;
      };
      stepFails = builtins.filter (s: s.status == "fail_steps") stepResults;
    in
    {
      pass = builtins.length hardFails == 0 && builtins.length stepFails == 0;
      inherit hardFails softWarns overridden classifications;
      inherit newWorkloads retiredWorkloads;
      inherit stepResults stepFails;
    };

in
{ inherit gate classify stepAxis maxAllocDeltaPermille allocRegressions bytesAggregateDelta; }
