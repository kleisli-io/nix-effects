# nix-unit fixtures for the pure regression-gate functions.
#
# Synthetic `{allocs = {...}}` summaries exercise the joint hard-fail rule
# |Δ| ≥ max(tol·base/1000, floor), the signed blame movers, and the absolute
# floor that stops a tiny-base counter from setting the verdict.
{ lib }:

let
  gate = import ./gate.nix { inherit lib; };
  format = import ./format.nix { inherit lib; };
  measure = import ./measure.nix { inherit lib; };
  inherit (gate) classify stepAxis maxAllocDeltaPermille allocRegressions bytesAggregateDelta;

  mkW = allocs: {
    alloc_deterministic = true;
    inherit allocs;
    cpu = { p50 = 1; p95 = 1; };
    wall = { p50 = 0; p95 = 0; };
    runs = 1;
  };

  # Small-base artifact: a base-3425 counter rises +486‰ on a 1666 absolute
  # move while the million-scale counter barely budges.
  artifactBase = { listConcats = 3425; values = 1000000; };
  artifactCur = { listConcats = 5091; values = 1000050; };

  # Real mover: +10‰ on a 10000 absolute move — must survive the floor.
  realBase = { values = 1000000; };
  realCur = { values = 1010000; };

  # Relocation: a list counter collapses (decrease) while an env counter rises.
  relocBase = { listElements = 12613425; envs = 427326; };
  relocCur = { listElements = 184547; envs = 797732; };

  # Real desc-ind.n1000 heap bytes (faithful rep change): listBytes collapses
  # (skew-binary RAL spine) while values/envs rise — net Σ-bytes +45‰ (~+4.6%),
  # within the generous aggregate tolerance though per-counter movers exceed 5‰.
  descIndBase = { valuesBytes = 144674192; envsBytes = 140370064; setsBytes = 169497664; listBytes = 11827320; };
  descIndCur = { valuesBytes = 161284832; envsBytes = 149340832; setsBytes = 172881504; listBytes = 4250736; };

  # Across-the-board +10%: a real memory regression the aggregate must catch.
  regressBase = { valuesBytes = 100; envsBytes = 100; setsBytes = 100; listBytes = 100; };
  regressCur = { valuesBytes = 110; envsBytes = 110; setsBytes = 110; listBytes = 110; };

  # Deep chain: listBytes collapse dominates, so Σ-bytes goes negative — read as
  # the improvement it is, not a regression.
  deepNBase = { valuesBytes = 100000000; envsBytes = 50000000; setsBytes = 10000000; listBytes = 200000000; };
  deepNCur = { valuesBytes = 110000000; envsBytes = 55000000; setsBytes = 10000000; listBytes = 80000000; };

  # symbolsBytes (code-size) is excluded from the aggregate.
  codeSizeBase = { valuesBytes = 1000; symbolsBytes = 1000; };
  codeSizeCur = { valuesBytes = 1000; symbolsBytes = 500000; };

  classify' = floor: base: cur:
    classify {
      workload = "w";
      baseline = mkW base;
      current = mkW cur;
      cpuBudgetPct = null;
      allocTolerancePermille = 5;
      allocAbsoluteFloor = floor;
    };

  # Isolate the Σ-bytes axis: a huge floor neutralises the per-counter gate so
  # the verdict is set by the aggregate alone.
  classifyBytes = base: cur:
    classify {
      workload = "w";
      baseline = mkW base;
      current = mkW cur;
      cpuBudgetPct = null;
      allocTolerancePermille = 5;
      allocAbsoluteFloor = 999999999;
      allocBytesAggregateTolerancePermille = 50;
    };

  stepProbe = loN: loSteps: hiN: hiSteps:
    { lo = { n = loN; steps = loSteps; }; hi = { n = hiN; steps = hiSteps; }; };
  stepStatus = probe: contractSlope:
    (builtins.head (stepAxis {
      stepProbes = { p = probe; };
      stepSlopes = { p = contractSlope; };
      tolerancePermille = 5;
    })).status;

  gcAt = heap: {
    gc = {
      heapSize = { p50 = heap; p95 = heap; };
      bytes = { p50 = 0; p95 = 0; };
      cycles = { p50 = 0; p95 = 0; };
    };
  };
  classifyHeap = baseHeap: curHeap:
    classify {
      workload = "w";
      baseline = mkW realBase // gcAt baseHeap;
      current = mkW realBase // gcAt curHeap;
      cpuBudgetPct = null;
      allocTolerancePermille = 5;
      allocAbsoluteFloor = 0;
    };

  # Minimal gateResult for serialiser fixtures.
  mdGateResult = stepResults: {
    classifications = [ ];
    hardFails = [ ];
    softWarns = [ ];
    overridden = [ ];
    newWorkloads = [ ];
    retiredWorkloads = [ ];
    inherit stepResults;
    stepFails = builtins.filter (s: s.status == "fail_steps") stepResults;
    pass = true;
  };
  mdMovedSlope = format.emitGateMarkdown {
    gateResult = mdGateResult (stepAxis {
      stepProbes = { "tc.vAppF" = stepProbe 1000 5001 5000 25001; };
      stepSlopes = { "tc.vAppF" = 4; };
      tolerancePermille = 5;
    });
  };
in
{
  maxAllocDeltaPermille = {
    floorExcludesSmallBase = {
      expr = maxAllocDeltaPermille 2000 artifactBase artifactCur;
      expected = 0;
    };
    noFloorIncludesSmallBase = {
      expr = maxAllocDeltaPermille 0 artifactBase artifactCur;
      expected = 486;
    };
    floorKeepsRealMover = {
      expr = maxAllocDeltaPermille 2000 realBase realCur;
      expected = 10;
    };
  };

  allocRegressions = {
    sortedSignedIncludesDecrease = {
      expr = map (m: { inherit (m) field deltaPermille; })
        (allocRegressions relocBase relocCur);
      expected = [
        { field = "listElements"; deltaPermille = -985; }
        { field = "envs"; deltaPermille = 866; }
      ];
    };
  };

  classify = {
    # Per-counter movers are diagnostic only: counter spike + flat Σ-bytes → pass.
    perCounterMoverNowPasses = {
      expr = (classify' 0 artifactBase artifactCur).status;
      expected = "pass";
    };
    # Faithful desc-ind rep change: per-counter movers >5‰, Σ-bytes +45‰ < 50‰ → pass.
    descIndRelocationPasses = {
      expr = (classify' 2000 descIndBase descIndCur).status;
      expected = "pass";
    };
    # Across-the-board Σ-bytes regression still hard-fails.
    bytesRegressionStillFails = {
      expr = (classify' 2000 regressBase regressCur).status;
      expected = "fail_allocs";
    };
    blameAttachedOnPass = {
      expr = map (m: m.field) (classify' 999999999 relocBase relocCur).blame;
      expected = [ "listElements" "envs" ];
    };
  };

  # Step-count work axis: per-level slope vs the declared contract.
  stepAxis = {
    # vAppF-shaped: 4n+1 at n∈{1000,5000} → slope 4, matches the contract → pass.
    flatSlopePasses = {
      expr = stepStatus (stepProbe 1000 4001 5000 20001) 4;
      expected = "pass";
    };
    # A synthetic extra reduction per layer (slope 4→5, +250‰) → fails.
    movedSlopeFails = {
      expr = stepStatus (stepProbe 1000 5001 5000 25001) 4;
      expected = "fail_steps";
    };
    # +1000 steps at both depths: slope still 4 → pass (intercept is not gated).
    interceptWobblePasses = {
      expr = stepStatus (stepProbe 1000 5001 5000 21001) 4;
      expected = "pass";
    };
    # desc-ind-shaped: 193n+147 → slope 193, matches contract → pass.
    descIndSlopePasses = {
      expr = stepStatus (stepProbe 1000 193147 5000 965147) 193;
      expected = "pass";
    };
    # conv-inl-shaped: 2n+1 goals → slope 2, matches contract → pass.
    convInlSlopePasses = {
      expr = stepStatus (stepProbe 1000 2001 5000 10001) 2;
      expected = "pass";
    };
    # An extra sibling goal per layer (slope 2→3, +500‰) → fails.
    convExtraGoalFails = {
      expr = stepStatus (stepProbe 1000 3001 5000 15001) 2;
      expected = "fail_steps";
    };
  };

  # Peak heap is GC-nondeterministic → advisory only, never a hard fail.
  peakHeap = {
    riseWarns = {
      expr = (classifyHeap 100000000 200000000).status;
      expected = "warn_heap";
    };
    riseUnderThresholdPasses = {
      expr = (classifyHeap 100000000 110000000).status;
      expected = "pass";
    };
    dropPasses = {
      expr = (classifyHeap 200000000 100000000).status;
      expected = "pass";
    };
    # Old history JSON carries no gc section — must not warn or crash.
    absentGcPasses = {
      expr = (classify' 0 realBase realBase).status;
      expected = "pass";
    };
    neverBlocksGate = {
      expr =
        let
          g = gate.gate {
            baseline = { results = { w = mkW realBase // gcAt 100000000; }; };
            current = { results = { w = mkW realBase // gcAt 300000000; }; };
            budgets = { };
          };
        in
        { pass = g.pass; warns = builtins.length g.softWarns; };
      expected = { pass = true; warns = 1; };
    };
  };

  summarize = {
    gcThreaded = {
      expr = (measure.summarize [
        { allocs = { values = 1; }; cpu = 1.0; wall = 1; gc = { cycles = 1; bytes = 10; heapSize = 100; }; }
        { allocs = { values = 1; }; cpu = 1.0; wall = 1; gc = { cycles = 3; bytes = 30; heapSize = 300; }; }
      ]).gc.heapSize;
      expected = { p50 = 200; p95 = 300; };
    };
  };

  emitGateMarkdown = {
    stepSectionRendersFail = {
      expr = lib.hasInfix "| tc.vAppF |" mdMovedSlope && lib.hasInfix "FAIL steps" mdMovedSlope;
      expected = true;
    };
    stepSummaryCountsFails = {
      expr = lib.hasInfix "**Step-axis fails**: 1" mdMovedSlope;
      expected = true;
    };
    # No gated probes → no step section, no summary line.
    stepSectionOmittedWhenInert = {
      expr = lib.hasInfix "Step axis" (format.emitGateMarkdown { gateResult = mdGateResult [ ]; });
      expected = false;
    };
  };

  bytesAggregateDelta = {
    relocationNetNeutral = {
      expr = bytesAggregateDelta descIndBase descIndCur;
      expected = 45;
    };
    acrossTheBoardRegression = {
      expr = bytesAggregateDelta regressBase regressCur;
      expected = 100;
    };
    deepNImprovementNegative = {
      expr = bytesAggregateDelta deepNBase deepNCur;
      expected = -291;
    };
    excludesSymbolsBytes = {
      expr = bytesAggregateDelta codeSizeBase codeSizeCur;
      expected = 0;
    };
  };

  classifyBytesAxis = {
    relocationWithinTolPasses = {
      expr = (classifyBytes descIndBase descIndCur).status;
      expected = "pass";
    };
    acrossTheBoardFails = {
      expr = (classifyBytes regressBase regressCur).status;
      expected = "fail_allocs";
    };
    deepNImprovementPasses = {
      expr = (classifyBytes deepNBase deepNCur).status;
      expected = "pass";
    };
  };
}
