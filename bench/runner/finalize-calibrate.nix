# Calibration post-processor.
#
# Reads a run history JSON produced by run.nix with a large `--runs` count
# (typically 20–50) and emits a budgets TOML proposal.
#
# Budget model (per workload):
#   noise_p95_pct = ceil((cpu.p95 - cpu.p50) / cpu.p50 * 100)
#   cpu_budget    = ceil(1.5 * noise_p95_pct), floor 3%.
#
# The floor exists because tiny-sample noise measurement understates true
# variance; empirically a 3% minimum keeps flaky workloads out of the
# always-fail bucket without hiding real regressions.
#
# `existingBudgetsPath` is the canonical `budgets.toml` (if it exists).
# Two exclusion arrays round-trip through calibration so re-running does
# not silently drop the declarations:
#
#   noiseLimited      — workloads excluded from cpu gating. Emitted TOML
#                       also skips them in the `[cpu]` section, since a
#                       budget for a noise-limited workload is worthless.
#   allocNoiseLimited — workloads excluded from alloc gating because
#                       their alloc count scales with unrelated work
#                       (e.g. test-count-monotonic suites). Cpu budgets
#                       still emitted for them — orthogonal dimension.
#
# Both arrays are validated against `bench.meta.tiers` so typos or stale
# names after a workload rename fail loudly at calibration time.
#
# The emitted TOML is a *proposal*; human review + `budgets.toml` commit
# is expected before CI uses it.
{ runPath, benchPath, existingBudgetsPath ? null, minBudget ? 3 }:

let
  run = builtins.fromJSON (builtins.readFile runPath);

  # Authoritative workload registry — validated against this, not the
  # current run's results, because `--filter` may narrow a calibration
  # to a subset of workloads while the exclusion arrays remain global.
  bench = import benchPath { };
  knownWorkloads = builtins.attrNames bench.meta.tiers;

  existing = if existingBudgetsPath == null
             then { }
             else builtins.fromTOML (builtins.readFile existingBudgetsPath);

  noiseLimited = existing.noiseLimited or [ ];
  allocNoiseLimited = existing.allocNoiseLimited or [ ];

  # Both exclusion arrays must name known bench workloads. A typo or
  # stale name (post-rename) would otherwise silently suppress nothing;
  # fail loudly instead.
  unknownNoiseLimited =
    builtins.filter (w: ! (builtins.elem w knownWorkloads)) noiseLimited;
  unknownAllocNoiseLimited =
    builtins.filter (w: ! (builtins.elem w knownWorkloads)) allocNoiseLimited;

  isNoiseLimited = w: builtins.elem w noiseLimited;

  # Ceil of (x * 100 / y) done in int: used for (p95-p50)/p50.
  ceilPct = num: den:
    if den == 0 then 0
    else
      let
        q = (num * 100) / den;
        r = (num * 100) - q * den;
      in if r > 0 then q + 1 else q;

  budgetFor = w: r:
    let
      p50ms = builtins.floor (r.cpu.p50 * 1000);
      p95ms = builtins.floor (r.cpu.p95 * 1000);
      raw = ceilPct (p95ms - p50ms) (if p50ms == 0 then 1 else p50ms);
      scaled = let s = raw * 15; in if s / 10 * 10 == s then s / 10 else s / 10 + 1;
    in if scaled < minBudget then minBudget else scaled;

  allWorkloads = builtins.attrNames run.results;
  cpuEntries = builtins.filter (w: ! (isNoiseLimited w)) allWorkloads;
  noiseEntries = builtins.filter isNoiseLimited allWorkloads;

  cpuBody =
    let
      lines = map
        (w: ''"${w}" = ${toString (budgetFor w run.results.${w})}'')
        cpuEntries;
    in builtins.concatStringsSep "\n" lines;

  noiseLimitedBlock =
    if noiseLimited == [ ] then ""
    else
      let
        items = map (w: ''  "${w}",'') noiseLimited;
      in ''

        # Workloads whose cpu.p95 spread is structurally noise-limited
        # (small-workload relative-variance artifacts or GC jitter on
        # specific DAG shapes). Excluded from cpu gating; alloc-deterministic
        # gating still applies at 0.5‰ tolerance.
        noiseLimited = [
        ${builtins.concatStringsSep "\n" items}
        ]
      '';

  allocNoiseLimitedBlock =
    if allocNoiseLimited == [ ] then ""
    else
      let
        items = map (w: ''  "${w}",'') allocNoiseLimited;
      in ''

        # Workloads whose alloc-count regresses monotonically with
        # unrelated work (e.g. test suites that grow with every feature
        # added to any module). Excluded from alloc gating because any
        # alloc delta on these workloads is dominated by test-count
        # growth, not by regressions in the code under test. Still
        # measured and recorded in bench runs for audit; simply not
        # CI-blocking.
        allocNoiseLimited = [
        ${builtins.concatStringsSep "\n" items}
        ]
      '';

  toml = ''
    # Perf budgets generated from calibration run '${run.name}'.
    # Runs per workload: ${toString run.runsPerWorkload}
    # Nix: ${run.nix}
    # System: ${run.system}
    # Timestamp: ${run.timestamp}

    allocTolerancePermille = 5
    ${noiseLimitedBlock}${allocNoiseLimitedBlock}
    [cpu]
    ${cpuBody}
  '';

  summary =
    let
      cpuRows = map
        (w:
          let
            r = run.results.${w};
            p50 = builtins.floor (r.cpu.p50 * 1000);
            p95 = builtins.floor (r.cpu.p95 * 1000);
            b = budgetFor w r;
          in "  ${w}: p50=${toString p50}ms p95=${toString p95}ms budget=${toString b}%")
        cpuEntries;
      noiseRows = map
        (w:
          let
            r = run.results.${w};
            p50 = builtins.floor (r.cpu.p50 * 1000);
            p95 = builtins.floor (r.cpu.p95 * 1000);
          in "  ${w}: p50=${toString p50}ms p95=${toString p95}ms budget=N/A (noise-limited)")
        noiseEntries;
    in builtins.concatStringsSep "\n" (cpuRows ++ noiseRows);

in
  if unknownNoiseLimited != [ ]
  then throw "finalize-calibrate: noiseLimited contains unknown workloads (typo?): ${builtins.concatStringsSep ", " unknownNoiseLimited}"
  else if unknownAllocNoiseLimited != [ ]
  then throw "finalize-calibrate: allocNoiseLimited contains unknown workloads (typo?): ${builtins.concatStringsSep ", " unknownAllocNoiseLimited}"
  else {
    inherit toml summary;
    cpuWorkloads = cpuEntries;
    noiseLimitedWorkloads = noiseEntries;
    inherit allocNoiseLimited;
  }
