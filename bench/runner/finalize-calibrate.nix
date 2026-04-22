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
# Its `noiseLimited = [...]` array enumerates workloads whose cpu.p95
# spread is structurally noise-limited (small-workload relative-variance
# artifacts, GC-jitter on specific DAG shapes). Those workloads are
# excluded from the emitted `[cpu]` section so future calibrations don't
# silently regenerate cpu budgets for them; the `noiseLimited` array
# round-trips verbatim so the declaration is preserved.
#
# The emitted TOML is a *proposal*; human review + `budgets.toml` commit
# is expected before CI uses it.
{ runPath, benchPath, existingBudgetsPath ? null, minBudget ? 3 }:

let
  run = builtins.fromJSON (builtins.readFile runPath);

  # Authoritative workload registry — validated against this, not the
  # current run's results, because `--filter` may narrow a calibration
  # to a subset of workloads while `noiseLimited` remains global.
  bench = import benchPath { };
  knownWorkloads = builtins.attrNames bench.meta.tiers;

  existing = if existingBudgetsPath == null
             then { }
             else builtins.fromTOML (builtins.readFile existingBudgetsPath);

  noiseLimited = existing.noiseLimited or [ ];

  # Every `noiseLimited` entry must be a known bench workload. A typo or
  # stale name (post-rename) would otherwise silently suppress nothing;
  # fail loudly instead.
  unknownNoiseLimited =
    builtins.filter (w: ! (builtins.elem w knownWorkloads)) noiseLimited;

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

  toml = ''
    # Perf budgets generated from calibration run '${run.name}'.
    # Runs per workload: ${toString run.runsPerWorkload}
    # Nix: ${run.nix}
    # System: ${run.system}
    # Timestamp: ${run.timestamp}

    allocTolerancePermille = 5
    ${noiseLimitedBlock}
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
  then throw "finalize-calibrate: noiseLimited contains workloads not present in the current run: ${builtins.concatStringsSep ", " unknownNoiseLimited}"
  else {
    inherit toml summary;
    cpuWorkloads = cpuEntries;
    noiseLimitedWorkloads = noiseEntries;
  }
