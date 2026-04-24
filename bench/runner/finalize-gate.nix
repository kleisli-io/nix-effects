# Baseline + current → gate classification + markdown.
#
# The shell driver collects two history JSON files (produced by run.nix),
# an optional budgets TOML, and an optional trailers JSON, then this
# helper threads them through `bench.gate.gate` + `bench.format.emitGateMarkdown`.
#
# Input:
#   benchPath     : bench directory.
#   baselinePath  : history JSON from a prior run (`name.json`).
#   currentPath   : history JSON from the run under test.
#   budgetsPath   : TOML with `allocTolerancePermille` + `cpu.<workload> = pct`.
#                   `null` → cpu gating is off; alloc gating runs at 5‰.
#   trailersPath  : JSON array of `{ workload, reason }`. `null` → no
#                   overrides; every hard fail is a hard fail.
#   cpuGating     : when false, the `[cpu]` table of `budgets` is ignored
#                   (reset to `{ }`) before classification. Use for
#                   environments where cpu timings are not meaningfully
#                   comparable against the recorded baseline (e.g. CI on
#                   shared runners versus a baseline captured on a
#                   developer workstation). Alloc gating is unaffected.
#   baselineName / currentName : labels for the emitted markdown header.
#
# Invariants enforced before classification:
#   - `budgets.cpu` keys and `budgets.noiseLimited` entries are disjoint.
#     Overlap would silently prefer the cpu budget and hide the
#     noise-limited declaration.
#   - Every entry in `noiseLimited` and `allocNoiseLimited` names a
#     workload present in baseline or current. An unknown entry (typo
#     or retired-and-forgotten workload) degrades silently to a no-op
#     exclusion, so the gate would keep hard-failing the workload the
#     operator thought was excluded.
#   - `baseline.nix == current.nix`. Allocation counters emitted by
#     `NIX_SHOW_STATS` are deterministic *for a fixed evaluator* —
#     different Nix versions can ship different thunk/env strategies and
#     produce different counts for identical code. Silent cross-version
#     comparison would blame the contributor for an evaluator change.
#     Either re-capture the baseline with the current Nix or pin the
#     evaluator to match the baseline.
#
# Output:
#   { gateResult; markdown; pass; }
{ benchPath, baselinePath, currentPath,
  budgetsPath ? null, trailersPath ? null,
  cpuGating ? true,
  baselineName ? "baseline", currentName ? "current" }:

let
  bench = import benchPath { };

  baseline = builtins.fromJSON (builtins.readFile baselinePath);
  current  = builtins.fromJSON (builtins.readFile currentPath);

  defaultBudgets = { cpu = { }; allocTolerancePermille = 5; };
  rawBudgets = if budgetsPath == null then defaultBudgets
               else builtins.fromTOML (builtins.readFile budgetsPath);

  budgets = if cpuGating
            then rawBudgets
            else rawBudgets // { cpu = { }; };

  # A workload can be either cpu-gated with a budget or declared
  # noise-limited — not both. Silent overlap would let a manual edit of
  # budgets.toml re-introduce a worthless cpu budget for a workload the
  # canonical file explicitly excluded. When cpu gating is off the
  # check is vacuously true (empty cpu set).
  noiseLimited = rawBudgets.noiseLimited or [ ];
  allocNoiseLimited = rawBudgets.allocNoiseLimited or [ ];
  cpuKeys = builtins.attrNames (budgets.cpu or { });
  overlap = builtins.filter (w: builtins.elem w cpuKeys) noiseLimited;
  validateBudgets =
    if overlap == [ ]
    then null
    else throw "finalize-gate: budgets.toml lists workloads in both [cpu] and noiseLimited: ${builtins.concatStringsSep ", " overlap}";

  # Typo-detection for exclusion lists. An unknown entry degrades
  # silently to a no-op — the intended exclusion never fires, and the
  # gate will hard-fail on a workload the operator thought was
  # excluded. Known workloads are the union of:
  #   - `bench.meta.tiers` — the canonical declared-workloads set.
  #     Higher-tier workloads (standard/heavy) appear here even when
  #     the current run is quick-tier and excludes them.
  #   - `baseline.results` — tolerates an exclusion for a workload that
  #     was retired since the baseline was captured.
  #   - `current.results` — tolerates a new workload added without a
  #     meta.nix entry (its tier defaults to standard).
  # Attrset union gives keyset membership in O(1).
  knownWorkloadSet =
    (bench.meta.tiers or { })
    // (baseline.results or { })
    // (current.results or { });
  validateExclusionList = listName: list:
    let unknown = builtins.filter (w: ! (knownWorkloadSet ? ${w})) list;
    in if unknown == [ ]
       then null
       else throw "finalize-gate: ${listName} lists unknown workloads (typo?): ${builtins.concatStringsSep ", " unknown}";
  validateNoiseLimited = validateExclusionList "noiseLimited" noiseLimited;
  validateAllocNoiseLimited = validateExclusionList "allocNoiseLimited" allocNoiseLimited;

  # Workloads missing from meta.nix default to tier=standard and
  # silently consume CI cycles. Soft-warn (non-fatal) so contributors
  # can iterate before landing the meta.nix entry.
  tieredWorkloadSet = bench.meta.tiers or { };
  currentWorkloadNames = builtins.attrNames (current.results or { });
  unregisteredWorkloads =
    builtins.filter
      (w: ! (tieredWorkloadSet ? ${w}))
      currentWorkloadNames;
  warnUnregistered =
    if unregisteredWorkloads == [ ]
    then null
    else builtins.trace
      "finalize-gate: warning — workloads missing from bench/workloads/meta.nix (tier defaults to standard): ${builtins.concatStringsSep ", " unregisteredWorkloads}"
      null;

  # Alloc determinism holds only within a Nix version. Allowing a
  # mismatch here turns every evaluator upgrade into a false alloc
  # regression against the old baseline.
  baselineNix = baseline.nix or "unknown";
  currentNix  = current.nix or "unknown";
  validateNixVersion =
    if baselineNix == currentNix
    then null
    else throw ''
      finalize-gate: Nix version mismatch between baseline and current run.
        baseline (${baselineName}): ${baselineNix}
        current  (${currentName}):  ${currentNix}

      Allocation counters are evaluator-version-specific; comparing across
      versions produces false regressions. Either re-capture the baseline
      with Nix ${currentNix}, or pin the gate invocation's Nix to
      ${baselineNix}.
    '';

  trailers = if trailersPath == null then [ ]
             else builtins.fromJSON (builtins.readFile trailersPath);

  guards = builtins.seq validateBudgets
             (builtins.seq validateNoiseLimited
               (builtins.seq validateAllocNoiseLimited
                 (builtins.seq validateNixVersion
                   (builtins.seq warnUnregistered null))));

  gateResult = builtins.seq guards (bench.gate.gate {
    inherit baseline current budgets trailers allocNoiseLimited;
  });

  markdown = bench.format.emitGateMarkdown {
    inherit gateResult baselineName currentName;
  };
in {
  inherit gateResult markdown;
  pass = gateResult.pass;
}
