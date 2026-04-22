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
  cpuKeys = builtins.attrNames (budgets.cpu or { });
  overlap = builtins.filter (w: builtins.elem w cpuKeys) noiseLimited;
  validateBudgets =
    if overlap == [ ]
    then null
    else throw "finalize-gate: budgets.toml lists workloads in both [cpu] and noiseLimited: ${builtins.concatStringsSep ", " overlap}";

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

  guards = builtins.seq validateBudgets (builtins.seq validateNixVersion null);

  gateResult = builtins.seq guards (bench.gate.gate {
    inherit baseline current budgets trailers;
  });

  markdown = bench.format.emitGateMarkdown {
    inherit gateResult baselineName currentName;
  };
in {
  inherit gateResult markdown;
  pass = gateResult.pass;
}
