# Open-regressions audit.
#
# Consumes:
#   benchPath     : bench directory (for lib.gate + lib.format).
#   baselinePath  : reference history JSON (the "expected good" state).
#   currentPath   : current history JSON to audit against baseline+budgets.
#   budgetsPath   : budgets.toml. `null` → cpu gating is off; alloc still runs.
#   trailersPath  : JSON array of `{ sha, workload, reason }` extracted from
#                   `Perf-regression:` trailers in the audit range.
#   since         : git-log range label for the markdown header.
#
# For each trailer entry, classifies the named workload using the
# standard gate logic against baseline/current/budgets with no trailer
# overrides. The resulting status tells the auditor whether the
# acknowledged regression has returned to within-budget territory:
#
#   pass         → recovered (metrics are back under budget).
#   fail_allocs  → open_allocs.
#   fail_cpu     → open_cpu.
#   warn_cpu     → open_warn.
#   (workload not in current.results) → unmeasured (bench regressed structurally).
{ benchPath, baselinePath, currentPath,
  budgetsPath ? null, trailersPath, since ? "<range>" }:

let
  bench = import benchPath { };

  baseline = builtins.fromJSON (builtins.readFile baselinePath);
  current  = builtins.fromJSON (builtins.readFile currentPath);
  trailers = builtins.fromJSON (builtins.readFile trailersPath);

  defaultBudgets = { cpu = { }; allocTolerancePermille = 5; };
  budgets = if budgetsPath == null then defaultBudgets
            else builtins.fromTOML (builtins.readFile budgetsPath);

  # Sanity (mirrors finalize-gate): a workload can be either cpu-gated
  # with a budget or declared noise-limited — not both.
  noiseLimited = budgets.noiseLimited or [ ];
  cpuKeys = builtins.attrNames (budgets.cpu or { });
  overlap = builtins.filter (w: builtins.elem w cpuKeys) noiseLimited;
  validateBudgets =
    if overlap == [ ]
    then null
    else throw "finalize-open-regressions: budgets.toml lists workloads in both [cpu] and noiseLimited: ${builtins.concatStringsSep ", " overlap}";

  gateResult = builtins.seq validateBudgets (bench.gate.gate {
    inherit baseline current budgets;
    trailers = [ ];
  });

  classifyByWorkload = builtins.listToAttrs
    (map (c: { name = c.workload; value = c; }) gateResult.classifications);

  auditOne = t:
    let
      cls = classifyByWorkload.${t.workload} or null;
      status =
        if cls == null then "unmeasured"
        else if cls.status == "pass" then "recovered"
        else if cls.status == "fail_allocs" then "open_allocs"
        else if cls.status == "fail_cpu" then "open_cpu"
        else if cls.status == "warn_cpu" then "open_warn"
        else cls.status;
    in {
      inherit (t) sha workload reason;
      inherit status;
      classification = cls;
    };

  entries = map auditOne trailers;

  openCount = builtins.length
    (builtins.filter (e: e.status != "recovered") entries);

  markdown = bench.format.emitOpenRegressionsMarkdown {
    inherit entries since;
  };

in {
  inherit entries markdown;
  pass = openCount == 0;
  openCount = openCount;
}
