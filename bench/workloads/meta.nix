# Per-workload metadata: tier assignment for CI scheduling.
#
# Tiers:
#   quick    — <  5s per run. Always runs in CI.
#   standard — < 60s per run. Always runs in CI.
#   heavy    — ≥ 60s per run. Reserved for merge-to-main or nightly.
#
# Workloads not listed here default to `standard`.
#
# Dotted-path keys match the `<group>.<category>.<name>` path under
# `workloads/`. Enumeration: `nix eval --file ./bench workloads`.
{ }:
let
  tiers = {
    # --- effects / interp ---
    "effects.interp.fib10"          = { tier = "quick"; };
    "effects.interp.fib15"          = { tier = "quick"; };
    "effects.interp.fib20"          = { tier = "standard"; };
    "effects.interp.fib25"          = { tier = "heavy"; };
    "effects.interp.lets100"        = { tier = "quick"; };
    "effects.interp.lets500"        = { tier = "quick"; };
    "effects.interp.lets1000"       = { tier = "standard"; };
    "effects.interp.sum100"         = { tier = "quick"; };
    "effects.interp.sum1000"        = { tier = "quick"; };
    "effects.interp.sum5000"        = { tier = "standard"; };
    "effects.interp.countdown1000"  = { tier = "quick"; };
    "effects.interp.countdown10000" = { tier = "standard"; };
    "effects.interp.ack32"          = { tier = "standard"; };
    "effects.interp.ack33"          = { tier = "heavy"; };

    # --- effects / build-sim ---
    "effects.buildSim.linear50"    = { tier = "quick"; };
    "effects.buildSim.linear100"   = { tier = "quick"; };
    "effects.buildSim.linear200"   = { tier = "standard"; };
    "effects.buildSim.linear500"   = { tier = "heavy"; };
    "effects.buildSim.wide50"      = { tier = "quick"; };
    "effects.buildSim.wide100"     = { tier = "quick"; };
    "effects.buildSim.wide200"     = { tier = "standard"; };
    "effects.buildSim.wide500"     = { tier = "heavy"; };
    "effects.buildSim.diamond5"    = { tier = "quick"; };
    "effects.buildSim.diamond8"    = { tier = "standard"; };
    "effects.buildSim.diamond10"   = { tier = "heavy"; };
    "effects.buildSim.tree5"       = { tier = "quick"; };
    "effects.buildSim.tree8"       = { tier = "standard"; };
    "effects.buildSim.mixed_small" = { tier = "quick"; };
    "effects.buildSim.mixed_medium"= { tier = "standard"; };
    "effects.buildSim.mixed_large" = { tier = "heavy"; };
    "effects.buildSim.fail_early"  = { tier = "quick"; };
    "effects.buildSim.fail_mid"    = { tier = "quick"; };
    "effects.buildSim.fail_late"   = { tier = "quick"; };

    # --- effects / stress ---
    "effects.stress.effectHeavy.s10k"    = { tier = "quick"; };
    "effects.stress.effectHeavy.s100k"   = { tier = "standard"; };
    "effects.stress.effectHeavy.s1m"     = { tier = "heavy"; };
    "effects.stress.bindHeavy.s10k"      = { tier = "quick"; };
    "effects.stress.bindHeavy.s100k"     = { tier = "standard"; };
    "effects.stress.bindHeavy.s1m"       = { tier = "heavy"; };
    "effects.stress.mixed.s10k"          = { tier = "quick"; };
    "effects.stress.mixed.s100k"         = { tier = "standard"; };
    "effects.stress.mixed.s1m"           = { tier = "heavy"; };
    "effects.stress.rawGC.s10k"          = { tier = "quick"; };
    "effects.stress.rawGC.s100k"         = { tier = "standard"; };
    "effects.stress.rawGC.s1m"           = { tier = "heavy"; };
    "effects.stress.deepChains.s10k"     = { tier = "quick"; };
    "effects.stress.deepChains.s50k"     = { tier = "standard"; };
    "effects.stress.nestedHandlers.d3_i1k"   = { tier = "quick"; };
    "effects.stress.nestedHandlers.d5_i1k"   = { tier = "standard"; };
    "effects.stress.nestedHandlers.d10_i100" = { tier = "standard"; };

    # --- effects / tests (full inline+integration suite) ---
    "effects.tests" = { tier = "heavy"; };

    # --- tc / conv ---
    "tc.conv.identical-shallow" = { tier = "quick"; };
    "tc.conv.identical-deep"    = { tier = "quick"; };
    "tc.conv.mu-heavy"          = { tier = "quick"; };
    "tc.conv.plus-heavy"        = { tier = "quick"; };
    "tc.conv.beta-distinct"     = { tier = "quick"; };
    "tc.conv.alpha-equivalent"  = { tier = "quick"; };

    # --- tc / quote ---
    "tc.quote.closed" = { tier = "quick"; };
    "tc.quote.open"   = { tier = "quick"; };
    "tc.quote.stuck"  = { tier = "quick"; };

    # --- tc / check ---
    "tc.check.nat-chain-5000"  = { tier = "quick"; };
    "tc.check.list-chain-5000" = { tier = "quick"; };
    "tc.check.macro-field"     = { tier = "quick"; };

    # --- tc / infer ---
    "tc.infer.deep-app-100" = { tier = "quick"; };

    # --- tc / elaborate ---
    "tc.elaborate.flatten"   = { tier = "quick"; };
    "tc.elaborate.recursive" = { tier = "quick"; };

    # --- tc / e2e ---
    "tc.e2e.tc-test-suite-full"      = { tier = "quick"; };
    "tc.e2e.category-theory-verify"  = { tier = "standard"; };
    "tc.e2e.synthetic-large-proof"   = { tier = "heavy"; };
    "tc.e2e.datatype-macro-big"      = { tier = "quick"; };
    "tc.e2e.datatypeI-fin-deep"      = { tier = "quick"; };
    # Per-module breakdown of the tc test suite.
    "tc.e2e.tc-test-suite-per-module.check"     = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.conv"      = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.elaborate" = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.eval"      = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.hoas"      = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.quote"     = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.term"      = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.value"     = { tier = "quick"; };
    "tc.e2e.tc-test-suite-per-module.verified"  = { tier = "quick"; };
  };

  defaultTier = "standard";
in {
  inherit tiers defaultTier;

  # Lookup helper: workload path -> tier string.
  lookup = path: (tiers.${path} or { tier = defaultTier; }).tier;

  # Filter helper: list of workload paths matching a tier predicate.
  # `tierPred :: String -> Bool`.
  filterByTier = tierPred: allPaths:
    builtins.filter (p: tierPred ((tiers.${p} or { tier = defaultTier; }).tier)) allPaths;
}
