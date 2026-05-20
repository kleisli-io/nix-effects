{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.elaborate.meta.engine: metavariable context, constraints, and local unification helpers for the elaborator overlay.";
  doc = ''
    # fx.tc.elaborate.meta.engine

    Internal engine for the elaborator's metavariable overlay. Δ is the
    metavariable context, 𝒦 is the constraint queue, and mentions is the
    watcher index from metavariable id to waiting constraint ids.
  '';
  value = {
    inherit (self)
      mkHole mkSolved isHole isSolved freshMetaInState
      lookupMeta extendMeta solveMeta reawakenMentions forceMeta
      mkConstraint addConstraint updateConstraint markConstraint registerMentions
      metaIdsVal mentionsOf occurs patternSpine levelsVal simplifyConstraint
      addAndSimplifyConstraint processActiveConstraints sigmaFlatten
      zonkTm evalElab;
  };
  tests = partTests;
}
