{ self, api, ... }:

let
  engine = api.extractValue self.meta;
in
{
  scope = {
    mkHole = api.leaf {
      value = engine.mkHole;
      description = "mkHole id type: construct an unsolved metavariable-context entry.";
      signature = "mkHole : Int -> MetaType -> MetaEntry";
    };
    mkSolved = api.leaf {
      value = engine.mkSolved;
      description = "mkSolved id tm type: construct a solved metavariable-context entry.";
      signature = "mkSolved : Int -> ElabVal -> MetaType -> MetaEntry";
    };
    isHole = api.leaf {
      value = engine.isHole;
      description = "isHole m: true when a metavariable-context entry is unsolved.";
      signature = "isHole : MetaEntry -> Bool";
    };
    isSolved = api.leaf {
      value = engine.isSolved;
      description = "isSolved m: true when a metavariable-context entry carries a solution.";
      signature = "isSolved : MetaEntry -> Bool";
    };
    freshMetaInState = api.leaf {
      value = engine.freshMetaInState;
      description = "freshMetaInState type state: allocate a new `VMeta` and append a matching Hole entry to Δ.";
      signature = "freshMetaInState : MetaType -> ElabState -> { meta : VMeta; state : ElabState; }";
    };
    lookupMeta = api.leaf {
      value = engine.lookupMeta;
      description = "lookupMeta state id: read a Δ entry by metavariable id, returning null when absent.";
      signature = "lookupMeta : ElabState -> Int -> MetaEntry | Null";
    };
    extendMeta = api.leaf {
      value = engine.extendMeta;
      description = "extendMeta id type state: add a Hole entry to Δ and advance the fresh-id counter past it.";
      signature = "extendMeta : Int -> MetaType -> ElabState -> ElabState";
    };
    solveMeta = api.leaf {
      value = engine.solveMeta;
      description = "solveMeta id tm state: replace a Δ entry with a Solved entry and reawaken constraints watching that id.";
      signature = "solveMeta : Int -> ElabVal -> ElabState -> ElabState";
    };
    reawakenMentions = api.leaf {
      value = engine.reawakenMentions;
      description = "reawakenMentions ids state: mark postponed constraints watching solved metavariables active.";
      signature = "reawakenMentions : [Int] -> ElabState -> ElabState";
    };
    forceMeta = api.leaf {
      value = engine.forceMeta;
      description = "forceMeta v state: if `v` is solved in Δ, replay its captured spine over the solution.";
      signature = "forceMeta : VMeta -> ElabState -> ElabVal";
    };
    mkConstraint = api.leaf {
      value = engine.mkConstraint;
      description = "mkConstraint c: normalize a constraint record with default position, mentions, and status fields.";
      signature = "mkConstraint : AttrSet -> Constraint";
    };
    addConstraint = api.leaf {
      value = engine.addConstraint;
      description = "addConstraint c state: allocate a constraint id, append to 𝒦, and register watcher mentions.";
      signature = "addConstraint : Constraint -> ElabState -> { id : Int; state : ElabState; }";
    };
    updateConstraint = api.leaf {
      value = engine.updateConstraint;
      description = "updateConstraint cid f state: update one constraint in 𝒦 by id.";
      signature = "updateConstraint : Int -> (Constraint -> Constraint) -> ElabState -> ElabState";
    };
    markConstraint = api.leaf {
      value = engine.markConstraint;
      description = "markConstraint cid status extra state: update one constraint status and merge extra diagnostic fields.";
      signature = "markConstraint : Int -> String -> AttrSet -> ElabState -> ElabState";
    };
    registerMentions = api.leaf {
      value = engine.registerMentions;
      description = "registerMentions mentions cid index: add a constraint id to every mentioned metavariable watcher list.";
      signature = "registerMentions : [Int] -> Int -> MentionsIndex -> MentionsIndex";
    };
    metaIdsVal = api.leaf {
      value = engine.metaIdsVal;
      description = "metaIdsVal v: collect metavariable ids referenced by an elaborator value and its spine payloads.";
      signature = "metaIdsVal : ElabVal -> [Int]";
    };
    mentionsOf = api.leaf {
      value = engine.mentionsOf;
      description = "mentionsOf vals: collect unique metavariable ids referenced by a list of elaborator values.";
      signature = "mentionsOf : [ElabVal] -> [Int]";
    };
    occurs = api.leaf {
      value = engine.occurs;
      description = "occurs id v: true when `v` references metavariable `id`.";
      signature = "occurs : Int -> ElabVal -> Bool";
    };
    patternSpine = api.leaf {
      value = engine.patternSpine;
      description = "patternSpine spine: true for application spines whose arguments are distinct bound variables.";
      signature = "patternSpine : Spine -> Bool";
    };
    levelsVal = api.leaf {
      value = engine.levelsVal;
      description = "levelsVal v: collect neutral variable levels referenced by an elaborator value.";
      signature = "levelsVal : ElabVal -> [Level]";
    };
    simplifyConstraint = api.leaf {
      value = engine.simplifyConstraint;
      description = "simplifyConstraint c state: locally simplify one constraint by rigid conversion, direct meta solving, occurs-check failure, or postponement.";
      signature = "simplifyConstraint : Constraint -> ElabState -> { state : ElabState; constraint : Constraint; }";
    };
    addAndSimplifyConstraint = api.leaf {
      value = engine.addAndSimplifyConstraint;
      description = "addAndSimplifyConstraint c state: simplify a constraint, allocate its id, append it to 𝒦, and update mentions.";
      signature = "addAndSimplifyConstraint : Constraint -> ElabState -> { id : Int; state : ElabState; }";
    };
    processActiveConstraints = api.leaf {
      value = engine.processActiveConstraints;
      description = "processActiveConstraints state: rerun local simplification for active constraints and preserve non-active constraints.";
      signature = "processActiveConstraints : ElabState -> ElabState";
    };
    sigmaFlatten = api.leaf {
      value = engine.sigmaFlatten;
      description = "sigmaFlatten id state: replace an unsolved Sigma-typed meta with a pair of freshly allocated component metas.";
      signature = "sigmaFlatten : Int -> ElabState -> ElabState";
    };
    # Forward the engine's leaf wrap directly so the inline tests
    # colocated in `meta/zonk.nix` and `meta/eval.nix` reach
    # `extractTests` via the `meta` api.namespace value path.
    inherit (self.meta.value) zonkTm evalElab;
  };
}
