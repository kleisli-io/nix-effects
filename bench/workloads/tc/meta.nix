# Metavariable unification workloads. These measure the elaborator
# overlay's local solver rather than the rigid kernel checker.
{ fx }:

let
  V = fx.tc.value;
  T = fx.tc.term;
  M = fx.tc.elaborate.meta;

  state0 = {
    delta = { };
    metaOrder = [ ];
    constraints = [ ];
    mentions = { };
    nextMetaId = 0;
    nextConstraintId = 0;
  };

  metaType = ty: { ctx = { }; inherit ty; };

  meta = id: spine: ty: {
    _vTag = "VMeta";
    inherit id spine;
    type = metaType ty;
  };

  app = V.eApp;
  x = V.vNe 0 [ ];
  piUnitUnit = V.vPi "_" V.vUnit (V.mkClosure [ ] T.mkUnit);

  conv = lhs: rhs: ty: {
    tag = "conv";
    depth = 0;
    inherit lhs rhs;
    type = ty;
  };

  ids = n: builtins.genList (i: i) n;

  extendMetas = n:
    builtins.foldl'
      (st: id: M.extendMeta id (metaType piUnitUnit) st)
      state0
      (ids n);

  addConstraint = st: c: (M.addAndSimplifyConstraint c st).state;

  process = rounds: st:
    builtins.foldl'
      (acc: _: M.processActiveConstraints acc)
      st
      (ids rounds);

  isSolved = st: id: (st.delta.${toString id}.tag or null) == "Solved";
  solvedCount = st: xs:
    builtins.length (builtins.filter (id: isSolved st id) xs);
  allSolved = st: xs: builtins.all (id: isSolved st id) xs;

  summary = st: xs: {
    solved = solvedCount st xs;
    constraints = builtins.length st.constraints;
    watchers = builtins.length (builtins.attrNames st.mentions);
  };

  solveChainState =
    let
      n = 100;
      terminal = n - 1;
      linkIds = builtins.genList (i: terminal - 1 - i) (n - 1);
      stSolved =
        addConstraint (extendMetas n)
          (conv
            (meta terminal [ (app x) ] piUnitUnit)
            V.vTt
            V.vUnit);
    in
    builtins.foldl'
      (st: id:
        addConstraint st
          (conv
            (meta id [ (app x) ] piUnitUnit)
            (meta (id + 1) [ (app x) ] piUnitUnit)
            V.vUnit))
      stSolved
      linkIds;

  postponeAndWakeState =
    let
      n = 100;
      blocked = 0;
      waitingIds = builtins.genList (i: i + 1) n;
      stWaiting =
        builtins.foldl'
          (st: id:
            addConstraint st
              (conv
                (meta id [ (app x) ] piUnitUnit)
                (meta blocked [ (app x) ] piUnitUnit)
                V.vUnit))
          (extendMetas (n + 1))
          waitingIds;
      stWoken =
        addConstraint stWaiting
          (conv
            (meta blocked [ (app x) ] piUnitUnit)
            V.vTt
            V.vUnit);
    in
    process 1 stWoken;

in
{
  solve-chain-100 =
    let xs = ids 100;
    in assert allSolved solveChainState xs;
    summary solveChainState xs;

  postpone-and-wake-100 =
    let xs = ids 101;
    in assert allSolved postponeAndWakeState xs;
    summary postponeAndWakeState xs;
}
