{ self, fx, ... }:

let
  V = fx.tc.value;
  E = fx.tc.eval;
  T = fx.tc.term;
  C = fx.tc.conv;

  state0 = {
    delta = { };
    metaOrder = [ ];
    constraints = [ ];
    mentions = { };
    nextMetaId = 0;
    nextConstraintId = 0;
  };

  meta = id: spine: ty: {
    _vTag = "VMeta";
    inherit id spine;
    type = { ctx = { }; inherit ty; };
  };

  m0 = spine: ty: meta 0 spine ty;
  m1 = spine: ty: meta 1 spine ty;
  app = V.eApp;
  x = V.vNe 0 [ ];
  y = V.vNe 1 [ ];
  z = V.vNe 2 [ ];
  fn = V.vNe 9 [ ];

  piUnitUnit = V.vPi "_" V.vUnit (V.mkClosure [ ] T.mkUnit);
  piUnitPiUnitUnit =
    V.vPi "_" V.vUnit (V.mkClosure [ ] (T.mkPi "_" T.mkUnit T.mkUnit));
  sigmaUnitUnit = V.vSigma "_" V.vUnit (V.mkClosure [ ] T.mkUnit);
  bootUnitUnit = V.vBootSum V.vUnit V.vUnit;
  eqTt = V.vBootEq V.vUnit V.vTt V.vTt;

  # A Pi whose codomain closure captures a `VMeta` and lifts it. Walking
  # this telescope forces the meta through `KLift_X`, which reads `.tag`
  # (absent on `VMeta`) — so the kernel evaluator crashes and only the
  # overlay instantiator succeeds.
  piUnitLiftMeta = V.vPi "_" V.vUnit
    (V.mkClosure [ (m1 [ ] V.vUnit) ]
      (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero) T.mkBootRefl (T.mkVar 1)));

  conv = lhs: rhs: ty: {
    tag = "conv";
    depth = 0;
    inherit lhs rhs;
    type = ty;
  };

  simplify = c: state: self.simplifyConstraint c state;
  solve = c: simplify c state0;
  status = c: (solve c).constraint.status;
  reason = c: (solve c).constraint.reason or null;
  solved = r: id: r.state.delta.${toString id};
  solvedTag = r: id: (solved r id).tag;

  apply1 = f: a: E.vApp f a;
  apply2 = f: a: b: E.vApp (E.vApp f a) b;

  direct = rhs: solve (conv (m0 [ ] V.vUnit) rhs V.vUnit);
  pattern1 = rhs: solve (conv (m0 [ (app x) ] piUnitUnit) rhs V.vUnit);
  pattern2 = rhs:
    solve (conv (m0 [ (app x) (app y) ] piUnitPiUnitUnit) rhs sigmaUnitUnit);

  cMeta0Tt = conv (m0 [ ] V.vUnit) V.vTt V.vUnit;
  cMeta1Unit = conv (m1 [ ] (V.vU V.vLevelZero)) V.vUnit (V.vU V.vLevelZero);

in
{
  scope = { };

  tests = {
    "meta-suite-positive-direct-unit" = {
      expr = let r = direct V.vTt; in { inherit (r.constraint) status; tag = (solved r 0).tm.tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    "meta-suite-positive-direct-string" = {
      expr =
        let r = solve (conv (m0 [ ] V.vString) (V.vStringLit "ok") V.vString);
        in { inherit (r.constraint) status; value = (solved r 0).tm.value; };
      expected = { status = "solved"; value = "ok"; };
    };

    "meta-suite-positive-direct-pi" = {
      expr =
        let
          lam = V.vLam "x" V.vUnit (V.mkClosure [ ] (T.mkVar 0));
          r = solve (conv (m0 [ ] piUnitUnit) lam piUnitUnit);
        in
        { inherit (r.constraint) status; tag = (apply1 (solved r 0).tm V.vTt).tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    "meta-suite-positive-symmetric-meta" = {
      expr =
        let r = solve (conv V.vTt (m0 [ ] V.vUnit) V.vUnit);
        in { inherit (r.constraint) status; tag = (solved r 0).tm.tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    "meta-suite-positive-rigid-conv" = {
      expr = status (conv V.vTt V.vTt V.vUnit);
      expected = "solved";
    };

    "meta-suite-positive-pattern-identity" = {
      expr =
        let
          r = pattern1 x;
          applied = apply1 (solved r 0).tm V.vTt;
        in
        { inherit (r.constraint) status; tag = applied.tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    # Regression: solving a pattern meta whose type telescope lifts a
    # captured `VMeta`. `lamSolution` opens the telescope via the overlay;
    # kernel instantiation would route the meta into the CEK machine.
    "meta-suite-positive-pattern-meta-typed-telescope" = {
      expr =
        let
          r = solve (conv (m0 [ (app x) ] piUnitLiftMeta) x V.vUnit);
          applied = apply1 (solved r 0).tm V.vTt;
        in
        { inherit (r.constraint) status; tag = applied.tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    "meta-suite-positive-pattern-constant" = {
      expr =
        let
          r = pattern1 V.vUnit;
          applied = apply1 (solved r 0).tm V.vTt;
        in
        { inherit (r.constraint) status; tag = applied.tag; };
      expected = { status = "solved"; tag = "VUnit"; };
    };

    "meta-suite-positive-pattern-pair-swap" = {
      expr =
        let
          r = pattern2 (V.vPair y x);
          applied = apply2 (solved r 0).tm V.vTt V.vUnit;
        in
        { inherit (r.constraint) status; fst = applied.fst.tag; snd = applied.snd.tag; };
      expected = { status = "solved"; fst = "VUnit"; snd = "VTt"; };
    };

    "meta-suite-positive-pattern-first-projection" = {
      expr =
        let
          r = pattern2 x;
          applied = apply2 (solved r 0).tm V.vTt V.vUnit;
        in
        { inherit (r.constraint) status; tag = applied.tag; };
      expected = { status = "solved"; tag = "VTt"; };
    };

    "meta-suite-positive-pattern-second-projection" = {
      expr =
        let
          r = pattern2 y;
          applied = apply2 (solved r 0).tm V.vTt V.vUnit;
        in
        { inherit (r.constraint) status; tag = applied.tag; };
      expected = { status = "solved"; tag = "VUnit"; };
    };

    "meta-suite-positive-flex-flex-left-solve" = {
      expr =
        let r = solve (conv (m0 [ ] V.vUnit) (m1 [ ] V.vUnit) V.vUnit);
        in { inherit (r.constraint) status; rhs = (solved r 0).tm.id; };
      expected = { status = "solved"; rhs = 1; };
    };

    "meta-suite-negative-duplicate-spine-postpones" = {
      expr = status (conv (m0 [ (app x) (app x) ] piUnitPiUnitUnit) x V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-non-var-spine-postpones" = {
      expr = status (conv (m0 [ (app V.vTt) ] piUnitUnit) V.vTt V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-rhs-outside-spine-postpones" = {
      expr = status (conv (m0 [ (app x) ] piUnitUnit) y V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-rhs-has-flex-postpones" = {
      expr = status (conv (m0 [ (app x) ] piUnitUnit) (m1 [ ] V.vUnit) V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-f-x-x-postpones" = {
      expr =
        let rhs = V.vNe 9 [ (app x) (app x) ];
        in status (conv (m0 [ (app x) ] piUnitUnit) rhs V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-pair-x-x-postpones" = {
      expr = status (conv (m0 [ (app x) ] piUnitUnit) (V.vPair x x) sigmaUnitUnit);
      expected = "postponed";
    };

    "meta-suite-negative-rigid-mismatch-postpones" = {
      expr = status (conv V.vTt V.vUnit V.vUnit);
      expected = "postponed";
    };

    "meta-suite-negative-unknown-constraint-postpones" = {
      expr = (self.simplifyConstraint { tag = "test"; lhs = V.vTt; rhs = V.vUnit; } state0).constraint.status;
      expected = "postponed";
    };

    "meta-suite-negative-levels-record-foreign-var" = {
      expr = self.levelsVal (V.vPair x z);
      expected = [ 0 2 ];
    };

    "meta-suite-negative-pattern-reason" = {
      expr = reason (conv (m0 [ (app x) ] piUnitUnit) y V.vUnit);
      expected = "pattern-spine-not-inverted";
    };

    "meta-suite-postpone-add-registers-watchers" = {
      expr =
        let r = self.addAndSimplifyConstraint (conv (m0 [ (app x) ] piUnitUnit) y V.vUnit) state0;
        in { id = r.id; watchers = r.state.mentions."0"; status = (builtins.head r.state.constraints).status; };
      expected = { id = 0; watchers = [ 0 ]; status = "postponed"; };
    };

    "meta-suite-postpone-solve-reawakens-one" = {
      expr =
        let
          st = self.solveMeta 0 V.vTt {
            delta = { "0" = self.mkHole 0 V.vUnit; };
            metaOrder = [ 0 ];
            mentions = { "0" = [ 2 ]; };
            constraints = [{ id = 2; status = "postponed"; }];
          };
        in
        st.constraints;
      expected = [{ id = 2; status = "active"; }];
    };

    "meta-suite-postpone-solve-reawakens-many" = {
      expr =
        let
          st = self.solveMeta 0 V.vTt {
            delta = { "0" = self.mkHole 0 V.vUnit; };
            metaOrder = [ 0 ];
            mentions = { "0" = [ 2 3 ]; };
            constraints = [
              { id = 2; status = "postponed"; }
              { id = 3; status = "postponed"; }
            ];
          };
        in
        map (c: c.status) st.constraints;
      expected = [ "active" "active" ];
    };

    "meta-suite-postpone-process-active-solves" = {
      expr =
        let
          st = self.processActiveConstraints {
            delta = { };
            metaOrder = [ ];
            mentions = { };
            constraints = [ (cMeta0Tt // { id = 0; status = "active"; }) ];
          };
        in
        { status = (builtins.head st.constraints).status; solved = st.delta."0".tag; };
      expected = { status = "solved"; solved = "Solved"; };
    };

    "meta-suite-postpone-process-preserves-postponed" = {
      expr =
        let
          c = conv (m0 [ (app x) ] piUnitUnit) y V.vUnit;
          st = self.processActiveConstraints {
            delta = { };
            metaOrder = [ ];
            mentions = { };
            constraints = [ (c // { id = 0; status = "postponed"; }) ];
          };
        in
        (builtins.head st.constraints).status;
      expected = "postponed";
    };

    "meta-suite-postpone-direct-add-solves" = {
      expr =
        let r = self.addAndSimplifyConstraint cMeta0Tt state0;
        in { id = r.id; status = (builtins.head r.state.constraints).status; solved = r.state.delta."0".tag; };
      expected = { id = 0; status = "solved"; solved = "Solved"; };
    };

    "meta-suite-postpone-order-a" = {
      expr =
        let
          r0 = self.addAndSimplifyConstraint cMeta0Tt state0;
          r1 = self.addAndSimplifyConstraint cMeta1Unit r0.state;
        in
        builtins.attrNames r1.state.delta;
      expected = [ "0" "1" ];
    };

    "meta-suite-postpone-order-b" = {
      expr =
        let
          r0 = self.addAndSimplifyConstraint cMeta1Unit state0;
          r1 = self.addAndSimplifyConstraint cMeta0Tt r0.state;
        in
        builtins.attrNames r1.state.delta;
      expected = [ "0" "1" ];
    };

    "meta-suite-eta-pi-direct-lambda" = {
      expr =
        let
          lam = V.vLam "x" V.vUnit (V.mkClosure [ ] (T.mkVar 0));
          r = solve (conv (m0 [ ] piUnitUnit) lam piUnitUnit);
        in
        C.conv 0 (apply1 (solved r 0).tm V.vTt) V.vTt;
      expected = true;
    };

    "meta-suite-eta-sigma-direct-pair" = {
      expr =
        let
          r = solve (conv (m0 [ ] sigmaUnitUnit) (V.vPair V.vTt V.vUnit) sigmaUnitUnit);
          pair = (solved r 0).tm;
        in
        { inherit (r.constraint) status; fst = pair.fst.tag; snd = pair.snd.tag; };
      expected = { status = "solved"; fst = "VTt"; snd = "VUnit"; };
    };

    "meta-suite-eta-boot-sum-inl" = {
      expr =
        let
          rhs = V.vBootInl V.vUnit V.vUnit V.vTt;
          r = solve (conv (m0 [ ] bootUnitUnit) rhs bootUnitUnit);
        in
        { inherit (r.constraint) status; tag = (solved r 0).tm.tag; };
      expected = { status = "solved"; tag = "VBootInl"; };
    };

    "meta-suite-eta-boot-sum-inr" = {
      expr =
        let
          rhs = V.vBootInr V.vUnit V.vUnit V.vTt;
          r = solve (conv (m0 [ ] bootUnitUnit) rhs bootUnitUnit);
        in
        { inherit (r.constraint) status; tag = (solved r 0).tm.tag; };
      expected = { status = "solved"; tag = "VBootInr"; };
    };

    "meta-suite-eta-eq-refl" = {
      expr =
        let r = solve (conv (m0 [ ] eqTt) V.vBootRefl eqTt);
        in { inherit (r.constraint) status; tag = (solved r 0).tm.tag; };
      expected = { status = "solved"; tag = "VBootRefl"; };
    };

    "meta-suite-eta-sigma-flatten" = {
      expr =
        let
          st = self.sigmaFlatten 0 {
            delta = { "0" = self.mkHole 0 { ctx = { }; ty = sigmaUnitUnit; }; };
            metaOrder = [ 0 ];
            constraints = [ ];
            mentions = { };
            nextMetaId = 1;
          };
        in
        { solved = st.delta."0".tag; pair = st.delta."0".tm.tag; ids = st.metaOrder; };
      expected = { solved = "Solved"; pair = "VPair"; ids = [ 0 1 2 ]; };
    };

    "meta-suite-occurs-self-app-fails" = {
      expr = status (conv (m0 [ ] V.vUnit) (m0 [ (app V.vTt) ] piUnitUnit) V.vUnit);
      expected = "failed";
    };

    "meta-suite-occurs-self-pair-fails" = {
      expr = status (conv (m0 [ ] V.vUnit) (V.vPair (m0 [ ] V.vUnit) V.vTt) V.vUnit);
      expected = "failed";
    };

    "meta-suite-occurs-self-fails" = {
      expr = status (conv (m0 [ ] V.vUnit) (m0 [ ] V.vUnit) V.vUnit);
      expected = "failed";
    };

    "meta-suite-occurs-reason" = {
      expr = reason (conv (m0 [ ] V.vUnit) (m0 [ (app V.vTt) ] piUnitUnit) V.vUnit);
      expected = "occurs-check";
    };

    "meta-suite-occurs-indirect-solved-meta" = {
      expr =
        let
          st = state0 // {
            delta = { "1" = self.mkSolved 1 (m0 [ ] V.vUnit) V.vUnit; };
            metaOrder = [ 1 ];
          };
          r = simplify (conv (m0 [ ] V.vUnit) (m1 [ ] V.vUnit) V.vUnit) st;
        in
        r.constraint.status;
      expected = "failed";
    };

    "meta-suite-occurs-other-flex-ok" = {
      expr = status (conv (m0 [ ] V.vUnit) (m1 [ ] V.vUnit) V.vUnit);
      expected = "solved";
    };

    "meta-suite-landmine-duplicate-rhs-not-solved" = {
      expr =
        let r = pattern1 (V.vPair x x);
        in { inherit (r.constraint) status; solved = r.state.delta ? "0"; };
      expected = { status = "postponed"; solved = false; };
    };

    "meta-suite-landmine-occurs-not-solved" = {
      expr =
        let r = solve (conv (m0 [ ] V.vUnit) (m0 [ (app V.vTt) ] piUnitUnit) V.vUnit);
        in { inherit (r.constraint) status; solved = r.state.delta ? "0"; };
      expected = { status = "failed"; solved = false; };
    };

    "meta-suite-landmine-foreign-var-not-solved" = {
      expr =
        let r = pattern1 y;
        in { inherit (r.constraint) status; solved = r.state.delta ? "0"; };
      expected = { status = "postponed"; solved = false; };
    };

    # Deep-walk gate: metaIds/occurs/levels traverse a 10000-deep neutral
    # spine flat. Native recursion overflows near ~5000. levels preserves
    # multiplicity (patternSolve reads allDistinct over the raw list).
    "meta-suite-metaids-deep-spine-10000" = {
      expr =
        let deep = builtins.foldl' (acc: _: V.vNe 0 [ (V.eApp acc) ])
          (meta 7 [ ] V.vUnit) (builtins.genList (i: i) 10000);
        in self.metaIdsVal deep;
      expected = [ 7 ];
    };
    "meta-suite-occurs-deep-spine-10000" = {
      expr =
        let deep = builtins.foldl' (acc: _: V.vNe 0 [ (V.eApp acc) ])
          (meta 7 [ ] V.vUnit) (builtins.genList (i: i) 10000);
        in { hit = self.occurs 7 deep; miss = self.occurs 0 deep; };
      expected = { hit = true; miss = false; };
    };
    "meta-suite-levels-deep-spine-10000" = {
      expr =
        let
          deep = builtins.foldl' (acc: _: V.vNe 0 [ (V.eApp acc) ])
            (V.freshVar 0) (builtins.genList (i: i) 10000);
          ls = self.levelsVal deep;
        in { n = builtins.length ls; allZero = builtins.all (l: l == 0) ls; };
      expected = { n = 10001; allZero = true; };
    };
  };
}
