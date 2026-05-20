{ self, fx, api, ... }:

let
  V = fx.tc.value;
  C = fx.tc.conv;
  E = fx.tc.eval;
  T = fx.tc.term;

  unique = xs:
    builtins.foldl'
      (acc: x: if builtins.elem x acc then acc else acc ++ [ x ])
      [ ]
      xs;

  isVMeta = v:
    builtins.isAttrs v && (v._vTag or null) == "VMeta";

  mkVMeta = id: spine: type:
    { _vTag = "VMeta"; inherit id spine type; };

  concatMap = f: xs: builtins.concatLists (map f xs);

  idsInElim = frame:
    let t = frame.tag or null;
    in
    if t == "EApp" then metaIdsVal frame.arg
    else if t == "EBootSumElim" then concatMap metaIdsVal [ frame.left frame.right frame.motive frame.onLeft frame.onRight ]
    else if t == "EBootJ" then concatMap metaIdsVal [ frame.type frame.lhs frame.motive frame.base frame.rhs ]
    else if t == "EStrEq" then metaIdsVal frame.arg
    else if t == "EDescInd" then concatMap metaIdsVal [ frame.D frame.motive frame.step frame.i ]
    else if t == "ELiftElim" then concatMap metaIdsVal [ frame.l frame.m frame.eq frame.A ]
    else if t == "ESquashElim" then concatMap metaIdsVal [ frame.A frame.B frame.f ]
    else if t == "EInterpD" then concatMap metaIdsVal [ frame.level frame.I frame.X frame.i ]
    else if t == "EAllD" then concatMap metaIdsVal [ frame.level frame.I frame.K frame.X frame.M frame.i frame.d ]
    else if t == "EEverywhereD" then concatMap metaIdsVal [ frame.level frame.I frame.K frame.X frame.M frame.ih frame.i frame.d ]
    else [ ];

  metaIdsVal = v:
    if isVMeta v then [ v.id ] ++ concatMap idsInElim (v.spine or [ ])
    else if builtins.isAttrs v then
      let t = v.tag or null;
      in
      if t == "VNe" then concatMap idsInElim (v.spine or [ ])
      else if t == "VLam" || t == "VPi" then metaIdsVal v.domain
      else if t == "VSigma" then metaIdsVal v.fst
      else if t == "VPair" then metaIdsVal v.fst ++ metaIdsVal v.snd
      else if t == "VBootSum" then metaIdsVal v.left ++ metaIdsVal v.right
      else if t == "VBootInl" || t == "VBootInr" then metaIdsVal v.left ++ metaIdsVal v.right ++ metaIdsVal v.val
      else if t == "VBootEq" then concatMap metaIdsVal [ v.type v.lhs v.rhs ]
      else if t == "VSquash" then metaIdsVal v.A
      else if t == "VSquashIntro" then metaIdsVal v.a
      else if t == "VDesc" then metaIdsVal v.level ++ metaIdsVal v.I
      else if t == "VMu" then concatMap metaIdsVal [ v.I v.D v.i ]
      # `_canonRef`-tagged VDescCons stand for closed canonical terms whose
      # `.D`/`.i`/`.d` slots are built by applying a canonical body to
      # `params` (see eval/desc.nix:206, 222). User-introduced metas can
      # therefore only flow through `params`; walking the body would
      # descend into self-referential canonical encodings (e.g. `descDesc`
      # nesting through `Lift`/`LevelMax`) and stack-overflow. Mirrors the
      # kernel `canonRefConv` short-circuit at conv.nix:427-430.
      else if t == "VDescCon" then
        if v ? _canonRef
        then concatMap metaIdsVal (v._canonRef.params or [ ])
        else concatMap metaIdsVal [ v.D v.i v.d ]
      else if t == "VInterpD" then concatMap metaIdsVal [ v.level v.I v.D v.X v.i ]
      else if t == "VAllD" then concatMap metaIdsVal [ v.level v.I v.D v.K v.X v.M v.i v.d ]
      else if t == "VEverywhereD" then concatMap metaIdsVal [ v.level v.I v.D v.K v.X v.M v.ih v.i v.d ]
      else if t == "VLift" then concatMap metaIdsVal [ v.l v.m v.eq v.A ]
      else if t == "VLiftIntro" then concatMap metaIdsVal [ v.l v.m v.eq v.A v.a ]
      else if t == "VLevelSuc" then metaIdsVal v.pred
      else if t == "VLevelMax" then metaIdsVal v.lhs ++ metaIdsVal v.rhs
      else if t == "VOpaqueLam" then metaIdsVal v.piTy
      else [ ]
    else [ ];

  mentionsOf = vals: unique (concatMap metaIdsVal vals);

  occurs = id: v:
    builtins.elem id (metaIdsVal v);

  spineArg = frame:
    if (frame.tag or null) == "EApp" then frame.arg else null;

  isVar = v:
    builtins.isAttrs v && (v.tag or null) == "VNe" && (v.spine or [ ]) == [ ];

  levelsInElim = frame:
    let t = frame.tag or null;
    in
    if t == "EApp" then levelsVal frame.arg
    else if t == "EBootSumElim" then concatMap levelsVal [ frame.left frame.right frame.motive frame.onLeft frame.onRight ]
    else if t == "EBootJ" then concatMap levelsVal [ frame.type frame.lhs frame.motive frame.base frame.rhs ]
    else if t == "EStrEq" then levelsVal frame.arg
    else if t == "EDescInd" then concatMap levelsVal [ frame.D frame.motive frame.step frame.i ]
    else if t == "ELiftElim" then concatMap levelsVal [ frame.l frame.m frame.eq frame.A ]
    else if t == "ESquashElim" then concatMap levelsVal [ frame.A frame.B frame.f ]
    else if t == "EInterpD" then concatMap levelsVal [ frame.level frame.I frame.X frame.i ]
    else if t == "EAllD" then concatMap levelsVal [ frame.level frame.I frame.K frame.X frame.M frame.i frame.d ]
    else if t == "EEverywhereD" then concatMap levelsVal [ frame.level frame.I frame.K frame.X frame.M frame.ih frame.i frame.d ]
    else [ ];

  levelsVal = v:
    if isVMeta v then concatMap levelsInElim (v.spine or [ ])
    else if builtins.isAttrs v then
      let t = v.tag or null;
      in
      if t == "VNe" then [ v.level ] ++ concatMap levelsInElim (v.spine or [ ])
      else if t == "VLam" || t == "VPi" then levelsVal v.domain
      else if t == "VSigma" then levelsVal v.fst
      else if t == "VPair" then levelsVal v.fst ++ levelsVal v.snd
      else if t == "VBootSum" then levelsVal v.left ++ levelsVal v.right
      else if t == "VBootInl" || t == "VBootInr" then levelsVal v.left ++ levelsVal v.right ++ levelsVal v.val
      else if t == "VBootEq" then concatMap levelsVal [ v.type v.lhs v.rhs ]
      else if t == "VSquash" then levelsVal v.A
      else if t == "VSquashIntro" then levelsVal v.a
      else if t == "VDesc" then levelsVal v.level ++ levelsVal v.I
      else if t == "VMu" then concatMap levelsVal [ v.I v.D v.i ]
      # Canonical-form short-circuit: see metaIdsVal above.
      else if t == "VDescCon" then
        if v ? _canonRef
        then concatMap levelsVal (v._canonRef.params or [ ])
        else concatMap levelsVal [ v.D v.i v.d ]
      else if t == "VInterpD" then concatMap levelsVal [ v.level v.I v.D v.X v.i ]
      else if t == "VAllD" then concatMap levelsVal [ v.level v.I v.D v.K v.X v.M v.i v.d ]
      else if t == "VEverywhereD" then concatMap levelsVal [ v.level v.I v.D v.K v.X v.M v.ih v.i v.d ]
      else if t == "VLift" then concatMap levelsVal [ v.l v.m v.eq v.A ]
      else if t == "VLiftIntro" then concatMap levelsVal [ v.l v.m v.eq v.A v.a ]
      else if t == "VLevelSuc" then levelsVal v.pred
      else if t == "VLevelMax" then levelsVal v.lhs ++ levelsVal v.rhs
      else if t == "VOpaqueLam" then levelsVal v.piTy
      else [ ]
    else [ ];

  spineVars = spine:
    let args = map spineArg spine;
    in if builtins.any (x: x == null || !(isVar x)) args then null else map (x: x.level) args;

  allDistinct = xs:
    builtins.length xs == builtins.length (unique xs);

  patternSpine = spine:
    let vars = spineVars spine;
    in vars != null && allDistinct vars;

  noMeta = v: metaIdsVal v == [ ];

  subsetOf = xs: ys:
    builtins.all (x: builtins.elem x ys) xs;

  quoteDomain = d: ty:
    let q = builtins.tryEval (fx.tc.quote.quote d ty);
    in if q.success then q.value else T.mkUnit;

  lamSolution = vars: metaType: rhs:
    let
      n = builtins.length vars;
      body = fx.tc.quote.quote n rhs;
      build = i: ty: inner:
        if i < 0 then inner
        else
          let
            pi = if builtins.isAttrs ty && (ty.tag or null) == "VPi" then ty else null;
            domain = if pi != null then pi.domain else V.vUnit;
            nextTy =
              if pi != null
              then E.instantiate pi.closure (V.freshVar i)
              else null;
          in
          T.mkLam "_" (quoteDomain i domain) (build (i - 1) nextTy inner);
      tm = build (n - 1) (metaType.ty or null) body;
    in
    E.eval [ ] tm;

  patternSolve = m: rhs: state:
    let
      vars = spineVars (m.spine or [ ]);
      rawRhsLevels = levelsVal rhs;
      rhsLevels = unique rawRhsLevels;
    in
    if vars != null && allDistinct rawRhsLevels && subsetOf rhsLevels vars && noMeta rhs then {
      state = self.solveMeta m.id (lamSolution vars (m.type or { }) rhs) state;
      result = { status = "solved"; };
    } else {
      state = state;
      result = { status = "postponed"; reason = "pattern-spine-not-inverted"; };
    };

  directMetaSolve = m: rhs: state:
    if occurs m.id rhs then {
      state = state;
      result = { status = "failed"; reason = "occurs-check"; };
    } else if (m.spine or [ ]) == [ ] then {
      state = self.solveMeta m.id rhs state;
      result = { status = "solved"; };
    } else if patternSpine (m.spine or [ ]) then
      patternSolve m rhs state
    else {
      state = state;
      result = { status = "postponed"; reason = "non-pattern-spine"; };
    };

  rigidConv = c:
    ! builtins.any (v: metaIdsVal v != [ ]) [ c.lhs c.rhs (c.type or V.vUnit) ]
    && C.conv (c.depth or 0) c.lhs c.rhs;

  simplifyConv = c: state:
    let
      lhs = if isVMeta c.lhs then self.forceMeta c.lhs state else c.lhs;
      rhs = if isVMeta c.rhs then self.forceMeta c.rhs state else c.rhs;
      c1 = c // { inherit lhs rhs; mentions = mentionsOf [ lhs rhs (c.type or V.vUnit) ]; };
    in
    if rigidConv c1 then { state = state; constraint = c1 // { status = "solved"; }; }
    else if isVMeta lhs then
      let r = directMetaSolve lhs rhs state;
      in { state = r.state; constraint = c1 // r.result; }
    else if isVMeta rhs then
      let r = directMetaSolve rhs lhs state;
      in { state = r.state; constraint = c1 // r.result; }
    else { state = state; constraint = c1 // { status = "postponed"; }; };

  simplifyPlicityAwait = c: state:
    let
      awaited = c.awaiting or null;
      entry = if awaited == null then null else self.lookupMeta state awaited;
      solved = entry != null && self.isSolved entry;
    in
    if solved
    then { state = state; constraint = c // { status = "solved"; }; }
    else { state = state; constraint = c // { status = "postponed"; }; };

  simplifyConstraint = c: state:
    if (c.tag or null) == "conv" && c ? lhs && c ? rhs
    then simplifyConv (self.mkConstraint c) state
    else if (c.tag or null) == "plicity-await"
    then simplifyPlicityAwait (self.mkConstraint c) state
    else { state = state; constraint = self.mkConstraint c; };

  addAndSimplifyConstraint = c: state:
    let
      simplified = simplifyConstraint c state;
      added = self.addConstraint simplified.constraint simplified.state;
    in
    {
      id = added.id;
      state = added.state;
    };

  processActiveConstraints = state:
    let
      step = acc: c:
        if (c.status or null) != "active" then acc // { constraints = acc.constraints ++ [ c ]; }
        else
          let r = simplifyConstraint (c // { status = "postponed"; }) (acc // { constraints = [ ]; });
          in r.state // { constraints = acc.constraints ++ [ r.constraint ]; };
    in
    builtins.foldl' step (state // { constraints = [ ]; }) (state.constraints or [ ]);

  sigmaFlatten = id: state:
    let
      entry = self.lookupMeta state id;
      ty = if entry != null && entry ? type && builtins.isAttrs entry.type && entry.type ? ty then entry.type.ty else null;
    in
    if ty != null && (ty.tag or null) == "VSigma" && self.isHole entry then
      let
        fstAlloc = self.freshMetaInState { ctx = entry.type.ctx or { }; ty = ty.fst; } state;
        # Meta-aware instantiation: `fstAlloc.meta` is a fresh VMeta;
        # kernel `instantiate` cannot read it from the closure body.
        # See `tc/elaborate/eval-overlay.nix`.
        sndTy = fx.tc.elaborate.instantiateOverlay ty.closure fstAlloc.meta;
        sndAlloc = self.freshMetaInState { ctx = entry.type.ctx or { }; ty = sndTy; } fstAlloc.state;
        pair = V.vPair fstAlloc.meta sndAlloc.meta;
      in
      self.solveMeta id pair sndAlloc.state
    else state;

in
{
  scope = {
    metaIdsVal = api.leaf {
      value = metaIdsVal;
      description = "metaIdsVal v: collect metavariable ids referenced by an elaborator value and its spine payloads.";
      signature = "metaIdsVal : ElabVal -> [Int]";
      tests = {
        "metaIdsVal-vmeta" = {
          expr = metaIdsVal (mkVMeta 5 [ ] { ctx = { }; ty = V.vUnit; });
          expected = [ 5 ];
        };
      };
    };
    mentionsOf = api.leaf {
      value = mentionsOf;
      description = "mentionsOf vals: collect unique metavariable ids referenced by a list of elaborator values.";
      signature = "mentionsOf : [ElabVal] -> [Int]";
    };
    occurs = api.leaf {
      value = occurs;
      description = "occurs id v: true when `v` references metavariable `id`.";
      signature = "occurs : Int -> ElabVal -> Bool";
      tests = {
        "occurs-detects-self" = {
          expr = occurs 0 (mkVMeta 0 [ (V.eApp V.vTt) ] { ctx = { }; ty = V.vUnit; });
          expected = true;
        };
      };
    };
    patternSpine = api.leaf {
      value = patternSpine;
      description = "patternSpine spine: true for application spines whose arguments are distinct bound variables.";
      signature = "patternSpine : Spine -> Bool";
      tests = {
        "patternSpine-distinct-vars" = {
          expr = patternSpine [ (V.eApp (V.vNe 0 [ ])) (V.eApp (V.vNe 1 [ ])) ];
          expected = true;
        };
        "patternSpine-rejects-duplicate" = {
          expr = patternSpine [ (V.eApp (V.vNe 0 [ ])) (V.eApp (V.vNe 0 [ ])) ];
          expected = false;
        };
      };
    };
    levelsVal = api.leaf {
      value = levelsVal;
      description = "levelsVal v: collect neutral variable levels referenced by an elaborator value.";
      signature = "levelsVal : ElabVal -> [Level]";
    };
    simplifyConstraint = api.leaf {
      value = simplifyConstraint;
      description = "simplifyConstraint c state: locally simplify one constraint by rigid conversion, direct meta solving, occurs-check failure, or postponement.";
      signature = "simplifyConstraint : Constraint -> ElabState -> { state : ElabState; constraint : Constraint; }";
      tests = {
        "simplifyConstraint-direct-meta-solve" = {
          expr =
            let
              m = mkVMeta 0 [ ] { ctx = { }; ty = V.vUnit; };
              r = simplifyConstraint { tag = "conv"; lhs = m; rhs = V.vTt; type = V.vUnit; } {
                delta = { };
                metaOrder = [ ];
                constraints = [ ];
                mentions = { };
                nextMetaId = 0;
              };
            in
            { status = r.constraint.status; solved = r.state.delta."0".tag; };
          expected = { status = "solved"; solved = "Solved"; };
        };
        "simplifyConstraint-occurs-check-fails" = {
          expr =
            let
              m = mkVMeta 0 [ ] { ctx = { }; ty = V.vUnit; };
              rhs = mkVMeta 0 [ (V.eApp V.vTt) ] { ctx = { }; ty = V.vUnit; };
              r = simplifyConstraint { tag = "conv"; lhs = m; rhs = rhs; type = V.vUnit; } {
                delta = { };
                constraints = [ ];
                mentions = { };
              };
            in
            r.constraint.status;
          expected = "failed";
        };
        "simplifyConstraint-pattern-identity-solves" = {
          expr =
            let
              ty = V.vPi "_" V.vUnit (V.mkClosure [ ] T.mkUnit);
              m = mkVMeta 0 [ (V.eApp (V.vNe 0 [ ])) ] { ctx = { }; ty = ty; };
              r = simplifyConstraint { tag = "conv"; lhs = m; rhs = V.vNe 0 [ ]; type = V.vUnit; } {
                delta = { };
                metaOrder = [ ];
                constraints = [ ];
                mentions = { };
              };
              applied = E.vApp r.state.delta."0".tm V.vTt;
            in
            { status = r.constraint.status; tag = applied.tag; };
          expected = { status = "solved"; tag = "VTt"; };
        };
        "simplifyConstraint-pattern-pair-swaps-vars" = {
          expr =
            let
              m = mkVMeta 0 [
                (V.eApp (V.vNe 0 [ ]))
                (V.eApp (V.vNe 1 [ ]))
              ]
                { ctx = { }; ty = V.vUnit; };
              rhs = V.vPair (V.vNe 1 [ ]) (V.vNe 0 [ ]);
              r = simplifyConstraint { tag = "conv"; lhs = m; rhs = rhs; type = V.vUnit; } {
                delta = { };
                metaOrder = [ ];
                constraints = [ ];
                mentions = { };
              };
              applied = E.vApp (E.vApp r.state.delta."0".tm V.vTt) V.vUnit;
            in
            { status = r.constraint.status; fst = applied.fst.tag; snd = applied.snd.tag; };
          expected = { status = "solved"; fst = "VUnit"; snd = "VTt"; };
        };
      };
    };
    addAndSimplifyConstraint = api.leaf {
      value = addAndSimplifyConstraint;
      description = "addAndSimplifyConstraint c state: simplify a constraint, allocate its id, append it to 𝒦, and update mentions.";
      signature = "addAndSimplifyConstraint : Constraint -> ElabState -> { id : Int; state : ElabState; }";
    };
    processActiveConstraints = api.leaf {
      value = processActiveConstraints;
      description = "processActiveConstraints state: rerun local simplification for active constraints and preserve non-active constraints.";
      signature = "processActiveConstraints : ElabState -> ElabState";
    };
    sigmaFlatten = api.leaf {
      value = sigmaFlatten;
      description = "sigmaFlatten id state: replace an unsolved Sigma-typed meta with a pair of freshly allocated component metas.";
      signature = "sigmaFlatten : Int -> ElabState -> ElabState";
      tests = {
        "sigmaFlatten-solves-sigma-hole" = {
          expr =
            let
              sigma = V.vSigma "_" V.vUnit (V.mkClosure [ ] T.mkUnit);
              st = sigmaFlatten 0 {
                delta = { "0" = self.mkHole 0 { ctx = { }; ty = sigma; }; };
                metaOrder = [ 0 ];
                constraints = [ ];
                mentions = { };
                nextMetaId = 1;
              };
            in
            {
              solved = st.delta."0".tag;
              pair = st.delta."0".tm.tag;
              metas = st.metaOrder;
            };
          expected = { solved = "Solved"; pair = "VPair"; metas = [ 0 1 2 ]; };
        };
      };
    };
  };

}
