{ self, fx, api, ... }:

let
  V = fx.tc.value;
  E = fx.tc.eval;

  isVMeta = v:
    builtins.isAttrs v && (v._vTag or null) == "VMeta";

  extendVMeta = v: frame:
    v // { spine = (v.spine or [ ]) ++ [ frame ]; };

  lookupMeta = state: id:
    let key = toString id;
    in if (state.delta or { }) ? ${key} then state.delta.${key} else null;

  extendMeta = id: type: state:
    let key = toString id;
    in state // {
      delta = (state.delta or { }) // { ${key} = self.mkHole id type; };
      metaOrder =
        if builtins.elem id (state.metaOrder or [ ])
        then state.metaOrder or [ ]
        else (state.metaOrder or [ ]) ++ [ id ];
      nextMetaId =
        if (state.nextMetaId or 0) <= id then id + 1 else state.nextMetaId or 0;
    };

  solvedType = old: fallback:
    if builtins.isAttrs old && old ? type then old.type else fallback;

  replaceConstraint = target: f: constraints:
    map (c: if (c.id or null) == target then f c else c) constraints;

  reawakenMentions = ids: state:
    let
      cidLists = map (id: (state.mentions or { }).${toString id} or [ ]) ids;
      unique = xs:
        builtins.foldl'
          (acc: x: if builtins.elem x acc then acc else acc ++ [ x ])
          [ ]
          xs;
      cids = unique (builtins.concatLists cidLists);
      wake = c:
        if (c.status or null) == "postponed"
        then c // { status = "active"; }
        else c;
    in
    state // {
      constraints =
        builtins.foldl'
          (cs: cid: replaceConstraint cid wake cs)
          (state.constraints or [ ])
          cids;
    };

  solveMeta = id: tm: state:
    let
      key = toString id;
      old = lookupMeta state id;
      next = state // {
        delta = (state.delta or { }) // {
          ${key} = self.mkSolved id tm (solvedType old null);
        };
        metaOrder =
          if builtins.elem id (state.metaOrder or [ ])
          then state.metaOrder or [ ]
          else (state.metaOrder or [ ]) ++ [ id ];
      };
    in
    reawakenMentions [ id ] next;

  forceMeta = v: state:
    let
      entry = lookupMeta state v.id;
      replayFrame = acc: frame:
        let t = frame.tag or null;
        in
        if t == "EApp" then if isVMeta acc then extendVMeta acc frame else E.vApp acc frame.arg
        else if t == "EFst" then if isVMeta acc then extendVMeta acc frame else E.vFst acc
        else if t == "ESnd" then if isVMeta acc then extendVMeta acc frame else E.vSnd acc
        else if t == "EBootSumElim" then if isVMeta acc then extendVMeta acc frame else E.vBootSumElim frame.left frame.right frame.motive frame.onLeft frame.onRight acc
        else if t == "EBootJ" then if isVMeta acc then extendVMeta acc frame else E.vBootJ frame.type frame.lhs frame.motive frame.base frame.rhs acc
        else if t == "ESquashElim" then if isVMeta acc then extendVMeta acc frame else E.vSquashElim frame.A frame.B frame.f acc
        else if t == "ELiftElim" then if isVMeta acc then extendVMeta acc frame else E.vLiftElimF frame.l frame.m frame.eq frame.A acc
        else if t == "EDescInd" then if isVMeta acc then extendVMeta acc frame else E.vDescInd frame.D frame.motive frame.step frame.i acc
        else if t == "EInterpD" then if isVMeta acc then extendVMeta acc frame else E.vInterpD frame.level frame.I acc frame.X frame.i
        else if t == "EAllD" then if isVMeta acc then extendVMeta acc frame else E.vAllD frame.level frame.I acc frame.K frame.X frame.M frame.i frame.d
        else if t == "EEverywhereD" then if isVMeta acc then extendVMeta acc frame else E.vEverywhereD frame.level frame.I acc frame.K frame.X frame.M frame.ih frame.i frame.d
        else acc;
    in
    if entry != null && self.isSolved entry
    then builtins.foldl' replayFrame entry.tm (v.spine or [ ])
    else v;

in
{
  scope = {
    lookupMeta = api.leaf {
      value = lookupMeta;
      description = "lookupMeta state id: read a Δ entry by metavariable id, returning null when absent.";
      signature = "lookupMeta : ElabState -> Int -> MetaEntry | Null";
      tests = {
        "lookupMeta-missing" = {
          expr = lookupMeta { delta = { }; } 0;
          expected = null;
        };
      };
    };
    extendMeta = api.leaf {
      value = extendMeta;
      description = "extendMeta id type state: add a Hole entry to Δ and advance the fresh-id counter past it.";
      signature = "extendMeta : Int -> MetaType -> ElabState -> ElabState";
      tests = {
        "extendMeta-adds-hole" = {
          expr = (extendMeta 2 V.vUnit { delta = { }; metaOrder = [ ]; nextMetaId = 0; }).delta."2".tag;
          expected = "Hole";
        };
      };
    };
    solveMeta = api.leaf {
      value = solveMeta;
      description = "solveMeta id tm state: replace a Δ entry with a Solved entry and reawaken constraints watching that id.";
      signature = "solveMeta : Int -> ElabVal -> ElabState -> ElabState";
      tests = {
        "solveMeta-reawakens-watchers" = {
          expr =
            let
              st = solveMeta 0 V.vTt {
                delta = { "0" = self.mkHole 0 V.vUnit; };
                metaOrder = [ 0 ];
                mentions = { "0" = [ 4 ]; };
                constraints = [{ id = 4; status = "postponed"; }];
              };
            in
            st.constraints;
          expected = [{ id = 4; status = "active"; }];
        };
      };
    };
    reawakenMentions = api.leaf {
      value = reawakenMentions;
      description = "reawakenMentions ids state: mark postponed constraints watching solved metavariables active.";
      signature = "reawakenMentions : [Int] -> ElabState -> ElabState";
    };
    forceMeta = api.leaf {
      value = forceMeta;
      description = "forceMeta v state: if `v` is solved in Δ, replay its captured spine over the solution.";
      signature = "forceMeta : VMeta -> ElabState -> ElabVal";
      tests = {
        "forceMeta-unsolved-stays-meta" = {
          expr =
            let m = { _vTag = "VMeta"; id = 0; spine = [ ]; type = { ctx = { }; ty = V.vUnit; }; };
            in (forceMeta m { delta = { }; })._vTag;
          expected = "VMeta";
        };
        "forceMeta-replays-application" = {
          expr =
            let
              id = V.vLam "x" V.vUnit (V.mkClosure [ ] fx.tc.term.mkVar 0);
              m = {
                _vTag = "VMeta";
                id = 0;
                spine = [ (V.eApp V.vTt) ];
                type = { ctx = { }; ty = V.vUnit; };
              };
            in
            (forceMeta m { delta = { "0" = self.mkSolved 0 id null; }; }).tag;
          expected = "VTt";
        };
      };
    };
  };

}
