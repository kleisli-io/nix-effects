{ self, fx, api, ... }:

let
  mkVMeta = id: spine: type:
    { _vTag = "VMeta"; inherit id spine type; };

  mkHole = id: type: {
    tag = "Hole";
    inherit id type;
  };

  mkSolved = id: tm: type: {
    tag = "Solved";
    inherit id tm type;
  };

  isHole = m:
    builtins.isAttrs m && (m.tag or null) == "Hole";

  isSolved = m:
    builtins.isAttrs m && (m.tag or null) == "Solved";

  freshMetaInState = type: state:
    let
      id = state.nextMetaId or 0;
      key = toString id;
      meta = mkVMeta id [ ] type;
    in
    {
      inherit meta;
      state = state // {
        delta = (state.delta or { }) // { ${key} = mkHole id type; };
        metaOrder = (state.metaOrder or [ ]) ++ [ id ];
        nextMetaId = id + 1;
      };
    };
in
{
  scope = {
    mkHole = api.leaf {
      value = mkHole;
      description = "mkHole id type: construct an unsolved metavariable-context entry.";
      signature = "mkHole : Int -> MetaType -> MetaEntry";
      tests = {
        "mkHole-tag" = {
          expr = (mkHole 3 fx.tc.value.vUnit).tag;
          expected = "Hole";
        };
      };
    };
    mkSolved = api.leaf {
      value = mkSolved;
      description = "mkSolved id tm type: construct a solved metavariable-context entry.";
      signature = "mkSolved : Int -> ElabVal -> MetaType -> MetaEntry";
      tests = {
        "mkSolved-tag" = {
          expr = (mkSolved 3 fx.tc.value.vTt fx.tc.value.vUnit).tag;
          expected = "Solved";
        };
      };
    };
    isHole = api.leaf {
      value = isHole;
      description = "isHole m: true when a metavariable-context entry is unsolved.";
      signature = "isHole : MetaEntry -> Bool";
      tests = {
        "isHole-true" = {
          expr = isHole (mkHole 0 fx.tc.value.vUnit);
          expected = true;
        };
      };
    };
    isSolved = api.leaf {
      value = isSolved;
      description = "isSolved m: true when a metavariable-context entry carries a solution.";
      signature = "isSolved : MetaEntry -> Bool";
      tests = {
        "isSolved-true" = {
          expr = isSolved (mkSolved 0 fx.tc.value.vTt fx.tc.value.vUnit);
          expected = true;
        };
      };
    };
    freshMetaInState = api.leaf {
      value = freshMetaInState;
      description = "freshMetaInState type state: allocate a new `VMeta` and append a matching Hole entry to Δ.";
      signature = "freshMetaInState : MetaType -> ElabState -> { meta : VMeta; state : ElabState; }";
      tests = {
        "freshMetaInState-allocates-id" = {
          expr =
            let
              r = freshMetaInState { ctx = { }; ty = fx.tc.value.vUnit; } {
                delta = { };
                metaOrder = [ ];
                nextMetaId = 0;
              };
            in
            { id = r.meta.id; next = r.state.nextMetaId; has = r.state.delta ? "0"; };
          expected = { id = 0; next = 1; has = true; };
        };
      };
    };
  };

}
