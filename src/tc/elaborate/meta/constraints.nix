{ self, fx, api, ... }:

let
  statusNames = [ "active" "postponed" "solved" "failed" ];

  unique = xs:
    builtins.foldl'
      (acc: x: if builtins.elem x acc then acc else acc ++ [ x ])
      [ ]
      xs;

  normalizeStatus = status:
    if builtins.elem status statusNames then status else "postponed";

  registerMentions = mentions: cid: index:
    builtins.foldl'
      (acc: id:
        let key = toString id;
        in acc // { ${key} = (acc.${key} or [ ]) ++ [ cid ]; }
      )
      index
      mentions;

  mkConstraint = c:
    c // {
      position = c.position or null;
      mentions = unique (c.mentions or [ ]);
      status = normalizeStatus (c.status or "postponed");
    };

  addConstraint = c: state:
    let
      cid = state.nextConstraintId or 0;
      constraint = mkConstraint (c // { id = cid; });
    in
    {
      id = cid;
      state = state // {
        constraints = (state.constraints or [ ]) ++ [ constraint ];
        mentions = registerMentions constraint.mentions cid (state.mentions or { });
        nextConstraintId = cid + 1;
      };
    };

  updateConstraint = cid: f: state:
    state // {
      constraints = map
        (c: if (c.id or null) == cid then f c else c)
        (state.constraints or [ ]);
    };

  markConstraint = cid: status: extra: state:
    updateConstraint cid (c: c // extra // { status = normalizeStatus status; }) state;

in
{
  scope = {
    mkConstraint = api.leaf {
      value = mkConstraint;
      description = "mkConstraint c: normalize a constraint record with default position, mentions, and status fields.";
      signature = "mkConstraint : AttrSet -> Constraint";
      tests = {
        "mkConstraint-default-status" = {
          expr = (mkConstraint { lhs = null; rhs = null; }).status;
          expected = "postponed";
        };
      };
    };
    addConstraint = api.leaf {
      value = addConstraint;
      description = "addConstraint c state: allocate a constraint id, append to 𝒦, and register watcher mentions.";
      signature = "addConstraint : Constraint -> ElabState -> { id : Int; state : ElabState; }";
      tests = {
        "addConstraint-registers-mention" = {
          expr =
            let
              r = addConstraint { lhs = null; rhs = null; mentions = [ 7 ]; } {
                constraints = [ ];
                mentions = { };
                nextConstraintId = 0;
              };
            in
            r.state.mentions."7";
          expected = [ 0 ];
        };
      };
    };
    updateConstraint = api.leaf {
      value = updateConstraint;
      description = "updateConstraint cid f state: update one constraint in 𝒦 by id.";
      signature = "updateConstraint : Int -> (Constraint -> Constraint) -> ElabState -> ElabState";
    };
    markConstraint = api.leaf {
      value = markConstraint;
      description = "markConstraint cid status extra state: update one constraint status and merge extra diagnostic fields.";
      signature = "markConstraint : Int -> String -> AttrSet -> ElabState -> ElabState";
    };
    registerMentions = api.leaf {
      value = registerMentions;
      description = "registerMentions mentions cid index: add a constraint id to every mentioned metavariable watcher list.";
      signature = "registerMentions : [Int] -> Int -> MentionsIndex -> MentionsIndex";
    };
  };

}
