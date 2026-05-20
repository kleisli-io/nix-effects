# Path: list of Position segments naming a structural descent from a
# validation root to a failure site.
#
# A path is `[Position]` — segments are produced by the canonical
# constructors in `fx.diag.positions` (`P.Field name`, `P.Elem i`,
# `P.Tag tag`, `P.Tuple i`, the ~30 nullary description/MLTT positions).
# This module provides only the list-level operations: `empty`,
# `extend`, `render`, `renderAll`. Construction of individual segments
# uses `fx.diag.positions` directly.
{ self, fx, api, ... }:

let
  P = fx.diag.positions;

  empty = [ ];

  extend = p: seg: p ++ [ seg ];

  render = seg: P.renderSegment seg;

  renderAll = segs: builtins.concatStringsSep "" (map render segs);

in
{
  scope = {
    path = api.leaf {
      value = {
        inherit empty extend render renderAll;
      };
      description = "path: list-level operations on a `[Position]` descent chain — `empty`, `extend`, `render`, `renderAll`. Position segments themselves are constructed via `fx.diag.positions` (`P.Field name`, `P.Elem i`, etc.); this module only handles the list assembly and pretty-rendering.";
      signature = "path : { empty, extend, render, renderAll }";
      doc = ''
        Operations on a path (a list of `Position` segments naming a
        structural descent from a validation root to a failure site):

        - `empty = []` is the root path.
        - `extend : Path -> Position -> Path` appends a segment.
        - `render : Position -> String` pretty-renders one segment.
        - `renderAll : Path -> String` concatenates rendered segments.

        Position segments are produced by `fx.diag.positions` (the
        canonical curried constructors `Field`, `Elem`, `Tag`, `Tuple`,
        plus the ~30 nullary description/MLTT positions). Handlers
        consume the same `Position` records regardless of whether they
        come from kernel descent or value-side `verify=` walks.
      '';
    };
  };

  tests = {
    "path-empty-is-list" = {
      expr = empty;
      expected = [ ];
    };
    "path-extend-appends" = {
      expr = extend (extend empty (P.Field "a")) (P.Elem 2);
      expected = [ (P.Field "a") (P.Elem 2) ];
    };
    "path-extend-preserves-order" = {
      expr =
        let
          p0 = empty;
          p1 = extend p0 (P.Field "outer");
          p2 = extend p1 (P.Field "inner");
        in
        map (s: s.name) p2;
      expected = [ "outer" "inner" ];
    };
    "path-render-field" = {
      expr = render (P.Field "age");
      expected = ".age";
    };
    "path-render-index" = {
      expr = render (P.Elem 3);
      expected = "[3]";
    };
    "path-render-branch" = {
      expr = render (P.Tag "Some");
      expected = "#Some";
    };
    "path-render-tuple" = {
      expr = render (P.Tuple 0);
      expected = "[0]";
    };
    "path-renderAll-empty" = {
      expr = renderAll empty;
      expected = "";
    };
    "path-renderAll-composes" = {
      expr = renderAll [
        (P.Field "user")
        (P.Field "addresses")
        (P.Elem 0)
        (P.Field "city")
      ];
      expected = ".user.addresses[0].city";
    };
    "path-renderAll-with-branch" = {
      expr = renderAll [
        (P.Tag "Right")
        (P.Field "value")
      ];
      expected = "#Right.value";
    };
  };

}
