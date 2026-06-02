# Generic value views over generated datatypes.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  Elab = fx.tc.elaborate;

  typeOf = x:
    if builtins.isAttrs x && x ? T then x.T else x;

  isHoas = x:
    builtins.isAttrs x && x ? _htag;

  foldValue = ty: cases: value:
    let
      hoasTy = typeOf ty;
      info = self.datatypeInfo ty;
      go = v:
        let
          record = self.view hoasTy v;
          con =
            if builtins.isAttrs record && record ? _con
            then self.constructorByName info record._con
            else throw "generic.value.fold: expected constructor-record view";
          fieldValue = f:
            let raw = builtins.getAttr f.name record; in
            if f.kind == "recAt" then go raw else raw;
          fields = builtins.listToAttrs (map
            (f: {
              name = f.name;
              value = fieldValue f;
            })
            (con.fields or [ ]));
          caseFn =
            if cases ? ${con.name} then builtins.getAttr con.name cases
            else if cases ? default then cases.default con
            else throw "generic.value.fold: missing case '${con.name}'";
        in
        caseFn fields;
    in
    go value;

  mapChildValues = ty: childMapper: value:
    let
      hoasTy = typeOf ty;
      info = self.datatypeInfo ty;
      record = self.view hoasTy value;
      con =
        if builtins.isAttrs record && record ? _con
        then self.constructorByName info record._con
        else throw "generic.value.mapChildren: expected constructor-record view";
      mappedFields = builtins.listToAttrs (map
        (f: {
          name = f.name;
          value =
            if f.kind == "recAt"
            then childMapper f (builtins.getAttr f.name record)
            else builtins.getAttr f.name record;
        })
        (con.fields or [ ]));
    in
    self.view hoasTy (self.review hoasTy (record // mappedFields));
in
{
  scope = {
    review = api.leaf {
      value = ty: value:
        Elab.elaborateValue (typeOf ty) value;
      description = "review: Nix-value → HOAS-value — friendly alias of `Elab.elaborateValue` taking the type either as `Hoas` directly or via a `.T` field (datatype outputs); inverse of `view`.";
      signature = "review : Hoas | { T : Hoas; ... } -> NixVal -> Hoas";
    };

    view = api.leaf {
      value = ty: value:
        let
          hoasTy = typeOf ty;
          hoasValue =
            if isHoas value then value else self.review hoasTy value;
        in
        Elab.extract hoasTy (E.eval [ ] (H.elab hoasValue));
      description = "view: HOAS-value or Nix-value → Nix constructor-record — kernel-elaborates if given a Nix value, then `Elab.extract`s back to a tagged record (`_con` for record/variant datatypes, primitive for leaf types).";
      signature = "view : Hoas | { T : Hoas; ... } -> Hoas | NixVal -> NixVal";
      doc = ''
        Idempotent on the HOAS form: when `value` is already an HOAS
        tree (`_htag` present), it skips re-elaboration. Otherwise
        round-trips through `review` to produce an HOAS value, then
        evaluates and extracts.

        Returns a constructor-record `{ _con = "name"; ...fields }` for
        record/variant datatypes. Primitive values (Nat, String, ...)
        flatten to their native Nix form. Cross-ref: `fromConstructorRecord`
        is the alias name used in the datatype-generic API surface.
      '';
    };

    toConstructorRecord = api.leaf {
      value = self.view;
      description = "toConstructorRecord: alias of `view` — the datatype-generic name for the value-to-record direction; preferred when expressing intent over generated datatypes.";
      signature = "toConstructorRecord : Hoas | { T : Hoas; ... } -> Hoas | NixVal -> NixVal";
    };

    fromConstructorRecord = api.leaf {
      value = self.review;
      description = "fromConstructorRecord: alias of `review` — the datatype-generic name for the record-to-value direction; preferred when expressing intent over generated datatypes.";
      signature = "fromConstructorRecord : Hoas | { T : Hoas; ... } -> NixVal -> Hoas";
    };

    fold = api.leaf {
      value = foldValue;
      description = "fold: structural fold over a generated datatype value — dispatches on the constructor's name in `cases`, recursing into `recAt` fields before invoking the case function with the record of materialised fields.";
      signature = "fold : Hoas -> { <ctor> = Fields -> R; default? : Constructor -> Fields -> R; } -> NixVal -> R";
      doc = ''
        Each case in `cases` receives a record of materialised fields
        keyed by field name; `recAt` fields have already been folded
        recursively, all other fields appear as raw Nix values. Missing
        constructors fall through to `cases.default constructor` if
        present, else throw `"missing case '<name>'"`.

        Implementation note: walks via `view` + `constructorByName`,
        so the input must be either a constructor-record or a value
        elaborable via `review`. Non-attrset value views (e.g., raw
        `Nat`) bypass this function — caller folds over the primitive
        directly.
      '';
    };

    mapChildren = api.leaf {
      value = mapChildValues;
      description = "mapChildren: rewrite a single layer of a generated datatype — for each `recAt` field, apply `childMapper field child`; non-recursive fields pass through unchanged. The result is `view`-normalised so it round-trips with `review`.";
      signature = "mapChildren : Hoas -> (Field -> NixVal -> NixVal) -> NixVal -> NixVal";
    };
  };

  tests = {
    "value-review-view-nat" = {
      expr = let V = self; in V.view H.nat (V.review H.nat (V.view H.nat 3));
      expected = 3;
    };

    "value-review-view-list" = {
      expr =
        let
          V = self;
          T = H.listOf H.nat;
        in
        V.view T (V.review T (V.view T [ 0 1 2 ]));
      expected = [ 0 1 2 ];
    };

    "value-review-view-sum" = {
      expr =
        let
          V = self;
          T = H.sum H.nat H.bool;
          value = { _tag = "Right"; value = true; };
        in
        V.view T (V.review T (V.view T value));
      expected = { _tag = "Right"; value = true; };
    };

    # Sum arms that are named datatypes must keep their constructor/field
    # names through extraction (the arms live in the app-spine, not in the
    # reified anonymous sum).
    "value-review-view-sum-of-named-datatypes" = {
      expr =
        let
          V = self;
          Box = H.datatype "SumArmBox" [ (H.con "box" [ (H.field "n" H.nat) ]) ];
          Other = H.datatype "SumArmOther" [ (H.con "other" [ (H.field "b" H.bool) ]) ];
          T = H.sum Box.T Other.T;
          value = { _tag = "Left"; value = { _con = "box"; n = 5; }; };
        in
        V.view T (V.review T value);
      expected = { _tag = "Left"; value = { _con = "box"; n = 5; }; };
    };

    # A record field whose type is itself a named datatype must decode with
    # the inner constructor/field names, not positional `con0`/`_field0`.
    "value-review-view-nested-named-datatype-field" = {
      expr =
        let
          V = self;
          Inner = H.datatype "NestedInner" [ (H.con "mk" [ (H.field "n" H.nat) ]) ];
          Outer = H.datatype "NestedOuter" [
            (H.con "wrap" [ (H.field "inner" Inner.T) (H.field "tag" H.nat) ])
          ];
          record = { _con = "wrap"; inner = { _con = "mk"; n = 7; }; tag = 1; };
        in
        V.view Outer.T (V.review Outer.T record);
      expected = { _con = "wrap"; inner = { _con = "mk"; n = 7; }; tag = 1; };
    };

    "value-review-view-custom-tree" = {
      expr =
        let
          V = self;
          Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (H.con "leaf" [ (H.field "value" A) ])
              (H.con "node" [ (H.recField "left") (H.recField "right") ])
            ]);
          T = H.app Tree.T H.nat;
          record = {
            _con = "node";
            left = { _con = "leaf"; value = 0; };
            right = { _con = "leaf"; value = 1; };
          };
        in
        V.view T (V.review T (V.view T record));
      expected = {
        _con = "node";
        left = { _con = "leaf"; value = 0; };
        right = { _con = "leaf"; value = 1; };
      };
    };

    "value-review-view-custom-mono-tree" = {
      expr =
        let
          V = self;
          Tree = H.datatype "GenericMonoTree" [
            (H.con "leaf" [ (H.field "value" H.nat) ])
            (H.con "node" [ (H.recField "left") (H.recField "right") ])
          ];
          record = {
            _con = "node";
            left = { _con = "leaf"; value = 0; };
            right = {
              _con = "node";
              left = { _con = "leaf"; value = 1; };
              right = { _con = "leaf"; value = 2; };
            };
          };
        in
        V.view Tree.T (V.review Tree.T (V.view Tree.T record));
      expected = {
        _con = "node";
        left = { _con = "leaf"; value = 0; };
        right = {
          _con = "node";
          left = { _con = "leaf"; value = 1; };
          right = { _con = "leaf"; value = 2; };
        };
      };
    };

    "value-review-view-indexed-datatype" = {
      expr =
        let
          V = self;
          Indexed = H.datatypeI "GenericIndexedRoundtrip" H.bool [
            (H.conI "mk" [ (H.field "value" H.nat) ] (_: H.true_))
          ];
          T = H.app Indexed.T H.true_;
          record = { _con = "mk"; value = 3; };
        in
        V.view T (V.review T (V.view T record));
      expected = { _con = "mk"; value = 3; };
    };

    "value-review-custom-tree-checks" = {
      expr =
        let
          V = self;
          Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (H.con "leaf" [ (H.field "value" A) ])
              (H.con "node" [ (H.recField "left") (H.recField "right") ])
            ]);
          T = H.app Tree.T H.nat;
          record = {
            _con = "node";
            left = { _con = "leaf"; value = 0; };
            right = { _con = "leaf"; value = 1; };
          };
        in
          !((H.checkHoas T (V.review T record)) ? error);
      expected = true;
    };

    "value-review-rejects-unknown-constructor" = {
      expr =
        let
          V = self;
          Box = H.datatype "Box" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        (builtins.tryEval (V.review Box.T { _con = "nope"; value = 0; })).success;
      expected = false;
    };

    "value-review-rejects-missing-field" = {
      expr =
        let
          V = self;
          Box = H.datatype "Box" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        (builtins.tryEval (V.review Box.T { _con = "box"; })).success;
      expected = false;
    };

    "value-review-rejects-unknown-field" = {
      expr =
        let
          V = self;
          Box = H.datatype "Box" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        (builtins.tryEval (V.review Box.T {
          _con = "box";
          value = 0;
          extra = true;
        })).success;
      expected = false;
    };

    "value-fold-custom-tree-size" = {
      expr =
        let
          V = self;
          Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (H.con "leaf" [ (H.field "value" A) ])
              (H.con "node" [ (H.recField "left") (H.recField "right") ])
            ]);
          T = H.app Tree.T H.nat;
          record = {
            _con = "node";
            left = { _con = "leaf"; value = 0; };
            right = { _con = "leaf"; value = 1; };
          };
        in
        V.fold T
          {
            leaf = _: 1;
            node = fields: 1 + fields.left + fields.right;
          }
          record;
      expected = 3;
    };

    "value-map-children-custom-tree-identity" = {
      expr =
        let
          V = self;
          Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (H.con "leaf" [ (H.field "value" A) ])
              (H.con "node" [ (H.recField "left") (H.recField "right") ])
            ]);
          T = H.app Tree.T H.nat;
          record = {
            _con = "node";
            left = { _con = "leaf"; value = 0; };
            right = { _con = "leaf"; value = 1; };
          };
        in
        V.mapChildren T (_field: child: child) record;
      expected = {
        _con = "node";
        left = { _con = "leaf"; value = 0; };
        right = { _con = "leaf"; value = 1; };
      };
    };
  };

}
