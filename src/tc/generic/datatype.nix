# Generic datatype metadata normalization.
{ self, fx, lib, api, ... }:

let
  H = fx.tc.hoas;

  hasMeta = x: builtins.isAttrs x && x ? _dtypeMeta;

  peelSpine = node: args:
    if builtins.isAttrs node && (node._htag or null) == "app"
    then peelSpine node.fn ([ node.arg ] ++ args)
    else { head = node; inherit args; };

  normalizeField = f:
    let eq = f.eq or null; in f // {
      level = f.level or null;
      eq = eq;
      proof = f.proof or (eq != null);
      type = f.type or null;
      typeFn = f.typeFn or null;
      S = f.S or null;
      SFn = f.SFn or null;
      idxFn = f.idxFn or null;
      branchIdxFn = f.branchIdxFn or null;
      role = f.role or null;
      source = f.source or null;
    };

  normalizeConstructor = c:
    c // {
      fields = map normalizeField (c.fields or [ ]);
    };

  normalizeMeta = meta:
    let
      metaName = meta.name or "<anonymous>";
      constructors =
        if meta ? constructors then map normalizeConstructor meta.constructors
        else
          throw
            "generic.datatype.normalizeMetadata: metadata for '${metaName}' is missing constructors";
    in
    meta // {
      indexed = meta.indexed or false;
      params = meta.params or [ ];
      paramArgs = meta.paramArgs or [ ];
      indexTy = meta.indexTy or null;
      constructors = constructors;
    };

  withSpec = spec: meta:
    normalizeMeta (meta // {
      D = if spec ? D then spec.D else meta.D or null;
      T = if spec ? T then spec.T else meta.T or null;
      elim = if spec ? elim then spec.elim else meta.elim or null;
    });

  infoOf = x:
    if hasMeta x then withSpec x x._dtypeMeta
    else if builtins.isAttrs x && (x._htag or null) == "app" then
      let
        spine = peelSpine x [ ];
        head = spine.head;
        meta = head._dtypeMeta or null;
      in
      if meta == null then
        throw "generic.datatype.datatypeInfo: app head carries no _dtypeMeta"
      else if meta ? instantiate then
        normalizeMeta (meta.instantiate spine.args)
      else
        normalizeMeta meta
    else throw "generic.datatype.datatypeInfo: expected DataSpec or datatype HOAS type";

  findFirst = pred: xs:
    let
      go = i:
        if i == builtins.length xs then null
        else
          let x = builtins.elemAt xs i;
          in if pred x then x else go (i + 1);
    in
    go 0;
in
{
  scope = {
    isDatatype = api.leaf {
      value = x:
        hasMeta x
        || (builtins.isAttrs x
        && (x._htag or null) == "app"
        && (
          let head = (peelSpine x [ ]).head;
          in builtins.isAttrs head && head ? _dtypeMeta
        ));
      description = "isDatatype: predicate identifying values that carry `_dtypeMeta` directly, or app-spines whose head carries `_dtypeMeta` (instantiated polymorphic datatypes).";
      signature = "isDatatype : Any -> Bool";
    };

    normalizeMetadata = api.leaf {
      value = normalizeMeta;
      description = "normalizeMetadata: canonicalise a raw `_dtypeMeta` attrset — requires `constructors`, defaults `indexed`/`params`/`paramArgs`/`indexTy`, and pre-fills every field with `level`/`eq`/`proof`/`type`/`typeFn`/`S`/`SFn`/`idxFn`/`branchIdxFn`/`role`/`source` slots.";
      signature = "normalizeMetadata : Meta -> Meta";
    };

    datatypeInfo = api.leaf {
      value = infoOf;
      description = "datatypeInfo: produce normalised metadata from either a `DataSpec` (record with `_dtypeMeta`) or an `H.app` spine whose head is a polymorphic datatype; for polymorphic heads, applies `meta.instantiate` to the spine args.";
      signature = "datatypeInfo : DataSpec | Hoas -> Meta";
    };

    instantiate = api.leaf {
      value = spec: paramArgs:
        let meta = (infoOf spec);
        in
        if meta ? instantiate then normalizeMeta (meta.instantiate paramArgs)
        else if paramArgs == [ ] then meta
        else throw "generic.datatype.instantiate: '${meta.name}' is not polymorphic";
      description = "instantiate: apply parameter arguments to a polymorphic datatype `DataSpec`, returning the normalised meta for that instantiation; throws for non-polymorphic datatypes given non-empty `paramArgs`.";
      signature = "instantiate : DataSpec -> [Hoas] -> Meta";
    };

    constructors = api.leaf {
      value = info:
        (if info ? constructors then info else infoOf info).constructors;
      description = "constructors: extract the constructor list from a meta or `DataSpec` — accepts either a pre-normalised meta with `constructors` or a raw `DataSpec`, calling `datatypeInfo` for the latter.";
      signature = "constructors : Meta | DataSpec -> [Constructor]";
    };

    fields = api.leaf {
      value = con: con.fields or [ ];
      description = "fields: extract the field list from a constructor record; defaults to `[]` for constructors with no fields slot.";
      signature = "fields : Constructor -> [Field]";
    };

    constructorByName = api.leaf {
      value = info: name:
        let found = findFirst (c: c.name == name) (self.constructors info);
        in if found == null
        then throw "generic.datatype.constructorByName: unknown constructor '${name}'"
        else found;
      description = "constructorByName: lookup a constructor by name in a datatype's meta/`DataSpec`; throws on unknown name with a descriptive message.";
      signature = "constructorByName : Meta | DataSpec -> String -> Constructor";
    };

    constructorByIx = api.leaf {
      value = info: ix:
        let cs = self.constructors info;
        in if !(builtins.isInt ix) || ix < 0 || ix >= builtins.length cs
        then throw "generic.datatype.constructorByIx: index out of range: ${toString ix}"
        else builtins.elemAt cs ix;
      description = "constructorByIx: lookup a constructor by zero-based declaration-order index; throws on out-of-range or non-integer index.";
      signature = "constructorByIx : Meta | DataSpec -> Int -> Constructor";
    };

    targetIndex = api.leaf {
      value = con: prev:
        if con ? targetIdx && con.targetIdx != null then con.targetIdx prev
        else throw "generic.datatype.targetIndex: constructor '${con.name}' has no target index function";
      description = "targetIndex: compute a constructor's target index in the datatype's index type — applies `con.targetIdx prev` where `prev` is the materialised previous-field record; throws if no `targetIdx` function is present.";
      signature = "targetIndex : Constructor -> AttrSet -> Hoas";
    };

    fieldType = api.leaf {
      value = field: prev:
        if field ? typeFn && field.typeFn != null then field.typeFn prev
        else if field ? type && field.type != null then field.type
        else throw "generic.datatype.fieldType: field '${field.name}' has no resolved type";
      description = "fieldType: resolve a field's HOAS type — prefers `field.typeFn prev` (dependent fields) over `field.type` (concrete); throws if neither slot is filled.";
      signature = "fieldType : Field -> AttrSet -> Hoas";
    };

    fieldRole = api.leaf {
      value = field: field.role or null;
      description = "fieldRole: extract the `role` annotation from a field, or `null` if unset. Used by generic derivations to distinguish e.g. proof-bearing fields from ordinary payload.";
      signature = "fieldRole : Field -> String | null";
    };
  };

  tests = {
    "datatype-info-mono-constructors" = {
      expr =
        let
          G = self;
          Pair = H.datatype "Pairish" [
            (H.con "mk" [ (H.field "left" H.nat) (H.field "right" H.bool) ])
          ];
          info = G.datatypeInfo Pair;
        in
        {
          name = info.name;
          n = builtins.length (G.constructors info);
          con = (G.constructorByIx info 0).name;
          byName = (G.constructorByName info "mk").index;
          fields = map (f: f.name) (G.fields (G.constructorByIx info 0));
        };
      expected = {
        name = "Pairish";
        n = 1;
        con = "mk";
        byName = 0;
        fields = [ "left" "right" ];
      };
    };

    "datatype-info-mono-field-type" = {
      expr =
        let
          G = self;
          Box = H.datatype "Box" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          field = builtins.head (G.fields (G.constructorByName (G.datatypeInfo Box) "box"));
        in
        (G.fieldType field { })._htag;
      expected = "mu";
    };

    "datatype-info-poly-instantiates" = {
      expr =
        let
          G = self;
          Tree = H.datatypeP "Tree" [{ name = "A"; kind = H.u 0; }] (ps:
            let A = builtins.elemAt ps 0; in [
              (H.con "leaf" [ (H.field "value" A) ])
              (H.con "node" [ (H.recField "left") (H.recField "right") ])
            ]);
          info = G.datatypeInfo (H.app Tree.T H.nat);
          leaf = G.constructorByName info "leaf";
          field = builtins.head (G.fields leaf);
        in
        {
          name = info.name;
          params = builtins.length info.params;
          args = builtins.length info.paramArgs;
          constructors = map (c: c.name) (G.constructors info);
          fieldType = (G.fieldType field { })._htag;
        };
      expected = {
        name = "Tree";
        params = 1;
        args = 1;
        constructors = [ "leaf" "node" ];
        fieldType = "mu";
      };
    };

    "datatype-info-target-index" = {
      expr =
        let
          G = self;
          Pair = H.datatype "Pairish" [
            (H.con "mk" [ (H.field "left" H.nat) ])
          ];
          con = G.constructorByName (G.datatypeInfo Pair) "mk";
        in
        (G.targetIndex con { })._htag;
      expected = "tt";
    };
  };

}
