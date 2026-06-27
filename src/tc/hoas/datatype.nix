# Datatype macro: declarative constructor signatures compile to a DataSpec
# record `{ name; D; T; <conName_i>; elim; _dtypeMeta }`. Plus the
# prelude instances (NatDT, ListDT, SumDT) and the surface forwarders
# (`nat`, `listOf`, `sum`, `zero`, `succ`, `nil`, `cons`, `inl`, `inr`)
# that route through the macro-generated constructors so the kernel's
# `dt-ctor-mono`/`dt-ctor-poly` chain-flatten path applies.
#
# A signature is a name and a non-empty ordered list of constructors;
# each constructor has a name and an ordered list of field
# specifications. The macro is a pure Nix function from the signature
# attrset to an attrset of HOAS terms; the kernel never learns about it.
{ self, api, ... }:

let
  # Field specification tags — invisible to consumers, used by conDesc /
  # mkCtor / stepTyOf to dispatch on field kind.
  _fieldMarker = "__nix-effects-datatype-field__";
  _conMarker = "__nix-effects-datatype-con__";
in
{
  scope = {
    # Field specifications. Each is a tagged attrset; position in the
    # constructor's field list is the position in the constructor's
    # argument list and in the payload spine.
    fieldAt = api.leaf {
      description = "fieldAt: universe-polymorphic field declarator — `fieldAt name level type` declares a field at an explicit sort level.";
      signature = "fieldAt : String -> Level -> Hoas -> { name; type; level; }";
      value = level: name: type:
        { _fieldTag = _fieldMarker; kind = "data"; inherit name level type; };
    };
    fieldDAt = api.leaf {
      description = "fieldDAt: universe-polymorphic dependent-field declarator — combines `fieldAt`'s explicit level with `fieldD`'s index dependence.";
      signature = "fieldDAt : String -> Level -> Hoas -> (Hoas -> Hoas) -> { name; type; level; indexFn; }";
      value = level: name: tyFn:
        { _fieldTag = _fieldMarker; kind = "dataD"; inherit name level; typeFn = tyFn; };
    };
    fieldAtWithEq = api.leaf {
      description = "fieldAtWithEq: fieldAt variant carrying an explicit bound-witness — supplies the `eq : Eq Level (max l k) k` proof for level-polymorphic positions.";
      signature = "fieldAtWithEq : String -> Level -> Hoas -> Hoas -> { name; type; level; eq; }";
      value = level: eq: name: type:
        { _fieldTag = _fieldMarker; kind = "data"; inherit name level eq type; };
    };
    fieldDAtWithEq = api.leaf {
      description = "fieldDAtWithEq: universe-polymorphic dependent-field with explicit bound-witness — combines fieldDAt with explicit eq.";
      signature = "fieldDAtWithEq : String -> Level -> Hoas -> Hoas -> (Hoas -> Hoas) -> { name; type; level; eq; indexFn; }";
      value = level: eq: name: tyFn:
        { _fieldTag = _fieldMarker; kind = "dataD"; inherit name level eq; typeFn = tyFn; };
    };
    field = api.leaf {
      description = "field: HOAS datatype field declarator — `field name type` declares a non-recursive constructor field; the macro routes through `descArg`.";
      signature = "field : String -> Hoas -> { name; type; }";
      value = name: type: self.fieldAt 0 name type;
    };
    fieldD = api.leaf {
      description = "fieldD: dependent-field declarator — `fieldD name type indexFn` declares a field whose type can depend on prior fields via the index function.";
      signature = "fieldD : String -> Hoas -> (Hoas -> Hoas) -> { name; type; indexFn; }";
      value = name: tyFn: self.fieldDAt 0 name tyFn;
    };
    # Recursive self-reference at a specific index. `idxFn : prev -> Hoas`
    # computes the recursive-call index from markers bound by earlier
    # data/dataD fields. `recField name` is sugar for the recursive field
    # at the ⊤-slice (idxFn = _: ttPrim) — valid only when the enclosing
    # datatype's index type is ⊤, and equivalent to `recFieldAt name
    # (_: ttPrim)`.
    recField = api.leaf {
      description = "recField: recursive-field declarator — `recField name indexFn` declares a recursive position whose target index is computed from prior fields.";
      signature = "recField : String -> (Hoas -> Hoas) -> { name; indexFn; recursive; }";
      doc = ''
        Marks the field as a recursive child via `_recursive = true`,
        routing through `descRec` rather than `descArg` in the
        description-emission step. The `indexFn` extracts the target
        index from prior fields, supporting indexed datatypes whose
        recursive children reference different indices.
      '';
      value = name: { _fieldTag = _fieldMarker; kind = "recAt"; inherit name; idxFn = _: self.ttPrim; };
    };
    recFieldAt = api.leaf {
      description = "recFieldAt: universe-polymorphic recursive-field declarator — `recFieldAt name level indexFn` with explicit level for the recursive position.";
      signature = "recFieldAt : String -> Level -> (Hoas -> Hoas) -> { name; indexFn; recursive; level; }";
      value = name: idxFn: { _fieldTag = _fieldMarker; kind = "recAt"; inherit name idxFn; };
    };
    piFieldAt = api.leaf {
      description = "piFieldAt: universe-polymorphic Π-typed field — `piFieldAt name level sort body` with explicit level.";
      signature = "piFieldAt : String -> Level -> Hoas -> (Hoas -> Hoas) -> { ... }";
      value = level: name: S:
        { _fieldTag = _fieldMarker; kind = "pi"; inherit name level S; };
    };
    piFieldDAt = api.leaf {
      description = "piFieldDAt: universe-polymorphic dependent Π-typed field — combines piFieldAt with piFieldD's dependence on prior fields.";
      signature = "piFieldDAt : String -> Level -> Hoas -> (Hoas -> Hoas -> Hoas) -> { ... }";
      value = level: name: SFn:
        { _fieldTag = _fieldMarker; kind = "piD"; inherit name level; SFn = SFn; };
    };
    piFieldAtWithEq = api.leaf {
      description = "piFieldAtWithEq: piFieldAt with explicit bound-witness — supplies the `eq` proof for level-polymorphic positions.";
      signature = "piFieldAtWithEq : String -> Level -> Hoas -> Hoas -> (Hoas -> Hoas) -> { ... }";
      value = level: eq: name: S:
        { _fieldTag = _fieldMarker; kind = "pi"; inherit name level eq S; };
    };
    piFieldDAtWithEq = api.leaf {
      description = "piFieldDAtWithEq: universe-polymorphic dependent Π-typed field with explicit bound-witness.";
      signature = "piFieldDAtWithEq : String -> Level -> Hoas -> Hoas -> (Hoas -> Hoas -> Hoas) -> { ... }";
      value = level: eq: name: SFn:
        { _fieldTag = _fieldMarker; kind = "piD"; inherit name level eq; SFn = SFn; };
    };
    piFieldAtIndex = api.leaf {
      description = "piFieldAtIndex: piFieldAt variant emitting an explicit-target-index — used when the recursive Π must specify the index of the resulting recursive child.";
      signature = "piFieldAtIndex : String -> Level -> Hoas -> (Hoas -> Hoas) -> (Hoas -> Hoas) -> { ... }";
      value = level: name: S: branchIdxFn:
        { _fieldTag = _fieldMarker; kind = "piAt"; inherit name level S branchIdxFn; };
    };
    piFieldDAtIndex = api.leaf {
      description = "piFieldDAtIndex: piFieldDAt variant emitting an explicit-target-index.";
      signature = "piFieldDAtIndex : String -> Level -> Hoas -> (Hoas -> Hoas -> Hoas) -> (Hoas -> Hoas -> Hoas) -> { ... }";
      value = level: name: SFn: branchIdxFn:
        { _fieldTag = _fieldMarker; kind = "piDAt"; inherit name level SFn branchIdxFn; };
    };
    piFieldAtIndexWithEq = api.leaf {
      description = "piFieldAtIndexWithEq: piFieldAtIndex with explicit bound-witness.";
      signature = "piFieldAtIndexWithEq : String -> Level -> Hoas -> Hoas -> (Hoas -> Hoas) -> (Hoas -> Hoas) -> { ... }";
      value = level: eq: name: S: branchIdxFn:
        { _fieldTag = _fieldMarker; kind = "piAt"; inherit name level eq S branchIdxFn; };
    };
    piFieldDAtIndexWithEq = api.leaf {
      description = "piFieldDAtIndexWithEq: piFieldDAtIndex with explicit bound-witness.";
      signature = "piFieldDAtIndexWithEq : String -> Level -> Hoas -> Hoas -> (Hoas -> Hoas -> Hoas) -> (Hoas -> Hoas -> Hoas) -> { ... }";
      value = level: eq: name: SFn: branchIdxFn:
        { _fieldTag = _fieldMarker; kind = "piDAt"; inherit name level eq SFn branchIdxFn; };
    };
    piField = api.leaf {
      description = "piField: Π-typed field declarator — `piField name sort body` declares a function-typed field where every element of `sort` indexes into the body description.";
      signature = "piField : String -> Hoas -> (Hoas -> Hoas) -> { name; sort; body; pi; }";
      value = name: S: self.piFieldAt 0 name S;
    };
    piFieldD = api.leaf {
      description = "piFieldD: dependent Π-typed field — `piFieldD` extends `piField` with the ability for the body to depend on prior constructor fields.";
      signature = "piFieldD : String -> Hoas -> (Hoas -> Hoas -> Hoas) -> { name; sort; body; pi; indexFn; }";
      value = name: SFn: self.piFieldDAt 0 name SFn;
    };

    # Constructor specification. `con` builds a constructor whose target
    # index is implicitly `ttPrim` (for ⊤-indexed families); `conI`
    # carries an explicit `targetIdx : prev -> Hoas` function computing
    # the target index from bound data/dataD markers.
    con = api.leaf {
      description = "con: HOAS constructor declarator — `con name fields` packages an ordered list of field declarations into a constructor specification consumed by `datatype`.";
      signature = "con : String -> [Field] -> Constructor";
      value = name: fields: { _conTag = _conMarker; inherit name fields; targetIdx = _: self.ttPrim; };
    };
    conI = api.leaf {
      description = "conI: indexed-constructor declarator — `conI name fields targetIndex` declares a constructor whose carrier targets a specific index of the datatype's index family.";
      signature = "conI : String -> [Field] -> (Hoas -> Hoas) -> Constructor";
      value = name: fields: targetIdx: { _conTag = _conMarker; inherit name fields targetIdx; };
    };

    # conDesc I descLevel prev fields targetIdx : Hoas Desc
    # Compile a field list into a description spine over index type `I`.
    # `prev` threads HOAS markers for earlier `field` / `fieldD` bindings
    # (the only field kinds that bind a description-level variable via
    # descArg); `recAt`, `pi`, `piD`, `piAt`, `piDAt` do not extend
    # `prev`. At the ret-leaf the target index is `targetIdx prev`.
    # `pi` / `piD` are the unit-slice constant-index aliases; `piAt` /
    # `piDAt` carry the branch index function used by indexed families.
    conDesc = I: descLevel: prev: fields: targetIdx:
      let
        inherit (self)
          retI recI descArg descArgAt descArgWithEq
          piI piIAt piIWithEq conDesc;
        isUnitI = (I._htag or null) == "unit";
        sameLevel = a: b:
          let r = builtins.tryEval (a == b); in
          r.success && r.value;
        checkedFieldType = f: S:
          self.ann S (self.u f.level);
        descArgFor = f: S: body:
          if f ? eq
          then descArgWithEq I f.level descLevel (checkedFieldType f S) f.eq body
          else if sameLevel f.level descLevel
          then descArg I descLevel (checkedFieldType f S) body
          else descArgAt I f.level descLevel (checkedFieldType f S) body;
        unitBranch = S:
          self.ann
            (self.lam "_" S (_: self.ttPrim))
            (self.forall "_" S (_: self.unitPrim));
        indexedBranch = f: S: prev:
          self.ann
            (self.lam "s" S (s: f.branchIdxFn prev s))
            (self.forall "_" S (_: I));
        branchFor = f: S: prev:
          if f.kind == "pi" || f.kind == "piD" then
            if isUnitI then unitBranch S
            else throw "datatype: piField '${f.name}' not supported at indexed family (I != unit); use piFieldAtIndex"
          else indexedBranch f S prev;
        descPiFor = f: S: prev: body:
          if f ? eq
          then piIWithEq I f.level descLevel (checkedFieldType f S) (branchFor f S prev) f.eq body
          else if sameLevel f.level descLevel
          then piI I descLevel (checkedFieldType f S) (branchFor f S prev) body
          else piIAt I f.level descLevel (checkedFieldType f S) (branchFor f S prev) body;
      in
      if fields == [ ] then retI I descLevel (targetIdx prev)
      else
        let
          f = builtins.head fields;
          rest = builtins.tail fields;
          k = f.kind;
          # Each field's emitted description node carries `f.name` as its
          # per-node presentation label (`_label`). Conv ignores labels so
          # this preserves definitional equality. Orthogonal to the
          # constructor-name slot (`_conLabel`) stamped by `_datatypeImpl`
          # at the spine site below — both can coexist on the same node
          # because they target distinct sidecars.
          labeled = d: self.withDescLabel f.name d;
        in
        if k == "data" then labeled (descArgFor f f.type (v: conDesc I descLevel (prev // { ${f.name} = v; }) rest targetIdx))
        else if k == "dataD" then labeled (descArgFor f (f.typeFn prev) (v: conDesc I descLevel (prev // { ${f.name} = v; }) rest targetIdx))
        else if k == "recAt" then labeled (recI I descLevel (f.idxFn prev) (conDesc I descLevel prev rest targetIdx))
        else if k == "pi" || k == "piAt" then
          labeled (descPiFor f f.S prev (conDesc I descLevel prev rest targetIdx))
        else if k == "piD" || k == "piDAt" then
          labeled (descPiFor f (f.SFn prev) prev (conDesc I descLevel prev rest targetIdx))
        else throw "datatype: unknown field kind '${k}'";

    # spineDesc descs : Hoas Desc
    # Combine per-constructor descriptions into a single description.
    # Uniform recursion: the singleton case IS the leaf (no outer tag);
    # n>=2 produces a right-associated plus-spine `plus D_0 (plus D_1
    # (... D_{n-1}))`. `interp (plus A B) X i` reduces STRUCTURALLY to
    # kernel `Sum (⟦A⟧ X i) (⟦B⟧ X i)` — no bool-tag dispatch, no
    # commuting-conv obligation on `interp ∘ bool-elim`. The generated
    # prelude descriptions expose this plus-spine through their `DT.D`
    # forwarders.
    spineDesc = I: descLevel: descs:
      let
        inherit (self) plusI spineDesc;
        n = builtins.length descs;
      in
      if n == 0 then throw "datatype: n=0 rejected (use H.void)"
      else if n == 1 then builtins.head descs
      else
        let
          D1 = builtins.elemAt descs 0;
          rest = builtins.tail descs;
        in
        plusI I descLevel D1 (spineDesc I descLevel rest);

    fieldLiftType = f: descLevel: S:
      if f ? eq
      then self.LiftAtWithEq f.level descLevel f.eq S
      else self.LiftAt f.level descLevel S;

    liftFieldValue = f: descLevel: S: v:
      if f ? eq
      then self.liftAtWithEq f.level descLevel f.eq S v
      else self.liftAt f.level descLevel S v;

    lowerFieldValue = f: descLevel: S: v:
      if f ? eq
      then self.lowerAtWithEq f.level descLevel f.eq S v
      else self.lowerAt f.level descLevel S v;

    isPiField = f:
      f.kind == "pi" || f.kind == "piD"
      || f.kind == "piAt" || f.kind == "piDAt";

    piDomain = f: prev:
      if f.kind == "pi" || f.kind == "piAt" then f.S
      else if f.kind == "piD" || f.kind == "piDAt" then f.SFn prev
      else null;

    branchIndex = f: prev: s:
      if f.kind == "piAt" || f.kind == "piDAt" then f.branchIdxFn prev s
      else self.ttPrim;

    payloadLeafAt = I: descLevel: targetIdx:
      self.liftAt 0 descLevel (self.bootEq I targetIdx targetIdx) self.bootRefl;

    # Build the payload expected by `interpD descLevel ...`, lifting
    # field values and the ret-leaf equality into `Desc^descLevel`.
    payloadTupleAt = I: descLevel: targetIdx: xs:
      let inherit (self) pair payloadTupleAt; in
      if xs == [ ] then self.payloadLeafAt I descLevel targetIdx
      else pair (builtins.head xs) (payloadTupleAt I descLevel targetIdx (builtins.tail xs));

    payloadTuple = xs: self.payloadTupleAt self.unitPrim 0 self.ttPrim xs;

    fieldPayloadValue = I: D: descLevel: f: prev: v:
      let
        S =
          if f.kind == "data" then f.type
          else if f.kind == "dataD" then f.typeFn prev
          else if self.isPiField f then self.piDomain f prev
          else null;
      in
      if f.kind == "data" || f.kind == "dataD" then
        self.liftFieldValue f descLevel S v
      else if self.isPiField f then
        self.lam "x" (self.fieldLiftType f descLevel S)
          (x:
            self.app
              (self.ann v (self.forall "_" S (s: self.muI I D (self.branchIndex f prev s))))
              (self.lowerFieldValue f descLevel S x))
      else v;

    fieldUserValue = descLevel: f: prev: v:
      let
        S =
          if f.kind == "data" then f.type
          else if f.kind == "dataD" then f.typeFn prev
          else if self.isPiField f then self.piDomain f prev
          else null;
      in
      if f.kind == "data" || f.kind == "dataD" then
        self.lowerFieldValue f descLevel S v
      else if self.isPiField f then
        self.lam "s" S
          (s:
            self.app v (self.liftFieldValue f descLevel S s))
      else v;

    ihUserValue = descLevel: f: prev: ih:
      let
        S = if self.isPiField f then self.piDomain f prev else null;
      in
      if self.isPiField f then
        self.lam "s" S
          (s:
            self.app ih (self.liftFieldValue f descLevel S s))
      else ih;

    # encodeTagAt k I dOuter descsHoas targetIdxVal t payload : Hoas
    # Wrap `payload` with the (n-1)-deep plus-coproduct prefix committing
    # at position t (0-based) out of n total. Mirrors spineDesc
    # structurally: at every layer the L/R type arguments are the interps
    # of the current summand and the plus-tree of the remaining summands
    # respectively, under the muFam `λi:I. μI I dOuter i`, evaluated at
    # the constructor's `targetIdxVal`. `bootInl L R` at position t=0;
    # otherwise `bootInr L R (encodeTagAt ... (t-1) (rest) payload)`.
    # n=1 has no prefix. `descsHoas` must have length >= 1; the
    # singleton case returns `payload` directly.
    #
    # `descsHoas` are encoded HOAS descs. The spine plus-folds through
    # `plusI I k`; the per-layer L/R interp emits kernel-primitive
    # `interp-d` Tms whose `vInterpDF` dispatch handles encoded VDescCon
    # shapes uniformly via the canonical-form path (CDMM §4.2.3).
    # `_datatypeImpl` uses the level-zero wrapper `encodeTag`; descDesc's
    # encoders use `encodeTagAt` at the lifted description level.
    encodeTagAt = level: I: dOuter: descsHoas: targetIdxVal: t: payload:
      let
        inherit (self) plusI bootInl bootInr interpD
          muI lam encodeTagAt;
        n = builtins.length descsHoas;
        muFam = lam "_i" I (iArg: muI I dOuter iArg);
        spineAfter = k:
          let remaining = n - k; in
          if remaining == 1 then builtins.elemAt descsHoas k
          else plusI I level (builtins.elemAt descsHoas k) (spineAfter (k + 1));
        interpAt = dH: interpD level I dH muFam targetIdxVal;
      in
      if n == 1 then payload
      else
        let
          lTy = interpAt (builtins.elemAt descsHoas 0);
          rTy = interpAt (spineAfter 1);
          rest = builtins.tail descsHoas;
        in
        if t == 0 then bootInl lTy rTy payload
        else
          bootInr lTy rTy
            (encodeTagAt level I dOuter rest targetIdxVal (t - 1) payload);

    encodeTag = I: dOuter: descsHoas: targetIdxVal: t: payload:
      self.encodeTagAt 0 I dOuter descsHoas targetIdxVal t payload;

    # Internal: build a DataSpec at index type `I`. When `indexed =
    # false`, exposes `T` as the bare kernel-level type `muI I D ttPrim`
    # (I must be ⊤) and builds a 1-ary eliminator `P : T → U`. When
    # `indexed = true`, exposes `T` as the ann-wrapped family-as-function
    # `λi:I. muI I D i` and builds a 2-ary eliminator `P : (i:I) → muI
    # I D i → U` with an explicit scrutinee-index binder. Description
    # spine, constructor terms, and dispatchStep / jTransportLeaf are
    # shared across both modes, parameterised on the per-constructor
    # `targetIdx` spec field.
    _datatypeImpl = { I, indexed, name, consList, params ? [ ], descLevel ? 0 }:
      let
        inherit (self)
          u forall lam let_ app ann annTrusted
          fst_ snd_ pair
          ttPrim unitPrim
          plusI bootSum bootInl bootInr bootSumElim
          bootEq bootRefl bootJ
          LiftAt liftAt lowerAt
          levelMax natToLevel
          muI descIAt descCon descInd interpD allD
          conDesc spineDesc payloadTupleAt fieldPayloadValue
          fieldUserValue ihUserValue encodeTagAt
          isPiField piDomain branchIndex;

        n = builtins.length consList;
        conNames = map (c: c.name) consList;

        # First duplicate constructor name (null if none).
        dupConName =
          let
            idxs = builtins.genList (x: x) n;
            step = acc: i:
              if acc != null then acc
              else
                let
                  nm = builtins.elemAt conNames i;
                  seen = builtins.genList (j: builtins.elemAt conNames j) i;
                in
                if builtins.elem nm seen then nm else null;
          in
          builtins.foldl' step null idxs;

        # Each constructor's full description carries `c.name` in the
        # `_conLabel` slot (distinct from the per-field `_label` slot
        # populated inside conDesc). Labeling per-summand rather than
        # tagging plus nodes avoids the rightmost-summand asymmetry of
        # the plan's `plus : (tag : Maybe String) → Desc → Desc → Desc`
        # signature: in `plus c0 (plus c1 c2)`, c2 has no plus above it.
        # `spineDesc` then plus-folds already-labeled descriptions and
        # needs no change.
        conDescs = map (c: self.withConLabel c.name (conDesc I descLevel { } c.fields c.targetIdx)) consList;
        sameHoas = a: b:
          let r = builtins.tryEval (a == b); in
          r.success && r.value;
        paramIndex = h:
          let
            idxs = builtins.genList (x: x) (builtins.length params);
            step = acc: i:
              if acc != null then acc
              else if sameHoas h (builtins.elemAt params i) then i
              else null;
          in
          builtins.foldl' step null idxs;
        typeKey = h:
          let
            pIdx = paramIndex h;
            tag = h._htag or null;
          in
          if pIdx != null then { tag = "param"; index = pIdx; }
          else if builtins.isAttrs h && h ? _dtypeMeta then {
            tag = "datatype";
            inherit (h._dtypeMeta) name indexed;
            params = map typeKey (h._dtypeMeta.paramArgs or [ ]);
          }
          else if tag == "unit" || tag == "string" || tag == "int"
            || tag == "float" || tag == "attrs" || tag == "path"
            || tag == "function" || tag == "any" || tag == "level"
          then { inherit tag; }
          else if tag == "U" && builtins.isInt h.level
          then { tag = "U"; inherit (h) level; }
          else { tag = "opaque"; };
        completeTypeKey = key:
          key.tag != "opaque"
          && (!(key ? params) || builtins.all completeTypeKey key.params);
        fieldMarker = f: i: { _signatureField = true; inherit (f) name; index = i; };
        fieldIndex = markers: h:
          let
            idxs = builtins.genList (x: x) (builtins.length markers);
            step = acc: i:
              if acc != null then acc
              else if sameHoas h (builtins.elemAt markers i) then i
              else null;
          in
          builtins.foldl' step null idxs;
        completeTermKey = key:
          key.tag != "opaque"
          && (!(key ? arg) || completeTermKey key.arg);
        termKey = markers: h:
          let
            pIdx = paramIndex h;
            fIdx = fieldIndex markers h;
            tag = h._htag or null;
          in
          if pIdx != null then { tag = "param"; index = pIdx; }
          else if fIdx != null then {
            tag = "field";
            index = fIdx;
            name = (builtins.elemAt markers fIdx).name;
          }
          else if tag == "tt" then { tag = "tt"; }
          else if sameHoas h self.zero then { tag = "zero"; }
          else if tag == "app"
            && builtins.isAttrs h.fn
            && sameHoas h.fn self.NatDT.succ
          then {
            tag = "succ";
            arg = termKey markers h.arg;
          }
          else { tag = "opaque"; };
        fieldSig = f:
          if f.kind == "data" then
            let key = typeKey f.type; in {
              inherit (f) kind level;
              type = key;
              complete = completeTypeKey key;
            }
          else if f.kind == "pi" || f.kind == "piAt" then
            let key = typeKey f.S; in {
              inherit (f) kind level;
              type = key;
              complete = completeTypeKey key;
            }
          else if f.kind == "recAt" then {
            inherit (f) kind;
            complete = false;
          }
          else {
            inherit (f) kind;
            complete = false;
          };
        constructorSig = c:
          let
            markers = builtins.genList
              (i: fieldMarker (builtins.elemAt c.fields i) i)
              (builtins.length c.fields);
            prev = builtins.foldl'
              (acc: i:
                let f = builtins.elemAt c.fields i; in
                if f.kind == "data" || f.kind == "dataD"
                then acc // { ${f.name} = builtins.elemAt markers i; }
                else acc)
              { }
              (builtins.genList (x: x) (builtins.length c.fields));
            fieldSigAt = i:
              let
                f = builtins.elemAt c.fields i;
                base = fieldSig f;
              in
              if f.kind == "recAt" then
                let idx = termKey markers (f.idxFn prev); in
                base // { inherit idx; complete = completeTermKey idx; }
              else base;
            fields = builtins.genList fieldSigAt (builtins.length c.fields);
            target = termKey markers (c.targetIdx prev);
          in
          {
            inherit fields;
            inherit target;
            complete = completeTermKey target && builtins.all (f: f.complete) fields;
          };
        signatureConstructors = map constructorSig consList;
        linearChainCandidates =
          let
            isDataLike = f: f.kind == "data" || f.kind == "dataD";
            linearCtor = i: c:
              let
                fieldCount = builtins.length c.fields;
                dataFieldCount = fieldCount - 1;
                dataFields = builtins.genList (j: builtins.elemAt c.fields j) dataFieldCount;
                recField = if fieldCount == 0 then null else builtins.elemAt c.fields dataFieldCount;
              in
              if n == 2
                && fieldCount > 0
                && recField.kind == "recAt"
                && builtins.all isDataLike dataFields
              then {
                ctor = i;
                side = if i == 0 then "inl" else "inr";
                inherit fieldCount dataFieldCount;
              }
              else null;
          in
          builtins.filter (x: x != null)
            (builtins.genList (i: linearCtor i (builtins.elemAt consList i)) n);
        linearChain =
          if builtins.length linearChainCandidates == 1
          then builtins.head linearChainCandidates
          else null;
        descRef = {
          kind = "datatype-desc";
          inherit name;
          level = descLevel;
          inherit I indexed params;
          arity = n;
          signature = {
            constructors = signatureConstructors;
            complete = builtins.all (c: c.complete) signatureConstructors;
          };
          constructors = map
            (c: {
              fieldKinds = map (f: f.kind) c.fields;
            })
            consList;
        } // (if linearChain == null then { } else { inherit linearChain; });
        # `spineDesc` plus-folds `conDescs` via `plusI I 0` — every
        # combinator under it (`retI`, `descArg`, `descRec`, `descPi`,
        # `plusI`) emits encoded HOAS, so the spine elaborates to a
        # `mkApp` chain over `encodeDescPlus_Tm`/etc. and evaluates to
        # `VDescCon`. `annTrusted` wraps the closed encoded body with
        # the kernel `Desc` ascription without re-checking — the body
        # is well-typed by construction (the encoder lambdas have
        # known polymorphic types).
        D = (annTrusted (spineDesc I descLevel conDescs) (descIAt descLevel I)) // {
          _descRef = descRef;
        };
        # `_descConCert` may carry an optional `validatedFields = { validated
        # : Bool; }`. When `validated`, the carrying layer's non-recursive
        # field positions have been pre-checked by the elaborator against
        # `classify.profile[j].S` under the same outer `ctx` the kernel
        # trampoline uses; sound by referential transparency.
        descConCertified = ctorIndex: fieldCount: targetIdx: payload:
          (descCon D targetIdx payload) // {
            _descConCert = {
              kind = "datatype-con-payload";
              ref = descRef;
              target = targetIdx;
              ctor = ctorIndex;
              inherit fieldCount;
            };
          };
        # Bare μ at the constant ⊤ index. The exposed `T` at
        # indexed=false, and the field type of `pi` / `piD` binders
        # (which are only valid at I=⊤ — see conDesc).
        TAtTt = muI I D ttPrim;
        # Family-as-function: `λi:I. muI I D i`. The exposed `T` at
        # indexed=true.
        TFam = ann (lam "i" I (iArg: muI I D iArg))
          (forall "_" I (_: u descLevel));
        T = if indexed then TFam else TAtTt;

        muFam = lam "_i" I (iArg: muI I D iArg);
        ppTy = K: forall "i" I (iArg: forall "_" (muI I D iArg) (_: u K));
        allLevel = K:
          if builtins.isInt descLevel && descLevel == 0 then K
          else if builtins.isInt K && K == 0 then descLevel
          else if builtins.isInt descLevel && builtins.isInt K then
            if descLevel < K then K else descLevel
          else
            let
              descLevelTm = if builtins.isInt descLevel then natToLevel descLevel else descLevel;
              kTm = if builtins.isInt K then natToLevel K else K;
            in
            levelMax descLevelTm kTm;

        # Apply the user motive `P` to a scrutinee `x` at its index
        # `idx`. At indexed=false the user motive is 1-ary and `idx` is
        # ignored; at indexed=true the motive is 2-ary.
        applyMotive = P: idx: x:
          if indexed then app (app P idx) x
          else app P x;

        # HOAS type of field `f` given `prev` markers for earlier
        # data/dataD fields. data/dataD bind a description-level
        # variable visible to later dependent forms; recAt / pi fields
        # compile to recI / descPi and do not extend `prev`.
        fieldTyOf = f: prev:
          if f.kind == "data" then f.type
          else if f.kind == "dataD" then f.typeFn prev
          else if f.kind == "recAt" then muI I D (f.idxFn prev)
          else if isPiField f then
            forall "_" (piDomain f prev) (s: muI I D (branchIndex f prev s))
          else throw "datatype '${name}': unknown field kind '${f.kind}'";

        extendsPrev = f: f.kind == "data" || f.kind == "dataD";
        isIHField = f: f.kind == "recAt" || isPiField f;

        fieldMeta = f: i: {
          inherit (f) name kind;
          index = i;
          level = f.level or null;
          eq = f.eq or null;
          proof = f.proof or ((f.eq or null) != null);
          type = f.type or null;
          typeFn =
            if f.kind == "data" then (_: f.type)
            else if f.kind == "dataD" then f.typeFn
            else if f.kind == "recAt" then (prev: muI I D (f.idxFn prev))
            else if isPiField f then
              (prev: forall "_" (piDomain f prev) (s: muI I D (branchIndex f prev s)))
            else (_: throw "datatype '${name}': unknown field kind '${f.kind}'");
          idxFn = f.idxFn or null;
          branchIdxFn = f.branchIdxFn or null;
          role = f.role or null;
          source = f.source or null;
        };

        # McBride forced-field set: occurs in `targetIdx` or in a later
        # field's type. See `forced.nix`.
	        forcedSetOf = c:
	          self.forcedFieldSet {
	            fields = c.fields;
	            targetIdx = c.targetIdx;
	            inherit fieldTyOf;
	          };
	        forcedSets = builtins.genList
	          (i: forcedSetOf (builtins.elemAt consList i))
	          n;
	        forcedSetAt = i: builtins.elemAt forcedSets i;

        # Π type of constructor `c`. Terminates in `muI I D (c.targetIdx
        # prev)` — the per-constructor μ-slice at its declared target
        # index. At I=⊤ with the default targetIdx this is `muI ⊤ D
        # ttPrim` = TAtTt.
	        ctorTyOf = i: c:
	          let
	            forced = forcedSetAt i;
	            forallFor = f:
	              if forced.${f.name} or false then self.implicitForall else forall;
            tyGo = remaining: prev:
              if remaining == [ ] then muI I D (c.targetIdx prev)
              else
                let
                  f = builtins.head remaining;
                  rest = builtins.tail remaining;
                in
                (forallFor f) f.name (fieldTyOf f prev) (v:
                  tyGo rest
                    (if extendsPrev f then prev // { ${f.name} = v; } else prev));
          in
          tyGo c.fields { };

        # Build constructor term for the i-th constructor. Zero-field cons
        # become `descCon D <tag-encoded tt>` directly; fielded cons build
        # a curried lam cascade emitting descCon over the payloadTuple of
        # the args, wrapped in `ann` against the full Π type so the ctor
        # stays inferable when applied.
        #
        # Fielded cons are tagged `dt-ctor-mono` so `elaborate` can
        # recognise saturated applications in the `app` branch and emit a
        # flat `desc-con` Tm. Unsaturated or non-chain uses route through
        # `fallback` = `ann bareCtor ctorTyOf`, preserving the inferable
        # surface.
	        mkCtor = i: c:
	          if c.fields == [ ]
          then
            let tIdx = c.targetIdx { }; in
            descConCertified i 0 tIdx
              (encodeTagAt descLevel I D conDescs tIdx i
                (payloadTupleAt I descLevel tIdx [ ]))
	          else
	            let
	              forced = forcedSetAt i;
	              lamFor = f:
	                if forced.${f.name} or false then self.implicitLam else lam;
              bareGo = remaining: prev: collected:
                if remaining == [ ] then
                  let tIdx = c.targetIdx prev; in
                  descConCertified i (builtins.length collected) tIdx
                    (encodeTagAt descLevel I D conDescs tIdx i
                      (payloadTupleAt I descLevel tIdx collected))
                else
                  let
                    f = builtins.head remaining;
                    rest = builtins.tail remaining;
                    fieldPrev = prev;
                  in
                  (lamFor f) f.name (fieldTyOf f prev) (v:
                    bareGo rest
                      (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                      (collected ++ [ (fieldPayloadValue I D descLevel f fieldPrev v) ]));
              bareCtor = bareGo c.fields { } [ ];
	              fallback = ann bareCtor (ctorTyOf i c);
            in
            {
              _htag = "dt-ctor-mono";
              ctorIndex = i;
              nCtors = n;
              dHoas = D;
              # Index type of the enclosing datatype and the
              # constructor's target-index function. `elaborate`'s
              # chain-flatten path uses these to emit the correct
              # `descCon` i-slot and per-summand `interp` types at
              # I ≠ ⊤. `targetIdx : prev → Hoas I` — `prev` is an
              # attrset keyed by data/dataD field names (declaration
              # order), values are HOAS arguments collected from the
              # app spine.
              inherit I;
              targetIdx = c.targetIdx;
              # Per-constructor HOAS descriptions — consumed by
              # `elaborate`'s flatten path to precompute the per-layer
              # L/R interp Tms of the `bootInl` / `bootInr` wrapping.
              inherit conDescs;
              descRef = descRef;
              inherit descLevel;
              nFields = builtins.length c.fields;
              fields = c.fields;
              inherit fallback;
            };

        ctorRecord = builtins.listToAttrs (builtins.genList
          (i:
            let c = builtins.elemAt consList i;
            in { name = c.name; value = mkCtor i c; }
          )
          n);

        # Type of step_i. Zero-field constructors reduce to `applyMotive
        # P (c.targetIdx {}) C_i`. Fielded constructors produce a Π over
        # fields (in declaration order), then a Π over IH binders (one
        # per recAt/pi/piD field in declaration order), terminating in
        # `applyMotive P (c.targetIdx prev) (C_i applied-to-fields)`.
        #
        # The terminal application chain requires C_i to be inferable,
        # hence mkCtor's ann-wrapping for fielded cons.
        stepTyOf = P: i: c:
          if c.fields == [ ] then
            applyMotive P (c.targetIdx { }) (mkCtor i c)
          else
            let
              ctor = mkCtor i c;

              # Reconstruct `prev` markers (data/dataD fields only) from
              # the ordered marker list, used to evaluate `c.targetIdx
              # prev` at the terminal position.
              prevOfMarkers = ms:
                builtins.foldl'
                  (acc: m:
                    if m.kind == "data" || m.kind == "dataD"
                    then acc // { ${m.name} = m.marker; }
                    else acc)
                  { }
                  ms;

              ihGo = ihRemaining: markers:
                let
                  applied = builtins.foldl' (acc: m: app acc m.marker)
                    ctor
                    markers;
                in
                if ihRemaining == [ ] then
                  applyMotive P (c.targetIdx (prevOfMarkers markers)) applied
                else
                  let
                    f = builtins.head ihRemaining;
                    rest = builtins.tail ihRemaining;
                    m = builtins.head (builtins.filter
                      (x: x.name == f.name)
                      markers);
                    ihTy =
                      if f.kind == "recAt" then
                        applyMotive P (f.idxFn m.prev) m.marker
                      else if isPiField f then
                        forall "s" (piDomain f m.prev)
                          (s:
                            applyMotive P (branchIndex f m.prev s) (app m.marker s))
                      else
                        throw "datatype '${name}': unexpected IH field kind '${f.kind}'";
                  in
                  forall ("ih_" + f.name) ihTy (_: ihGo rest markers);

              # Field binders follow the constructor's forced-set; IH
              # binders stay explicit (case content, not index witness).
	              forced = forcedSetAt i;
	              forallFor = f:
	                if forced.${f.name} or false then self.implicitForall else forall;
              fieldGo = remaining: prev: collected:
                if remaining == [ ] then
                  ihGo (builtins.filter isIHField c.fields) collected
                else
                  let
                    f = builtins.head remaining;
                    rest = builtins.tail remaining;
                  in
                  (forallFor f) f.name (fieldTyOf f prev) (v:
                    fieldGo rest
                      (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                      (collected ++ [{
                        inherit (f) name kind;
                        marker = v;
                        prev = prev;
                      }]));
            in
            fieldGo c.fields { } [ ];

        # Apply user-supplied step `s` to the projections of `payload` and
        # `payloadIH` per `c`'s field list.
        #
        # Field x_j (0-based) lives at fst (snd^j payload), where the
        # payload is a right-nested pair from payloadTuple — so fields in
        # declaration order line up with snd-descents.
        #
        # For payloadIH, only rec/pi/piD fields contribute a Σ component.
        # The
        # i-th rec/pi IH (0-based among rec/pi-only fields, in declaration
        # order) lives at fst (snd^i payloadIH).
        buildStepApply = K: P: s: c: payload: payloadIH:
          if c.fields == [ ] then s
          else
            let
              KAll = allLevel K;
              projAt = j: src:
                let
                  go = idx: acc:
                    if idx == 0 then fst_ acc
                    else go (idx - 1) (snd_ acc);
                in
                go j src;
              fieldArgs =
                let
                  go = idx: prev:
                    if idx == builtins.length c.fields then [ ]
                    else
                      let
                        f = builtins.elemAt c.fields idx;
                        raw = projAt idx payload;
                        user = fieldUserValue descLevel f prev raw;
                        prev' =
                          if extendsPrev f then prev // { ${f.name} = user; } else prev;
                      in
                      [ user ] ++ go (idx + 1) prev';
                in
                go 0 { };
              ihCount = builtins.length (builtins.filter isIHField c.fields);
              ihFields = builtins.filter isIHField c.fields;
              fieldIndex = field:
                let
                  idxs = builtins.genList (x: x) (builtins.length c.fields);
                in
                builtins.foldl'
                  (acc: idx:
                    if acc != null then acc
                    else if (builtins.elemAt c.fields idx).name == field.name then idx
                    else null)
                  null
                  idxs;
              prevForField = field:
                builtins.foldl'
                  (acc: idx:
                    let f = builtins.elemAt c.fields idx; in
                    if extendsPrev f
                    then acc // { ${f.name} = builtins.elemAt fieldArgs idx; }
                    else acc)
                  { }
                  (builtins.genList (x: x) (fieldIndex field));
              # The IH witnesses come from `everywhereD`, typed at the
              # lifted internal motive `Pp` (codomain `allLevel K`). The
              # user step's IH binders are at the bare motive `P`
              # (codomain `K`). For a direct recursive position the bridge
              # is a `lowerAt K KAll` back onto `applyMotive P idx subterm`;
              # it collapses to the identity whenever `KAll ≡ K` (every
              # monomorphic datatype, where `descLevel = 0`), and does the
              # real work only when the carrier carries a level parameter.
              ihArgs = builtins.genList
                (i:
                  let
                    f = builtins.elemAt ihFields i;
                    prev = prevForField f;
                    rawIH = projAt i payloadIH;
                  in
                  if f.kind == "recAt"
                  then
                    let subterm = builtins.elemAt fieldArgs (fieldIndex f); in
                    lowerAt K KAll (applyMotive P (f.idxFn prev) subterm) rawIH
                  else ihUserValue descLevel f prev rawIH)
                ihCount;
              withFields = builtins.foldl' (acc: a: app acc a) s fieldArgs;
              withIHs = builtins.foldl' (acc: a: app acc a) withFields ihArgs;
            in
            withIHs;

        # Reconstruct `prev` markers (for data/dataD fields only) from
        # a runtime payload value. Used by dispatchStep to evaluate a
        # constructor's `targetIdx` at dispatch time so the J-motive can
        # carry the correct `(I, targetIdx_c)` witness pair.
        prevOfPayload = c: payload:
          let
            projAt = j: src:
              let
                go = idx: acc:
                  if idx == 0 then fst_ acc
                  else go (idx - 1) (snd_ acc);
              in
              go j src;
            step = acc: idx:
              let
                f = builtins.elemAt c.fields idx;
                raw = projAt idx payload;
              in
              if f.kind == "data" || f.kind == "dataD"
              then acc // { ${f.name} = fieldUserValue descLevel f acc raw; }
              else acc;
          in
          builtins.foldl' step { } (builtins.genList (x: x) (builtins.length c.fields));

        # dispatchStep Pp iArg ctx descs steps cons payload payloadIH : Hoas
        # Walks the per-constructor descriptions in declaration order,
        # threading an outer-context wrapper `ctx` that reconstitutes the
        # full payload at each level (used in the sumElim motive so conv
        # discharges Pp iArg (descCon D iArg (ctx ...)) ≡ P (C_i ...) via
        # Pp-β + Σ-η + J-transport on the leaf Eq witness). Pp is the
        # indexed motive wrapper `λi:I. λx:muI I D i. P-applied`; at
        # indexed=false it ignores i and applies P 1-ary, at indexed=true
        # it applies P 2-ary (i.e. Pp = P). n=1 (leaf) wraps the user
        # step in J-transport over the leaf Eq witness; n>=2 emits a
        # sumElim that commits to constructor i on `inl` (J-transported)
        # and descends into the rest-spine on `inr`.
        #
        dispatchStep = K: P: Pp: iArg: ctx: descs: steps: cons: payload: payloadIH:
          let
            n' = builtins.length descs;
            KAll = allLevel K;

            jTransportLeaf = targetIdx_c: payloadCtx: c: r: userApplied:
              let
                fieldCount = builtins.length c.fields;
                projAt = i: src:
                  let
                    go = idx: acc:
                      if idx == 0 then fst_ acc
                      else go (idx - 1) (snd_ acc);
                  in
                  go i src;
                sndN = i: src:
                  let
                    go = idx: acc:
                      if idx == 0 then acc
                      else go (idx - 1) (snd_ acc);
                  in
                  go i src;
                eLeaf = sndN fieldCount r;
                lowerLeaf = y: e:
                  lowerAt 0 descLevel (bootEq I targetIdx_c y) e;
                liftLeaf = y: e:
                  liftAt 0 descLevel (bootEq I targetIdx_c y) e;
                buildPayload = y: e:
                  let
                    go = i:
                      if i == fieldCount then liftLeaf y e
                      else pair (projAt i r) (go (i + 1));
                  in
                  go 0;
                target = y: e: descCon D y (payloadCtx (buildPayload y e));
                targetBase = target targetIdx_c bootRefl;
                liftedApplied =
                  liftAt K KAll (applyMotive P targetIdx_c targetBase) userApplied;
                motive = lam "y" I (y:
                  lam "e" (bootEq I targetIdx_c y) (e:
                    app (app Pp y) (target y e)));
              in
              bootJ I targetIdx_c motive liftedApplied iArg (lowerLeaf iArg eLeaf);
          in
          if n' == 1 then
            let
              c = builtins.head cons;
              s = builtins.head steps;
              applied = buildStepApply K P s c payload payloadIH;
              targetIdx_c = c.targetIdx (prevOfPayload c payload);
            in
            jTransportLeaf targetIdx_c ctx c payload applied
          else
            let
              D1 = builtins.elemAt descs 0;
              s1 = builtins.head steps;
              c1 = builtins.head cons;
              restD = builtins.tail descs;
              restS = builtins.tail steps;
              restC = builtins.tail cons;
              restSpine = spineDesc I descLevel restD;
              # Interp types of the two summands at the current iArg:
              # the outer plus's interp reduces to `Sum lInterp rInterp`
              # (kernel Sum), and `payload : Sum lInterp rInterp` is
              # dispatched via `bootSumElim`.
              lInterp = interpD descLevel I D1 muFam iArg;
              rInterp = interpD descLevel I restSpine muFam iArg;
              # Sum-elim motive: each summand inhabits this Pp-target
              # rebuilt through `ctx (bootInl/bootInr …)`.
              sumMot = lam "s" (bootSum lInterp rInterp) (s:
                forall "rih" (allD descLevel I (plusI I descLevel D1 restSpine) KAll muFam Pp iArg s) (_:
                  app (app Pp iArg) (descCon D iArg (ctx s))));
              onInl = lam "r" lInterp (r:
                lam "rih" (allD descLevel I D1 KAll muFam Pp iArg r) (rih:
                  let targetIdx_c1 = c1.targetIdx (prevOfPayload c1 r); in
                  jTransportLeaf targetIdx_c1
                    (local: ctx (bootInl lInterp rInterp local))
                    c1
                    r
                    (buildStepApply K P s1 c1 r rih)));
              ctx' = local: ctx (bootInr lInterp rInterp local);
              onInr = lam "r" rInterp (r:
                lam "rih" (allD descLevel I restSpine KAll muFam Pp iArg r) (rih:
                  dispatchStep K P Pp iArg ctx' restD restS restC r rih));
            in
            app (bootSumElim lInterp rInterp sumMot onInl onInr payload)
              payloadIH;

        # Generic eliminator. The closed term is wrapped in `ann` against
        # its full Π type so it stays inferable when applied via `app` in
        # checked positions — the bidirectional kernel has no infer rule
        # for bare `lam`. `ann` is eval-transparent, so nf-equivalence
        # against the inline-adapter spelling is preserved.
        motiveTy = K:
          if indexed
          then forall "i" I (iArg: forall "_" (muI I D iArg) (_: u K))
          else forall "_" TAtTt (_: u K);
        stepNames = builtins.genList (i: "step_${toString i}") n;

        # Wrap a body with `lam step_i (stepTyOf P i c)` for each
        # constructor in declaration order, then call `mkBody` with the
        # collected step markers.
        buildLamCascade = mkBody: P:
          let
            go = i: stepsAcc:
              if i == n then mkBody stepsAcc
              else
                let c = builtins.elemAt consList i; in
                lam (builtins.elemAt stepNames i) (stepTyOf P i c) (s:
                  go (i + 1) (stepsAcc ++ [ s ]));
          in
          go 0 [ ];

        buildPiCascade = mkBody: P:
          let
            go = i:
              if i == n then mkBody
              else
                let c = builtins.elemAt consList i; in
                forall (builtins.elemAt stepNames i) (stepTyOf P i c) (_:
                  go (i + 1));
          in
          go 0;

        # Step body for `descInd`. Same shape at indexed=false and
        # indexed=true — the step function is always `λi:I. λd:⟦D⟧ muFam
        # i. λih:All D D Pp i d. dispatchStep Pp i id conDescs steps cons
        # d ih`. `K` is the motive's codomain universe and flows into
        # `allD` so the internal pTy binder accepts a `Pp` whose
        # codomain lives at U(K). The scrutinee description level `L = 0`
        # — `datatype` constructors all bind their sorts at `U(0)`.
        indStep = K: P: Pp: steps:
          let KAll = allLevel K; in
          lam "i" I (iArg:
            lam "d" (interpD descLevel I D muFam iArg) (d:
              lam "ih" (allD descLevel I D KAll muFam Pp iArg d) (ih:
                dispatchStep K P Pp iArg (x: x) conDescs steps consList d ih)));

        elimTy = K:
          if indexed then
            forall "P" (motiveTy K)
              (P:
                buildPiCascade
                  (forall "i" I (iArg:
                    forall "scrut" (muI I D iArg) (scrut: app (app P iArg) scrut)))
                  P)
          else
            forall "P" (motiveTy K) (P:
              buildPiCascade
                (forall "scrut" TAtTt (scrut: app P scrut))
                P);

        elimBody = K:
          if indexed then
            lam "P" (motiveTy K)
              (P:
                buildLamCascade
                  (steps:
                    lam "i" I (iArg:
                      lam "scrut" (muI I D iArg) (scrut:
                        let_ "Pp" (ppTy (allLevel K))
                          (lam "i" I (pIdx:
                            lam "x" (muI I D pIdx) (x:
                              LiftAt K (allLevel K) (app (app P pIdx) x))))
                          (Pp:
                            lowerAt K (allLevel K) (app (app P iArg) scrut)
                              (descInd D Pp (indStep K P Pp steps) iArg scrut)))))
                  P)
          else
            lam "P" (motiveTy K) (P:
              buildLamCascade
                (steps:
                  lam "scrut" TAtTt (scrut:
                    let_ "Pp" (ppTy (allLevel K))
                      (lam "i" I (_: lam "x" (muI I D ttPrim) (x:
                        LiftAt K (allLevel K) (app P x))))
                      (Pp:
                        lowerAt K (allLevel K) (app P scrut)
                          (descInd D Pp (indStep K P Pp steps) ttPrim scrut))))
                P);

        elim = K: ann (elimBody K) (elimTy K);

        constructorMeta = i: c: {
          inherit (c) name;
          index = i;
          targetIdx = c.targetIdx;
          ctor = mkCtor i c;
          fields = builtins.genList
            (j: fieldMeta (builtins.elemAt c.fields j) j)
            (builtins.length c.fields);
        };

        constructors = builtins.genList
          (i: constructorMeta i (builtins.elemAt consList i))
          n;

        # Uniform metadata exposed alongside the DataSpec. `indexTy`
        # describes the index type of the family; at `indexed=false` it
        # is the unit type, at `indexed=true` it is the user-supplied
        # `I`. `constructors` is the normalized generic-programming
        # surface consumed by walkers and record helpers.
        _dtypeMeta = {
          inherit name indexed constructors;
          params = params;
          paramArgs = [ ];
          indexTy = I;
          inherit D T elim;
        };

        # Per-field polymorphic types, consumed by datatypeP / datatypePI
        # to build the outer `ann (λparams. monoField) (Π(params).
        # monoFieldTy)` wrapping. At indexed=false `T`'s type is `U`; at
        # indexed=true `T` is a function from I to U and its type is
        # `Π(i:I). U`.
        _tys = {
          D = descIAt descLevel I;
          T = if indexed then forall "_" I (_: u descLevel) else u descLevel;
          elim = elimTy;
        } // (builtins.listToAttrs (builtins.genList
          (i:
            let c = builtins.elemAt consList i; in
	            { name = c.name; value = ctorTyOf i c; }
          )
          n));
      in
      if n == 0 then throw "datatype '${name}': n=0 rejected (use H.void)"
      else if dupConName != null then
        throw "datatype '${name}': duplicate constructor name '${dupConName}'"
      else
        (ctorRecord // {
          inherit name D elim _dtypeMeta _tys;
          # Attach `_dtypeMeta` to the exported `T` so the elaborate-layer
          # extract path can recover constructor + field names when
          # decomposing macro-generated VMu values. Internal uses of `T`
          # within this let-block (fieldTyOf, ctorTyOf, dispatchStep, etc.)
          # are unaffected — the HOAS elaborator only reads `_htag` and `D`
          # from a "mu" form; extra attrs are ignored.
          T = T // { inherit _dtypeMeta; };
          _cons = consList;
        });

    # Monomorphic ⊤-indexed DataSpec. Exposes `T = muI ⊤ D ttPrim` (a
    # bare μ-type) and a 1-ary eliminator `P : T → U`.
    datatypeAt = api.leaf {
      description = "datatypeAt: universe-polymorphic ⊤-slice datatype — `datatypeAt name level [con …]` emits a datatype at sort level `level`.";
      signature = "datatypeAt : String -> Level -> [Constructor] -> DataSpec";
      value = name: descLevel: consList:
        self._datatypeImpl {
          I = self.unitPrim;
          indexed = false;
          inherit name descLevel consList;
        };
    };

    datatype = api.leaf {
      description = "datatype: HOAS datatype macro — `datatype name [con …]` declares a named ⊤-slice datatype, emitting `{ D, T, elim, <constructors> }` with `_dtypeMeta` for walker dispatch.";
      signature = "datatype : String -> [Constructor] -> DataSpec";
      doc = ''
        The macro builds the description from constructor field lists,
        synthesises the type former (`T = mu D tt`), generated
        constructors that introduce values, and an eliminator
        specialised for the description. The result attrset's
        `_dtypeMeta` field carries the constructor list for walker
        dispatch (used by `recoverConstructor` / `walkAttrsetDatatype`).
        Surface entry point for declaring new datatypes — prefer over
        manual `mu` + `descCon` construction.
      '';
      value = name: consList: self.datatypeAt name 0 consList;
    };

    # Monomorphic indexed DataSpec over index type `I`. Exposes `T = ann
    # (λi:I. muI I D i) (Π(_:I). U)` — a family-as-function — and a
    # 2-ary eliminator `P : (i:I) → muI I D i → U` with an explicit
    # scrutinee-index binder. Each constructor is a `conI name fields
    # targetIdx` where `targetIdx : prev → Hoas` computes the
    # constructor's target index from bound data/dataD markers;
    # recursive fields at non-default indices use `recFieldAt name
    # idxFn`.
    datatypeI = api.leaf {
      description = "datatypeI: indexed-datatype macro — `datatypeI name indexSort [conI …]` declares a datatype indexed by `indexSort`; each constructor must declare its target index.";
      signature = "datatypeI : String -> Hoas -> [ConI] -> DataSpec";
      doc = ''
        Indexed counterpart to `datatype`. The index sort `I` parametrises
        the carrier family, and each constructor's `conI` declares the
        index it produces. The resulting `T : I -> U` is the family
        type former; `app T idx` is the carrier at a specific index.
        Prelude `fin`, `vec` use this form.
      '';
      value = name: I: consList:
        self._datatypeImpl {
          inherit I;
          indexed = true;
          inherit name consList;
        };
    };

    # Internal: polymorphic datatype builder. Each output field f is the
    # mono field λ-abstracted over params, wrapped in `ann` against
    # `Π(params). T_f` where `T_f` is pulled from the mono spec's
    # `_tys.<field>`. The outer `ann` is what makes the curried
    # constructor/eliminator inferable in checked positions after the
    # first parameter application; without it `app <polyField> firstArg`
    # would have a bare-λ head and fail synthesis.
    #
    # At `indexed = true`, `indexFn markers : Hoas` computes the index
    # type from parameter markers (the param-dependent analogue of
    # `datatypeI`'s I argument); the spec of each constructor uses
    # `conI name fields targetIdx`.
    #
    # The probe call `mkCtors dummyMarkers` is only used to extract
    # constructor names and metadata (via shallow attrs c.name / f.name /
    # f.kind). Each polymorphic field's closure re-runs `mkCtors` with real
    # HOAS markers at elaborate-time, so field types and constructor
    # bodies are never resolved against the probe's dummy values.
    _datatypePImpl = { indexed, name, params, indexFn, levelFn ? (_: 0), mkCtors }:
      let
        inherit (self) u lam forall ann;

        nParams = builtins.length params;
        monoOf = markers:
          self._datatypeImpl {
            I = if indexed then indexFn markers else self.unitPrim;
            inherit indexed name;
            descLevel = levelFn markers;
            consList = mkCtors markers;
            params = markers;
          };
        # A parameter's `kind` is either a fixed Hoas (the common case,
        # e.g. `kind = u 0`) or a function from the list of bound
        # parameter markers to a Hoas (e.g. for W-type's
        # `P : S → U` where `kind = ms: forall "_" (builtins.elemAt ms 0)
        # (_: u 0)`). This is the parameter-level analogue of `field` vs
        # `fieldD` and `piField` vs `piFieldD`: same "depends on prior
        # bindings" pattern, applied one scope outward.
        resolveKind = p: markers:
          if builtins.isFunction p.kind then p.kind markers else p.kind;
        overParams = mkBody:
          let
            go = i: markers:
              if i == nParams then mkBody markers
              else
                let p = builtins.elemAt params i; in
                lam p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [ m ]));
          in
          go 0 [ ];
        # Params are always forced (appear rigidly in the conclusion).
        implicitOverParams = mkBody:
          let
            go = i: markers:
              if i == nParams then mkBody markers
              else
                let p = builtins.elemAt params i; in
                self.implicitLam p.name (resolveKind p markers)
                  (m: go (i + 1) (markers ++ [ m ]));
          in
          go 0 [ ];
        paramPi = mkBodyTy:
          let
            go = i: markers:
              if i == nParams then mkBodyTy markers
              else
                let p = builtins.elemAt params i; in
                forall p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [ m ]));
          in
          go 0 [ ];
        implicitParamPi = mkBodyTy:
          let
            go = i: markers:
              if i == nParams then mkBodyTy markers
              else
                let p = builtins.elemAt params i; in
                self.implicitForall p.name (resolveKind p markers)
                  (m: go (i + 1) (markers ++ [ m ]));
          in
          go 0 [ ];
        annotateParamArgs = args:
          let
            go = i: prev:
              if i == nParams then [ ]
              else
                let
                  p = builtins.elemAt params i;
                  a = builtins.elemAt args i;
                  K = resolveKind p prev;
                  # A universe level is a sort, not a term: ascribing it
                  # (`ann level level`) is vacuous and makes the level opaque
                  # to `sameLevelSyntax`/`levelAsInt`, spuriously defeating
                  # `LiftAt`/`liftAt` idempotence at equal levels. Keep level
                  # params bare; ascribe only genuine type/term params.
                  aAnn = if (K._htag or null) == "level" then a else ann a K;
                in
                [ aAnn ] ++ go (i + 1) (prev ++ [ aAnn ]);
          in
          go 0 [ ];
        polyField = fieldName:
          ann
            (overParams (markers:
              builtins.getAttr fieldName (monoOf markers)))
            (paramPi (markers:
              builtins.getAttr fieldName (monoOf markers)._tys));
        # `elim` on the monomorphic spec is `K → Tm` (universe-polymorphic
        # in the motive's codomain); the polymorphic wrapper threads `K`
        # outside the parameter cascade so callers write `ListDT.elim K A P
        # N C scrut` with `K` leading the parameter-plus-motive spine.
        polyElim = K:
          ann (implicitOverParams (markers: (monoOf markers).elim K))
            (implicitParamPi (markers: (monoOf markers)._tys.elim K));
        # Poly constructor wrapper: tagged `dt-ctor-poly` HOAS node
        # carrying the nParams/monoAt hook that `elaborate`'s `app` branch
        # uses to recognise saturated chains and flatten them into a flat
        # `desc-con` Tm. Non-saturated/non-chain uses elaborate via
        # `fallback` (the regular ann + overParams wrapping) and behave
        # identically to the pre-flattening code. For zero-field
        # constructors the fallback's inner body is the plain `descCon D
        # payload` HOAS; for fielded constructors it is the dt-ctor-mono
        # node's ann fallback.
        polyCtor = cName:
          ann
            (implicitOverParams (markers:
              let m = builtins.getAttr cName (monoOf markers); in
              if builtins.isAttrs m && m ? _htag && m._htag == "dt-ctor-mono"
              then m.fallback
              else m))
            (implicitParamPi (markers:
              builtins.getAttr cName (monoOf markers)._tys));
        # Shallow probe: only c.name / f.name / f.kind are read. u 0 as a
        # dummy HOAS is structurally valid anywhere a type is expected;
        # field type expressions are never forced during the probe.
        dummyMarkers = map (_: u 0) params;
        probe = mkCtors dummyMarkers;
        conNames = map (c: c.name) probe;
        # Eagerly validate shape (n=0, duplicate con names) at datatypeP time.
        _validate = builtins.seq (monoOf dummyMarkers).name null;
        # For each constructor name, expose a `dt-ctor-poly` tagged node
        # wrapping the polyCtor fallback. Keeps unsaturated uses identical
        # to the prior ann-lam cascade; enables the elaborate app-branch
        # to detect saturated chains and emit flat desc-con Tms for stack
        # safety on deep recursive values (5000+).
        mkPolyCtorNode = cName:
          let
            probeC = builtins.head (builtins.filter (c: c.name == cName) probe);
            nFields = builtins.length probeC.fields;
          in
          {
            _htag = "dt-ctor-poly";
            name = cName;
            # Dtype identity for `elaborateForCheck` to align the term-spine
            # head with the expected type's carrier `T`. `T._dtypeMeta.name`
            # carries the same string at the type side.
            _dtypeName = name;
            inherit nParams;
            inherit nFields;
            fields = probeC.fields;
            # HOAS accessor: given a list of parameter HOAS args, produce
            # the mono constructor HOAS (a `dt-ctor-mono` tagged node for
            # fielded ctors, or a plain `descCon` HOAS for zero-field
            # ctors).
            monoAt = paramArgs: builtins.getAttr cName (monoOf (annotateParamArgs paramArgs));
            # Fallback for non-saturated / non-chain uses.
            fallback = polyCtor cName;
          };
        ctorRecord = builtins.listToAttrs (map
          (cName: {
            name = cName;
            value = mkPolyCtorNode cName;
          })
          conNames);

        probeFieldMeta = f: i: {
          inherit (f) name kind;
          index = i;
          level = f.level or null;
          eq = f.eq or null;
          proof = f.proof or ((f.eq or null) != null);
          type = f.type or null;
          typeFn = f.typeFn or null;
          idxFn = f.idxFn or null;
          branchIdxFn = f.branchIdxFn or null;
          role = f.role or null;
          source = f.source or null;
        };
        probeConstructorMeta = i: c: {
          inherit (c) name;
          index = i;
          targetIdx = c.targetIdx;
          ctor = builtins.getAttr c.name ctorRecord;
          fields = builtins.genList
            (j: probeFieldMeta (builtins.elemAt c.fields j) j)
            (builtins.length c.fields);
        };
        probeConstructors = builtins.genList
          (i: probeConstructorMeta i (builtins.elemAt probe i))
          (builtins.length probe);

        # Polymorphic `_dtypeMeta` is a head witness. Concrete generic
        # consumers should call `instantiate`, which reruns the datatype
        # macro with real parameter arguments and returns resolved metadata.
        _dtypeMeta = {
          inherit name indexed params;
          paramArgs = [ ];
          indexTy = null;
          inherit indexFn levelFn;
          D = polyField "D";
          T = polyField "T";
          elim = polyElim;
          constructors = probeConstructors;
          instantiate = paramArgs:
            let mono = monoOf paramArgs;
            in mono._dtypeMeta // {
              inherit params;
              paramArgs = paramArgs;
            };
        };
      in
      builtins.seq _validate (ctorRecord // {
        inherit name params;
        D = polyField "D";
        # `T` carries `_dtypeMeta` so the elaborate-layer extract path can
        # peel an `app L.T A1 .. An` spine to find the polymorphic head
        # and recover constructor + field names for macro-generated VMu
        # values.
        T = (polyField "T") // { inherit _dtypeMeta; };
        elim = polyElim;
        inherit _dtypeMeta;
        _cons = probe;
      });

    # ⊤-indexed polymorphic DataSpec. Each field of the output is an
    # `ann`-wrapped `λparams. monoField`. Constructors use `con`.
    datatypePAt = api.leaf {
      description = "datatypePAt: universe-polymorphic parametric datatype — `datatypePAt` extends `datatypeP` with explicit sort levels for parameters.";
      signature = "datatypePAt : String -> Level -> [Param] -> (Hoas -> [Constructor]) -> DataSpec";
      value = name: params: levelFn: mkCtors:
        self._datatypePImpl {
          indexed = false;
          indexFn = _: self.unitPrim;
          inherit name params levelFn mkCtors;
        };
    };

    datatypeP = api.leaf {
      description = "datatypeP: parametric-datatype macro — `datatypeP name [param …] [con …]` declares a datatype parametric in zero or more sort parameters.";
      signature = "datatypeP : String -> [Param] -> (Hoas -> [Constructor]) -> DataSpec";
      doc = ''
        Parameters are sorts external to the datatype; the
        constructor list is a function of the parameter binders.
        Resulting `T` takes parameters before producing the carrier
        type. Prelude `listOf`, `sum` would be expressed via this
        macro (in practice they're macro-generated via `ListDT`,
        `SumDT` at fixed parameter shapes).
      '';
      value = name: params: mkCtors:
        self.datatypePAt name params (_: 0) mkCtors;
    };

    # Indexed polymorphic DataSpec. `indexFn : params → Hoas` produces
    # the index type from parameter markers; `mkCtors` produces a list of
    # `conI`-tagged constructor specs.
    datatypePI = api.leaf {
      description = "datatypePI: parametric + indexed datatype — `datatypePI name [param …] indexSortFn [conI …]` combines parameters and indices in one macro.";
      signature = "datatypePI : String -> [Param] -> (Hoas -> Hoas) -> (Hoas -> [ConI]) -> DataSpec";
      doc = ''
        The most general datatype declarator: takes external
        parameters AND an index sort that can depend on those
        parameters, AND constructors whose index decisions depend on
        both. Used by `vec` (parameter A, index n : nat) and similar
        prelude families.
      '';
      value = name: params: indexFn: mkCtors:
        self._datatypePImpl {
          indexed = true;
          inherit name params indexFn mkCtors;
        };
    };

    # Macro-derived prelude datatypes. Surface types and introductions
    # forward to fields of these specs; extract/reifyType detect the
    # μ-shape match and route decoding through the existing prelude
    # branches so reify-shape equivalence is preserved.
    BoolDT =
      let inherit (self) datatype con; in
      datatype "Bool" [
        (con "true" [ ])
        (con "false" [ ])
      ];

    NatDT =
      let inherit (self) datatype con recField; in
      datatype "Nat" [
        (con "zero" [ ])
        (con "succ" [ (recField "pred") ])
      ];

    ListDT =
      let inherit (self) datatypePAt con fieldAt recField level u; in
      datatypePAt "List"
        [{ name = "k"; kind = level; }
          { name = "A"; kind = ps: u (builtins.elemAt ps 0); }]
        (ps: builtins.elemAt ps 0)
        (ps:
          let
            k = builtins.elemAt ps 0;
            A = builtins.elemAt ps 1;
          in
          [
            (con "nil" [ ])
            (con "cons" [ (fieldAt k "head" A) (recField "tail") ])
          ]);

    SumDT =
      let inherit (self) datatypePAt con fieldAt level u; in
      datatypePAt "Sum"
        [{ name = "k"; kind = level; }
          { name = "A"; kind = ps: u (builtins.elemAt ps 0); }
          { name = "B"; kind = ps: u (builtins.elemAt ps 0); }]
        (ps: builtins.elemAt ps 0)
        (ps:
          let
            k = builtins.elemAt ps 0;
            A = builtins.elemAt ps 1;
            B = builtins.elemAt ps 2;
          in
          [
            (con "Left" [ (fieldAt k "value" A) ])
            (con "Right" [ (fieldAt k "value" B) ])
          ]);

    # Fin — monomorphic indexed datatype over Nat. Two constructors,
    # both with target index `succ m` carrying the index equality
    # through the ret-leaf. `Fin 0` is vacuous by construction; the
    # no-confusion discharge lives in `combinators.nix:absurdFin0`.
    FinDT =
      let inherit (self) datatypeI conI field recFieldAt nat succ; in
      datatypeI "Fin" nat [
        (conI "fzero" [ (field "m" nat) ]
          (p: succ p.m))
        (conI "fsuc" [
          (field "m" nat)
          (recFieldAt "k" (p: p.m))
        ]
          (p: succ p.m))
      ];

    # Vec — parametric indexed datatype `Vec A : Nat → U`. `vnil`
    # targets index `zero`; `vcons` targets `succ m` with the tail
    # at index `m`.
    VecDT =
      let inherit (self) datatypePI conI field recFieldAt u nat zero succ; in
      datatypePI "Vec"
        [{ name = "A"; kind = u 0; }]
        (_: nat)
        (ps:
          let A = builtins.elemAt ps 0; in [
            (conI "vnil" [ ] (_: zero))
            (conI "vcons"
              [
                (field "m" nat)
                (field "x" A)
                (recFieldAt "xs" (p: p.m))
              ]
              (p: succ p.m))
          ]);

    # Eq — parametric indexed datatype `Eq A a : A → U` with
    # parameter-dependent index type (`indexFn = ps: ps.A`). Single
    # constructor `refl` targets index `a`.
    EqDT =
      let inherit (self) datatypePI conI u; in
      datatypePI "Eq"
        [{ name = "A"; kind = u 0; }
          { name = "a"; kind = ms: builtins.elemAt ms 0; }]
        (ps: builtins.elemAt ps 0)
        (ps:
          let a = builtins.elemAt ps 1; in [
            (conI "refl" [ ] (_: a))
          ]);

    # Le — monomorphic doubly-indexed inductive predicate
    # `Le : Nat → Nat → U`, the Agda `Data.Nat.Base._≤_` form. Index
    # carrier is `Σ Nat (_: Nat)` so a single `datatypeI` call captures
    # both arguments; the surface forwarder `le m n` (in
    # `combinators.nix`) curries by applying `LeDT.T` to `pair m n`.
    # Two constructors mirror Agda exactly:
    #   leZ  : ∀ n. Le 0 n           (z≤n)
    #   leSS : ∀ m n. Le m n → Le (suc m) (suc n)   (s≤s)
    # Chosen over the existential form `Σ k (m + k ≡ n)` because
    # decidability proofs recurse simultaneously on `m` and `n`,
    # matching the constructor shape. See Agda
    # `Data.Nat.Properties._≤?_` for the textbook recipe.
    LeDT =
      let inherit (self) datatypeI conI field recFieldAt nat zero succ
        sigma pair;
      in
      datatypeI "Le"
        (sigma "_lem" nat (_: nat))
        [
          (conI "leZ" [ (field "n" nat) ]
            (p: pair zero p.n))
          (conI "leSS" [
            (field "m" nat)
            (field "n" nat)
            (recFieldAt "lemn" (p: pair p.m p.n))
          ]
            (p: pair (succ p.m) (succ p.n)))
        ];

    # IntZ — the literature-canonical 2-constructor inductive Int. Agda
    # `Data.Integer.Base`: `data ℤ : Set where +_ : ℕ → ℤ; -[1+_] : ℕ → ℤ`.
    # Lean 4 `Init.Data.Int.Basic`: `inductive Int where | ofNat : Nat → Int
    # | negSucc : Nat → Int`. Exact match.
    #
    # Unique representation — `pos 0` is the only encoding of zero; no
    # two-zeros problem. `negSucc n` encodes `-(n+1)` so the negative
    # range `[-∞, -1]` is covered without ambiguity. Carrier of choice
    # for structurally decidable equality / ordering: case analysis on
    # the sign discriminator reduces every `Eq IntZ` / `Le IntZ` query
    # to a `Nat` sub-query plus a no-confusion lemma at the sign
    # mismatch.
    #
    # Coexists with the primitive `int_` type. Existing refinement
    # predicates over `int_` are unaffected; consumers that want
    # structural induction over integers select `IntZ`.
    IntZDT =
      let inherit (self) datatype con field nat; in
      datatype "IntZ" [
        (con "pos" [ (field "n" nat) ])
        (con "negSucc" [ (field "n" nat) ])
      ];

    WDT = api.leaf {
      description = "WDT: W-type description macro — packages shape sort + position family into a `DataSpec` for arbitrary-branching inductive trees outside the description layer.";
      signature = "WDT : Hoas -> (Hoas -> Hoas) -> DataSpec";
      value =
        let inherit (self) datatypePAt con fieldAt piFieldDAt level u forall app; in
        datatypePAt "W"
          [{ name = "k"; kind = level; }
            { name = "S"; kind = ms: u (builtins.elemAt ms 0); }
            {
              name = "P";
              kind = ms:
                let
                  k = builtins.elemAt ms 0;
                  S = builtins.elemAt ms 1;
                in
                forall "_" S (_: u k);
            }]
          (ps: builtins.elemAt ps 0)
          (ps:
            let
              k = builtins.elemAt ps 0;
              S = builtins.elemAt ps 1;
              P = builtins.elemAt ps 2;
            in
            [
              (con "sup" [
                (fieldAt k "s" S)
                (piFieldDAt k "f" (prev: app P prev.s))
              ])
            ]);
    };

    # Surface forwarders onto the macro-derived prelude. `nat` is
    # `NatDT.T` directly — monomorphic `T` is a `"mu"` HOAS node carrying
    # `_dtypeMeta`. `listOf`/`sum` are spines of `app` over the
    # polymorphic `T`, keeping the parameter HOAS as a literal structural
    # slot. The un-reduced app form carries two pieces of information the
    # β-reduced `mu (app ListDT.D A)` destroys: `_dtypeMeta` from the
    # polyField head and the parameter HOAS with any surface sugar intact
    # (`H.record`, `H.variant`, `H.maybe`). elaborateValue / validateValue
    # / extractInner all dispatch on the app-spine directly and never
    # round-trip through a kernel value to recover the parameter.
    nat = api.leaf {
      description = "nat: HOAS `Nat` type former — generated by `NatDT.T` from the macro-derived natural-number datatype; serves as the index sort for vector / list-length families.";
      signature = "nat : Hoas";
      value = self.NatDT.T;
    };
    listOfAt = api.leaf {
      description = "listOfAt: universe-polymorphic list type former — `listOfAt level A` builds `List A` at the given universe level, used when the homogeneous-level `listOf` cannot carry an element type above U(0).";
      signature = "listOfAt : Hoas -> Hoas -> Hoas  -- level, A";
      value = k: A:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.implicitApp (self.implicitApp self.ListDT.T kTm) A;
    };
    listOf = api.leaf {
      description = "listOf: HOAS list type former — `listOf elemTy` is `μ Unit listDesc tt` at element type `elemTy`; the description-derived counterpart to Nix-native lists.";
      signature = "listOf : Hoas -> Hoas";
      value = A: self.listOfAt self.levelZero A;
    };
    sumAt = api.leaf {
      description = "sumAt: universe-polymorphic coproduct — `sumAt level A B` builds `A + B` at the given universe level, used when the homogeneous-level `sum` cannot decide the bound witness.";
      signature = "sumAt : Hoas -> Hoas -> Hoas -> Hoas  -- level, A, B";
      value = k: A: B:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.implicitApp (self.implicitApp (self.implicitApp self.SumDT.T kTm) A) B;
    };
    sum = api.leaf {
      description = "sum: HOAS coproduct type former — `sum A B` builds `A + B` via `SumDT.T` at the implicit base level; inhabitants enter via `inl` / `inr`.";
      signature = "sum : Hoas -> Hoas -> Hoas";
      value = A: B: self.sumAt self.levelZero A B;
    };
    w = api.leaf {
      description = "w: W-type former — generalised inductive type for trees with arbitrary branching; foundational for encoding finitely-branching datatypes outside the description layer.";
      signature = "w : Hoas -> Hoas -> Hoas  -- shapeTy, posFn";
      value = k: S: P: self.app (self.app (self.app self.WDT.T k) S) P;
    };

    # Macro-introduced constructors. `zero`/`nil`/`inl`/`inr` are spines
    # over the polymorphic `T` in `datatypeP`; `succ`/`cons` similarly
    # forward through the macro so the Nix-level surface stays unchanged
    # while the elaborated Tm flows through the `dt-ctor-mono` /
    # `dt-ctor-poly` chain-flatten path.
    zero = api.leaf {
      description = "zero: HOAS `Nat` constructor — the natural-number zero; introduces `nat` at the `descRet` summand of `natDesc`.";
      signature = "zero : Hoas";
      value = self.NatDT.zero;
    };
    succ = api.leaf {
      description = "succ: HOAS `Nat` successor — `succ n` builds `n + 1`; introduces `nat` at the `descRec descRet` summand.";
      signature = "succ : Hoas -> Hoas";
      value = h: self.app self.NatDT.succ h;
    };
    nil = api.leaf {
      description = "nil: HOAS empty-list constructor — `nil : listOf A`; element type inferred from the expected type.";
      signature = "nil : Hoas";
      value = self.ListDT.nil;
    };
    cons = api.leaf {
      description = "cons: HOAS list-cons constructor — `cons h t` prepends `h : A` to `t : listOf A`; element type inferred.";
      signature = "cons : Hoas -> Hoas -> Hoas  -- head, tail";
      value = h: t: self.app (self.app self.ListDT.cons h) t;
    };
    nilAtExplicit = api.leaf {
      description = "nilAtExplicit: internal List nil with hidden level + element type supplied explicitly for rigid/raw evaluation sites.";
      signature = "nilAtExplicit : Level -> Hoas -> Hoas  -- level, elemTy";
      value = k: A:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.implicitApp (self.implicitApp self.ListDT.nil kTm) A;
    };
    consAtExplicit = api.leaf {
      description = "consAtExplicit: internal List cons with hidden level + element type supplied explicitly for rigid/raw evaluation sites.";
      signature = "consAtExplicit : Level -> Hoas -> Hoas -> Hoas -> Hoas  -- level, elemTy, head, tail";
      value = k: A: h: t:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.app (self.app (self.implicitApp (self.implicitApp self.ListDT.cons kTm) A) h) t;
    };
    inlAt = api.leaf {
      description = "inlAt: universe-polymorphic left-injection — `inlAt v` builds `Left v : Sum A B`; level, leftTy, rightTy inferred.";
      signature = "inlAt : Hoas -> Hoas  -- value";
      value = v: self.app self.SumDT.Left v;
    };
    inrAt = api.leaf {
      description = "inrAt: universe-polymorphic right-injection — `inrAt v` builds `Right v : Sum A B`; level, leftTy, rightTy inferred.";
      signature = "inrAt : Hoas -> Hoas  -- value";
      value = v: self.app self.SumDT.Right v;
    };
    inlAtExplicit = api.leaf {
      description = "inlAtExplicit: internal Sum left-injection with hidden parameters supplied explicitly for raw evaluation sites.";
      signature = "inlAtExplicit : Level -> Hoas -> Hoas -> Hoas -> Hoas  -- level, leftTy, rightTy, value";
      value = k: A: B: v:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.app (self.implicitApp (self.implicitApp (self.implicitApp self.SumDT.Left kTm) A) B) v;
    };
    inrAtExplicit = api.leaf {
      description = "inrAtExplicit: internal Sum right-injection with hidden parameters supplied explicitly for raw evaluation sites.";
      signature = "inrAtExplicit : Level -> Hoas -> Hoas -> Hoas -> Hoas  -- level, leftTy, rightTy, value";
      value = k: A: B: v:
        let kTm = if builtins.isInt k then self.natToLevel k else k; in
        self.app (self.implicitApp (self.implicitApp (self.implicitApp self.SumDT.Right kTm) A) B) v;
    };
    inl = api.leaf {
      description = "inl: HOAS sum left-injection — `inl v` builds `Left v : Sum A B`; level, leftTy, rightTy inferred. Alias of `inlAt` post-implicit-migration.";
      signature = "inl : Hoas -> Hoas  -- value";
      value = self.inlAt;
    };
    inr = api.leaf {
      description = "inr: HOAS sum right-injection — `inr v` builds `Right v : Sum A B`; level, leftTy, rightTy inferred. Alias of `inrAt` post-implicit-migration.";
      signature = "inr : Hoas -> Hoas  -- value";
      value = self.inrAt;
    };
    wDesc = api.leaf {
      description = "wDesc: W-type description forwarder — alias for `WDT.D`, the description of W-type trees over shape S and position family pos.";
      signature = "wDesc : Hoas -> (Hoas -> Hoas) -> Hoas";
      value = k: S: P: self.app (self.app (self.app self.WDT.D k) S) P;
    };
    sup = api.leaf {
      description = "sup: HOAS W-type constructor `sup s t` — supplies the node-shape `s` and the recursive-children family `t : pos s → W`.";
      signature = "sup : Hoas -> Hoas -> Hoas";
      value = k: S: P: s: f:
        self.app (self.app (self.app (self.app (self.app self.WDT.sup k) S) P) s) f;
    };
    wElim = api.leaf {
      description = "wElim: W-type eliminator forwarder — alias for `WDT.elim`, the dependent recursor for W-type trees.";
      signature = "wElim : Level -> Hoas -> (Hoas -> Hoas) -> Hoas -> Hoas -> Hoas -> Hoas";
      value = k: K: S: P: Q: step: x:
        self.app (self.app (self.app (self.app (self.app (self.app (self.WDT.elim K) k) S) P) Q) step) x;
    };
  };
  tests = {
    "datatype-indexed-pi-field-constructor-checks" = {
      expr =
        let
          H = self;
          IndexedPi = H.datatypeI "IndexedPiVoid" H.bool [
            (H.conI "mk"
              [ (H.piFieldAtIndex 0 "next" H.void (_prev: _x: H.true_)) ]
              (_: H.true_))
          ];
          T = H.muI H.bool IndexedPi.D H.true_;
          vacuous = H.lam "x" H.void (x: H.absurd T x);
        in
          !((H.checkHoas T (H.app IndexedPi.mk vacuous)) ? error);
      expected = true;
    };

    "datatype-indexed-pi-field-metadata" = {
      expr =
        let
          H = self;
          IndexedPi = H.datatypeI "IndexedPiMeta" H.bool [
            (H.conI "mk"
              [ (H.piFieldDAtIndex 0 "next" (_: H.void) (_prev: _x: H.true_)) ]
              (_: H.true_))
          ];
          field = builtins.head
            ((builtins.head IndexedPi._dtypeMeta.constructors).fields);
        in
        {
          inherit (field) name kind;
          hasBranch = field.branchIdxFn != null;
        };
      expected = {
        name = "next";
        kind = "piDAt";
        hasBranch = true;
      };
    };

    "datatype-unit-pi-rejects-indexed-family" = {
      expr =
        let
          H = self;
        in
        (builtins.tryEval (
          (H.datatypeI "BadIndexedPi" H.bool [
            (H.conI "mk" [ (H.piField "next" H.void) ] (_: H.true_))
          ]).D.term.f._htag
        )).success;
      expected = false;
    };
  };
}
