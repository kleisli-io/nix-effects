# Generic ornament entry points over generated datatypes.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  HI = fx.tc.hoas._internal._indexed;

  algSupportedFragment = [ "ret" "arg" "rec" "pi" "plus" ];

  isRawOrn = x:
    builtins.isAttrs x && (x._ornTag or null) == "orn";

  isFunctionalOrn = x:
    builtins.isAttrs x && (x._functionalOrnTag or null) == "functional-ornament";

  isLeafOrn = x:
    builtins.isAttrs x && (x._leafOrnTag or null) == "leaf-ornament";

  isUnitTy = x:
    builtins.isAttrs x && (x._htag or null) == "unit";

  coreOf = x:
    if builtins.isAttrs x && x ? ornament then x.ornament else x;

  # Leaf ornaments have no μ-encoded base; their Nix-meta forget is
  # consumed directly, not via `H.ornForget`.
  rawOrnOf = ornamented:
    if isLeafOrn ornamented then null
    else if isRawOrn ornamented then ornamented
    else if isFunctionalOrn ornamented then ornamented.ornament
    else if builtins.isAttrs ornamented && ornamented ? ornament && isRawOrn ornamented.ornament
    then ornamented.ornament
    else null;

  forgetHoasOf = ornamented:
    if ornamented ? forget0 then ornamented.forget0
    else if ornamented ? forget then ornamented.forget
    else if builtins.isAttrs ornamented
      && ornamented ? ornament
      && builtins.isAttrs ornamented.ornament
      && ((ornamented.ornament._ornTag or null) == "orn")
    then H.ornForget ornamented.ornament
    else if builtins.isAttrs ornamented && ((ornamented._ornTag or null) == "orn")
    then H.ornForget ornamented
    else throw "generic.ornaments.forgetHoas: expected ornamented datatype or raw ornament";

  forgetHoasApplied = ornamented: value:
    let raw = rawOrnOf ornamented; in
    if raw != null && isUnitTy raw.J
    then H.app (H.app (H.ornForget raw) H.tt) value
    else H.app (forgetHoasOf ornamented) value;

  # `G.ornaments.forget : Ornamented → Value → Value` is one
  # morphism; the HOAS-term and Nix-meta paths are two
  # evaluations of it. Dispatch is structural on the well-formed
  # sum `_htag` (HOAS term) ⊕ `_con` (Nix-meta μ-value). Neither,
  # both, or unrecognised inputs throw.
  forgetValue = ornamented: value:
    if !(builtins.isAttrs value) then
      throw "generic.ornaments.forget: value must be an attrset (HOAS term with `_htag` or μ-value with `_con`); got ${builtins.typeOf value}"
    else
      let hasHtag = value ? _htag; hasCon = value ? _con; in
      if hasHtag && hasCon then
        throw "generic.ornaments.forget: value carries both `_htag` and `_con`; cannot dispatch"
      else if hasHtag then forgetHoasApplied ornamented value
      else if hasCon then forgetMetaImpl ornamented value
      else throw "generic.ornaments.forget: value is neither a HOAS term (`_htag`) nor a μ-encoded Nix value (`_con`)";

  isAlg = x:
    builtins.isAttrs x && (x._algOrnTag or null) == "alg";

  descKindLabel = kind:
    if kind == "ret" then "descRet"
    else if kind == "arg" then "descArg"
    else if kind == "rec" then "descRec"
    else if kind == "plus" then "descPlus"
    else if kind == "pi" then "descPi"
    else kind;

  sampleAlgBody = path: body:
    let r = builtins.tryEval (body H.tt);
    in if r.success then r.value
    else throw "generic.ornaments.algShape: path ${path}: algebra body could not be sampled for shape checking";

  algShapeAt = path: alg:
    if !(isAlg alg) then { kind = "non-algebra"; }
    else if alg.tag == "ret" then { kind = "ret"; }
    else if alg.tag == "arg" then {
      kind = "arg";
      body = algShapeAt "${path}.arg" (sampleAlgBody path alg.body);
    }
    else if alg.tag == "rec" then {
      kind = "rec";
      sub = algShapeAt "${path}.rec" (sampleAlgBody path alg.body);
    }
    else if alg.tag == "pi" then {
      kind = "pi";
      sub = algShapeAt "${path}.pi" alg.body;
    }
    else if alg.tag == "plus" then {
      kind = "plus";
      left = algShapeAt "${path}.left" alg.left;
      right = algShapeAt "${path}.right" alg.right;
    }
    else { kind = alg.tag; };

  algShapeOf = alg:
    algShapeAt "root" alg;

  algShapeMismatch = path: descShape: algShape:
    "generic.ornaments.algShape: path ${path}: desc node ${descKindLabel descShape.kind} expects algebra node '${descShape.kind}', got '${algShape.kind}'";

  algShapeDiagnosticsAt = path: descShape: algShape:
    if algShape.kind != descShape.kind then
      [ (algShapeMismatch path descShape algShape) ]
    else if descShape.kind == "arg" then
      algShapeDiagnosticsAt "${path}.arg" descShape.body algShape.body
    else if descShape.kind == "rec" then
      algShapeDiagnosticsAt "${path}.rec" descShape.sub algShape.sub
    else if descShape.kind == "pi" then
      algShapeDiagnosticsAt "${path}.pi" descShape.sub algShape.sub
    else if descShape.kind == "plus" then
      (algShapeDiagnosticsAt "${path}.left" descShape.left algShape.left)
      ++ (algShapeDiagnosticsAt "${path}.right" descShape.right algShape.right)
    else [ ];

  algShapeDiagnosticsOf = args:
    let
      D = args.D or args.baseD;
      descShape = self.shape D;
      algShape = algShapeOf args.algebra;
    in
    algShapeDiagnosticsAt "root" descShape algShape;

  checkAlgShapeOf = args:
    let errors = algShapeDiagnosticsOf args; in
    if errors == [ ] then args.algebra
    else throw (builtins.concatStringsSep "\n" errors);

  diagnosticText = d:
    d.text or d.message;

  functionalDiagnostic = code: path: message: {
    inherit code path message;
    severity = "error";
    text = "generic.ornaments.functional: path ${builtins.concatStringsSep "." path}: ${message}";
  };

  isFunctionalSynthesisArgs = args:
    builtins.isAttrs args && (args ? base || args ? spec || args ? synth);

  functionalArgs = args:
    if builtins.isAttrs args && args ? ornament
    then args // { ornament = coreOf args.ornament; }
    else args;

  attrOrEmpty = x:
    if builtins.isAttrs x then x else { };

  maybeAttr = attrs: name:
    if builtins.isAttrs attrs && builtins.hasAttr name attrs
    then builtins.getAttr name attrs
    else null;

  functionalPath = conName: fieldName:
    [ "functional" "constructors" conName "fields" fieldName ];

  functionalProofPath = conName: fieldName:
    [ "functional" "constructors" conName "proofs" fieldName ];

  functionalMeasurePath = conName: fieldName:
    [ "functional" "constructors" conName "fields" fieldName "measure" ];

  isProofInsert = fieldSpec:
    (fieldSpec.proof or false) || ((fieldSpec.role or null) == "proof");

  measureFns = args:
    attrOrEmpty (args.measures or (if args ? measure then { default = args.measure; } else { }));

  measureNames = args:
    builtins.attrNames (measureFns args);

  measureNameOf = fieldSpec:
    fieldSpec.measure or null;

  measureBuilder = args: name:
    maybeAttr (measureFns args) name;

  fieldBuilder = synth: conName: fieldSpec:
    let
      name = fieldSpec.insert;
      conSynth = attrOrEmpty (maybeAttr (attrOrEmpty (synth.constructors or { })) conName);
      fieldSynth = attrOrEmpty (conSynth.fields or { });
      proofSynth = attrOrEmpty (conSynth.proofs or { });
      fromFields = maybeAttr fieldSynth name;
      fromProofs = maybeAttr proofSynth name;
      fromCon = maybeAttr conSynth name;
    in
    if isProofInsert fieldSpec && fieldSpec ? prove then fieldSpec.prove
    else if fieldSpec ? build then fieldSpec.build
    else if isProofInsert fieldSpec && fromProofs != null then fromProofs
    else if fromFields != null then fromFields
    else fromCon;

  proofObligation = conName: fieldName:
    let
      path = functionalProofPath conName fieldName;
      message = "proof field needs builder";
    in
    {
      code = "functional.unresolved-proof";
      kind = "proof";
      field = fieldName;
      constructor = conName;
      inherit path message;
      text = "generic.ornaments.functional: path ${builtins.concatStringsSep "." path}: ${message}";
    };

  measureObligation = conName: fieldName: measureName:
    let
      path = functionalMeasurePath conName fieldName;
      message = "measure field needs declared measure";
    in
    {
      code = "functional.missing-measure";
      kind = "measure";
      field = fieldName;
      measure = measureName;
      constructor = conName;
      inherit path message;
      text = "generic.ornaments.functional: path ${builtins.concatStringsSep "." path}: ${message}";
    };

  baseFieldByName = con: name:
    let
      matches = builtins.filter (f: f.name == name) (con.fields or [ ]);
    in
    if matches == [ ] then null else builtins.head matches;

  isPiFieldKind = kind:
    kind == "pi" || kind == "piD" || kind == "piAt" || kind == "piDAt";

  synthesisFieldDiagnostics = args: con: fieldSpec:
    let
      synth = args.synth or { };
    in
    if fieldSpec ? insert then
      let
        builder = fieldBuilder synth con.name fieldSpec;
        proof = isProofInsert fieldSpec;
        measureName = measureNameOf fieldSpec;
        measureFn =
          if measureName == null then null else measureBuilder args measureName;
        path =
          if proof
          then functionalProofPath con.name fieldSpec.insert
          else functionalPath con.name fieldSpec.insert;
        measurePath = functionalMeasurePath con.name fieldSpec.insert;
      in
      if measureName != null && measureFn == null then
        [ (functionalDiagnostic "functional.missing-measure" measurePath "measure field needs declared measure") ]
      else if measureName != null && !(builtins.isFunction measureFn) then
        [ (functionalDiagnostic "functional.invalid-measure" measurePath "measure must be a function") ]
      else if builder == null && measureName != null then
        [ ]
      else if builder == null && proof then
        [ ]
      else if builder == null then
        [ (functionalDiagnostic "functional.missing-builder" path "inserted field needs builder") ]
      else if !(builtins.isFunction builder) && proof then
        [ (functionalDiagnostic "functional.invalid-proof-builder" path "proof field builder must be a function") ]
      else if !(builtins.isFunction builder) then
        [ (functionalDiagnostic "functional.invalid-builder" path "inserted field builder must be a function") ]
      else [ ]
    else if fieldSpec ? keep then
      let
        baseField = baseFieldByName con fieldSpec.keep;
        kind = if baseField == null then null else baseField.kind;
        path = functionalPath con.name fieldSpec.keep;
      in
      if baseField == null then [ ]
      else if kind == "recAt" then
        [ (functionalDiagnostic "functional.unsupported-recursive-synthesis" path "recursive keep synthesis is not supported yet") ]
      else if isPiFieldKind kind then
        [ (functionalDiagnostic "functional.unsupported-pi-synthesis" path "dependent function keep synthesis is not supported yet") ]
      else [ ]
    else [ ];

  synthesisFieldObligations = args: con: fieldSpec:
    let
      synth = args.synth or { };
      builder =
        if fieldSpec ? insert then fieldBuilder synth con.name fieldSpec else null;
      measureName =
        if fieldSpec ? insert then measureNameOf fieldSpec else null;
      measureFn =
        if measureName == null then null else measureBuilder args measureName;
    in
    if fieldSpec ? insert && measureName != null && measureFn == null
    then [ (measureObligation con.name fieldSpec.insert measureName) ]
    else if fieldSpec ? insert && isProofInsert fieldSpec && builder == null
    then [ (proofObligation con.name fieldSpec.insert) ]
    else [ ];

  synthesisConstructorDiagnostics = args: con:
    let
      conSpec = builtins.getAttr con.name args.spec.constructors;
      fields = conSpec.fields or [ ];
    in
    builtins.concatMap (synthesisFieldDiagnostics args con) fields;

  synthesisConstructorObligations = args: con:
    let
      conSpec = builtins.getAttr con.name args.spec.constructors;
      fields = conSpec.fields or [ ];
    in
    builtins.concatMap (synthesisFieldObligations args con) fields;

  synthesisObligations = args:
    if !(builtins.isAttrs args) || !(args ? base) || !(args ? spec) then [ ]
    else
      let
        ornamentValidation = H.validateOrnament args.base args.spec;
        info = self.datatypeInfo args.base;
      in
      if !(ornamentValidation.ok) then [ ]
      else builtins.concatMap (synthesisConstructorObligations args) info.constructors;

  synthesisDiagnosticRecords = args:
    if !(builtins.isAttrs args) then
      [ (functionalDiagnostic "functional.invalid-spec" [ "functional" ] "expected attrset spec") ]
    else if !(args ? base) then
      [ (functionalDiagnostic "functional.missing-base" [ "functional" "base" ] "functional synthesis needs `base`") ]
    else if !(args ? spec) then
      [ (functionalDiagnostic "functional.missing-spec" [ "functional" "spec" ] "functional synthesis needs `spec`") ]
    else
      let
        ornamentValidation = H.validateOrnament args.base args.spec;
        info = self.datatypeInfo args.base;
        indexedDiagnostics =
          if (info.indexed or false) || args.spec ? index then
            [ (functionalDiagnostic "functional.unsupported-indexed-synthesis" [ "functional" "index" ] "indexed synthesis is not supported yet") ]
          else [ ];
        obligationDiagnostics = map
          (o:
            functionalDiagnostic o.code o.path o.message)
          (synthesisObligations args);
        builderDiagnostics =
          builtins.concatMap (synthesisConstructorDiagnostics args) info.constructors;
      in
      if !(ornamentValidation.ok) then ornamentValidation.diagnostics
      else indexedDiagnostics ++ obligationDiagnostics ++ builderDiagnostics;

  validateFunctionalSynthesis = args:
    let
      diagnostics = synthesisDiagnosticRecords args;
      obligations = synthesisObligations args;
    in
    if diagnostics == [ ] then { ok = true; diagnostics = [ ]; inherit obligations; }
    else { ok = false; inherit diagnostics obligations; };

  synthesizeRecord = args: ornamented: i: baseValue:
    let
      synth = args.synth or { };
      measureFnsForArgs = measureFns args;
      baseRecord = self.view args.base.T baseValue;
      conName = baseRecord._con;
      conSpec = builtins.getAttr conName args.spec.constructors;
      measureContext = name: {
        index = i;
        constructor = conName;
        path = [ "functional" "constructors" conName "measures" name ];
        inherit baseValue baseRecord;
      };
      measures = builtins.mapAttrs
        (name: measure: measure (measureContext name))
        measureFnsForArgs;
      defaultMeasure = measures.default or null;
      step = acc: fieldSpec:
        if fieldSpec ? keep then
          let
            value = builtins.getAttr fieldSpec.keep baseRecord;
          in
          acc // {
            basePrev = acc.basePrev // { ${fieldSpec.keep} = value; };
            ornPrev = acc.ornPrev // { ${fieldSpec.keep} = value; };
            ornRecord = acc.ornRecord // { ${fieldSpec.keep} = value; };
          }
        else
          let
            builder = fieldBuilder synth conName fieldSpec;
            context = {
              index = i;
              constructor = conName;
              field = fieldSpec.insert;
              fieldSpec = fieldSpec;
              path = functionalPath conName fieldSpec.insert;
              measure = defaultMeasure;
              inherit baseRecord measures;
              inherit (acc) basePrev ornPrev;
            };
            value =
              if builder != null then builder context
              else if fieldSpec ? measure then builtins.getAttr fieldSpec.measure measures
              else throw "generic.ornaments.functional: field '${fieldSpec.insert}' has no builder";
          in
          acc // {
            ornPrev = acc.ornPrev // { ${fieldSpec.insert} = value; };
            ornRecord = acc.ornRecord // { ${fieldSpec.insert} = value; };
          };
      result = builtins.foldl' step
        {
          basePrev = { };
          ornPrev = { };
          ornRecord = { _con = conName; };
        }
        (conSpec.fields or [ ]);
    in
    self.review ornamented.T result.ornRecord;

  functionalFromSynthesis = args:
    let
      validation = validateFunctionalSynthesis args;
      ornamented = self.ornament args.base args.spec;
    in
    if !(validation.ok) then
      throw (builtins.concatStringsSep "\n" (map diagnosticText validation.diagnostics))
    else
      H.functionalOrnament {
        ornament = ornamented.ornament;
        chooseIndex = args.chooseIndex or (i: _baseValue: i);
        indexProof = args.indexProof or (_i: _baseValue: H.bootRefl);
        section = synthesizeRecord args ornamented;
        meta = (args.meta or { }) // {
          inherit (args) base spec;
          synth = args.synth or { };
          measures = measureNames args;
          algebra = args.algebra or null;
          inherit (validation) obligations;
          inherit ornamented;
        };
      };

  validateFunctionalArgs = args:
    if isFunctionalSynthesisArgs args
    then validateFunctionalSynthesis args
    else H.validateFunctionalOrnament (functionalArgs args);

  tryFunctionalArgs = args:
    let validation = validateFunctionalArgs args; in
    if validation.ok then validation // { value = functionalValue args; }
    else validation;

  functionalValue = args:
    if isFunctionalSynthesisArgs args
    then functionalFromSynthesis args
    else H.functionalOrnament (functionalArgs args);

  # Functorial container lifts: given `o : Ornament A A'`, produce
  # `lift.F o : Ornament (F A) (F A')` for each strictly-positive
  # container functor F (Dagand thesis §6). All produce leaf-style
  # ornaments whose Nix-meta forget / section map structurally over the
  # container.
  metaForgetOf = label: o:
    if builtins.isAttrs o && o ? forget && builtins.isFunction o.forget
    then o.forget
    else if builtins.isAttrs o && o ? _ornMeta
    then (value: forgetMetaImpl o value)
    else throw "${label}: input has no Nix-meta `forget` function";

  metaSectionOf = label: o:
    if builtins.isAttrs o && o ? section && builtins.isFunction o.section
    then o.section
    else if builtins.isAttrs o && o ? _ornMeta
    then (_value: throw "${label}: μ-ornament has no Nix-meta `section`; only `forget` is exposed at the meta level")
    else throw "${label}: input has no Nix-meta `section` function";

  forwardTypeOf = label: o:
    if isLeafOrn o then o.primitive
    else if builtins.isAttrs o && o ? _ornMeta && o ? T then o.T
    else throw "${label}: cannot extract forward type — input must be a leaf ornament or a decorated μ-ornament";

  liftList = o:
    let
      f = metaForgetOf "ornaments.lift.list" o;
      s = metaSectionOf "ornaments.lift.list" o;
    in
    H.leafOrnament {
      primitive = H.listOf (forwardTypeOf "ornaments.lift.list" o);
      forget = xs: map f xs;
      section = xs: map s xs;
      meta = { kind = "lift.list"; inner = o; };
    };

  liftAttrs = o:
    let
      f = metaForgetOf "ornaments.lift.attrs" o;
      s = metaSectionOf "ornaments.lift.attrs" o;
    in
    H.leafOrnament {
      primitive = H.attrs;
      forget = as: builtins.mapAttrs (_n: f) as;
      section = as: builtins.mapAttrs (_n: s) as;
      meta = { kind = "lift.attrs"; inner = o; };
    };

  liftMaybe = o:
    let
      f = metaForgetOf "ornaments.lift.maybe" o;
      s = metaSectionOf "ornaments.lift.maybe" o;
    in
    H.leafOrnament {
      primitive = H.maybe (forwardTypeOf "ornaments.lift.maybe" o);
      forget = m: if m == null then null else f m;
      section = m: if m == null then null else s m;
      meta = { kind = "lift.maybe"; inner = o; };
    };

  liftField = fieldName: o:
    let
      f = metaForgetOf "ornaments.lift.field" o;
      s = metaSectionOf "ornaments.lift.field" o;
    in
    if !(builtins.isString fieldName)
    then throw "ornaments.lift.field: fieldName must be a string"
    else
      H.leafOrnament {
        primitive = H.attrs;
        forget = r:
          if !(builtins.isAttrs r) || !(r ? ${fieldName})
          then throw "ornaments.lift.field.forget: input lacks field '${fieldName}'"
          else r // { ${fieldName} = f r.${fieldName}; };
        section = r:
          if !(builtins.isAttrs r) || !(r ? ${fieldName})
          then throw "ornaments.lift.field.section: input lacks field '${fieldName}'"
          else r // { ${fieldName} = s r.${fieldName}; };
        meta = { kind = "lift.field"; inner = o; fieldName = fieldName; };
      };

  # Direct evaluation of an ornament's forget on a Nix-meta
  # μ-value. Walks the spec's constructor arms to copy kept
  # fields, drop inserted fields, and dispatch keepSub fields
  # through the sub-ornament's forget. The sub-ornament's
  # `forget` is the Nix-meta function for leaf ornaments and is
  # routed back through `forgetMetaImpl` recursively for
  # decorated μ-sub-ornaments. Constructor `_con` is preserved
  # because the kernel reuses the base constructor name for the
  # refined branch.
  hasOrnMeta = o:
    builtins.isAttrs o && o ? _ornMeta;

  fieldSpecKindOf = spec:
    if spec ? insert && spec ? keep then "invalid"
    else if spec ? insert then "insert"
    else if spec ? keep && spec ? sub then "keepSub"
    else if spec ? keep then "keep"
    else "invalid";

  applySubForgetMeta = sub: fieldValue:
    if isLeafOrn sub then sub.forget fieldValue
    else if hasOrnMeta sub then forgetMetaImpl sub fieldValue
    else if isRawOrn sub then
      throw "generic.ornaments.forgetMeta: raw μ-ornament sub has no Nix-meta forget; use the decorated form (datatype + ornament)"
    else throw "generic.ornaments.forgetMeta: keepSub `sub` must be a leaf ornament or a decorated μ-ornament";

  forgetMetaImpl = ornamented: value:
    if !(hasOrnMeta ornamented) then
      throw "generic.ornaments.forgetMeta: expected ornamented datatype (with _ornMeta)"
    else if !(builtins.isAttrs value) then
      throw "generic.ornaments.forgetMeta: expected attrset μ-value, got ${builtins.typeOf value}"
    else if !(value ? _con) then
      throw "generic.ornaments.forgetMeta: μ-value lacks `_con` tag"
    else
      let
        meta = ornamented._ornMeta;
        spec = meta.spec;
        conName = value._con;
        conSpec =
          if spec ? constructors && spec.constructors ? ${conName}
          then spec.constructors.${conName}
          else throw "generic.ornaments.forgetMeta: no spec arm for constructor '${conName}'";
        specFields = conSpec.fields or [ ];
        oneField = acc: fspec:
          let kind = fieldSpecKindOf fspec; in
          if kind == "insert" then acc
          else if kind == "keep" then
            if !(value ? ${fspec.keep})
            then throw "generic.ornaments.forgetMeta: μ-value lacks kept field '${fspec.keep}'"
            else acc // { ${fspec.keep} = value.${fspec.keep}; }
          else if kind == "keepSub" then
            if !(value ? ${fspec.keep})
            then throw "generic.ornaments.forgetMeta: μ-value lacks kept field '${fspec.keep}'"
            else acc // {
              ${fspec.keep} = applySubForgetMeta fspec.sub value.${fspec.keep};
            }
          else throw "generic.ornaments.forgetMeta: field spec under '${conName}' is neither keep nor insert";
        forgottenFields = builtins.foldl' oneField { } specFields;
      in
      { _con = conName; } // forgottenFields;
in
{
  scope = {
    algSupportedFragment = api.leaf {
      value = algSupportedFragment;
      description = "algSupportedFragment: the constructor-tag whitelist `[ \"ret\" \"arg\" \"rec\" \"pi\" \"plus\" ]` accepted by `algOrn`; surfaced as the `expected` field of `algShape`'s diagnostic when an algebra falls outside this fragment.";
      signature = "algSupportedFragment : [String]";
    };

    ornament = api.leaf {
      value = base: spec:
        H.ornament base spec;
      description = "ornament: user-facing entry — given a generated `DataSpec` (`base`) and a constructor-by-constructor `spec`, produce the ornamented `Datatype` with `forget` morphism baked in.";
      signature = "ornament : DataSpec -> OrnamentSpec -> Datatype";
    };

    forget = api.leaf {
      value = ornamented: value:
        forgetValue ornamented value;
      description = "forget: apply the forgetting morphism to an ornamented `value`, returning the underlying base-description value at the same J-index.";
      signature = "forget : OrnamentedDatatype -> Tm -> Tm";
    };

    forgetHoas = api.leaf {
      value = forgetHoasOf;
      description = "forgetHoas: yield the HOAS-level `forget` term `J -> ornMu -> baseMu` for an ornamented datatype or raw ornament; prefers `forget0` when the J-index is `Unit`.";
      signature = "forgetHoas : OrnamentedDatatype -> Tm";
    };

    compose = api.leaf {
      value = outer: inner:
        H.ornCompose (coreOf outer) (coreOf inner);
      description = "compose: vertical composition of ornaments at the generic surface — `outer ∘ inner` lifts the inner ornament's J through the outer's K, automatically unpacking `.ornament` cores.";
      signature = "compose : Ornament -> Ornament -> Ornament  -- outer, inner";
    };

    algShape = api.leaf {
      value = algShapeOf;
      description = "algShape: total predicate `{ ok, kind, expected }` over an algebra value's shape — surfaces the offending `kind` when the algebra falls outside `algSupportedFragment`.";
      signature = "algShape : Algebra -> { ok : Bool, kind? : String, expected? : [String] }";
    };

    algShapeDiagnostics = api.leaf {
      value = algShapeDiagnosticsOf;
      description = "algShapeDiagnostics: human-readable diagnostic strings for an algebra whose shape falls outside the supported `ret/arg/rec/pi/plus` fragment.";
      signature = "algShapeDiagnostics : Attrs -> [String]";
    };

    checkAlgShape = api.leaf {
      value = checkAlgShapeOf;
      description = "checkAlgShape: return `algebra` unchanged when it lies in the supported fragment, otherwise throw with the concatenated `algShapeDiagnostics` text.";
      signature = "checkAlgShape : Attrs -> Algebra  -- throws on unsupported shape";
    };

    algOrn = api.leaf {
      value = args:
        H.algOrn (args // { algebra = checkAlgShapeOf args; });
      description = "algOrn: build an algebraic ornament from `args`, running `checkAlgShape` first so unsupported algebra shapes are rejected with structured diagnostics before delegating to `H.algOrn`.";
      signature = "algOrn : { I?, J, baseD | D, erase, algebra, ... } -> Ornament";
    };

    pullbackHoas = api.leaf {
      value = ornamented: resultTy: baseFn:
        H.ornPullback (coreOf ornamented) resultTy baseFn;
      description = "pullbackHoas: HOAS-level pullback of a base function `baseFn : I -> baseMu -> R(i)` through an ornamented carrier — auto-unpacks `.ornament` cores from generated datatypes.";
      signature = "pullbackHoas : OrnamentedDatatype -> (Tm -> Tm) -> Tm -> Tm";
    };

    liftFold = api.leaf {
      value = ornamented: resultTy: baseFold:
        H.ornLiftFold (coreOf ornamented) resultTy baseFold;
      description = "liftFold: alias for `pullbackHoas` specialised to folds — composes a base fold with `forget` so it runs on ornamented carriers without re-deriving the algebra.";
      signature = "liftFold : OrnamentedDatatype -> (Tm -> Tm) -> Tm -> Tm";
    };

    pullback = api.leaf {
      value = ornamented: baseFn: value:
        H.app baseFn (forgetValue ornamented value);
      description = "pullback: apply a base function `baseFn` to a forgotten ornamented value — the value-level companion to `pullbackHoas`, running entirely in HOAS application.";
      signature = "pullback : OrnamentedDatatype -> Tm -> Tm -> Tm";
    };

    functional = api.leaf {
      value = functionalValue;
      description = "functional: total smart constructor for a functional ornament — validates `args` via `validateFunctional` and throws with diagnostics on failure, otherwise returns the built record.";
      signature = "functional : Attrs -> FunctionalOrnament  -- throws on invalid spec";
    };

    validateFunctional = api.leaf {
      value = args:
        validateFunctionalArgs args;
      description = "validateFunctional: total predicate `{ ok, diagnostics }` over candidate functional-ornament `args` — `coreOf` is applied to `.ornament` first so generated datatypes pass through.";
      signature = "validateFunctional : Attrs -> { ok : Bool, diagnostics : [Diagnostic] }";
    };

    tryFunctional = api.leaf {
      value = args:
        tryFunctionalArgs args;
      description = "tryFunctional: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the built functional ornament when valid, otherwise diagnostics-only.";
      signature = "tryFunctional : Attrs -> { ok : Bool, diagnostics : [Diagnostic], value? : FunctionalOrnament }";
    };

    diagnoseFunctional = api.leaf {
      value = args:
        map diagnosticText (validateFunctionalArgs args).diagnostics;
      description = "diagnoseFunctional: human-readable diagnostic strings for a candidate functional-ornament spec — derived from `validateFunctional` for surfacing in errors.";
      signature = "diagnoseFunctional : Attrs -> [String]";
    };

    validateFunctionalLaws = api.leaf {
      value = functional:
        H.validateFunctionalLaws functional;
      description = "validateFunctionalLaws: delegates to `H.validateFunctionalLaws` — total predicate `{ ok, diagnostics }` over a functional ornament's law-check bundle.";
      signature = "validateFunctionalLaws : FunctionalOrnament -> { ok : Bool, diagnostics : [Diagnostic] }";
    };

    diagnoseFunctionalLaws = api.leaf {
      value = functional:
        H.functionalLawDiagnostics functional;
      description = "diagnoseFunctionalLaws: human-readable diagnostic strings for failed law checks on a functional ornament — surfaces which law-check returned non-`true` or failed to evaluate.";
      signature = "diagnoseFunctionalLaws : FunctionalOrnament -> [String]";
    };

    composeFunctional = api.leaf {
      value = outer: inner:
        H.functionalCompose outer inner;
      description = "composeFunctional: vertical composition of two functional ornaments — threads `inner.chooseIndex` and `inner.section` into `outer` to produce a stacked section pipeline.";
      signature = "composeFunctional : FunctionalOrnament -> FunctionalOrnament -> FunctionalOrnament";
    };

    functionalSection = api.leaf {
      value = functional:
        H.ornSection functional;
      description = "functionalSection: extract the `section` slot of a functional ornament — the builder `i -> baseValue -> ornamentedValue` realising the section morphism.";
      signature = "functionalSection : FunctionalOrnament -> (Tm -> Tm -> Tm)";
    };

    functionalTargetIndex = api.leaf {
      value = functional:
        H.ornTargetIndex functional;
      description = "functionalTargetIndex: extract the `chooseIndex` slot of a functional ornament — the function `i -> baseValue -> J` that picks the ornamented index per base input.";
      signature = "functionalTargetIndex : FunctionalOrnament -> (Tm -> Tm -> Tm)";
    };

    functionalBuildIndexed = api.leaf {
      value = functional: index: baseValue:
        H.ornBuild functional index baseValue;
      description = "functionalBuildIndexed: build the ornamented value at an explicit `index` from `baseValue` — wraps `H.ornBuild` for the indexed surface.";
      signature = "functionalBuildIndexed : FunctionalOrnament -> Tm -> Tm -> Tm";
    };

    functionalBuild = api.leaf {
      value = functional: baseValue:
        H.ornBuild functional H.tt baseValue;
      description = "functionalBuild: build the ornamented value from `baseValue` at the unit index `tt` — convenience wrapper for J = `Unit` functional ornaments.";
      signature = "functionalBuild : FunctionalOrnament -> Tm -> Tm";
    };

    liftProducerIndexed = api.leaf {
      value = functional: index: baseFn: baseInput:
        H.ornLiftProducer functional baseFn index baseInput;
      description = "liftProducerIndexed: lift a base producer `baseFn : baseInput -> baseValue` through a functional ornament at an explicit J-index, returning the ornamented output.";
      signature = "liftProducerIndexed : FunctionalOrnament -> Tm -> (Tm -> Tm) -> Tm -> Tm";
    };

    liftProducer = api.leaf {
      value = functional: baseFn: baseInput:
        self.liftProducerIndexed functional H.tt baseFn baseInput;
      description = "liftProducer: lift a base producer through a functional ornament at unit index `tt` — convenience wrapper for J = `Unit`.";
      signature = "liftProducer : FunctionalOrnament -> (Tm -> Tm) -> Tm -> Tm";
    };

    liftTransformIndexed = api.leaf {
      value = args: outputIndex: inputIndex: ornamentedInput:
        H.ornLiftTransform
          {
            input =
              if isFunctionalOrn args.input then args.input else coreOf args.input;
            output = args.output;
            fn = args.fn;
          }
          outputIndex
          inputIndex
          ornamentedInput;
      description = "liftTransformIndexed: lift a base transform through paired input/output functional ornaments at explicit indices — auto-unpacks `.ornament` cores from the input side.";
      signature = "liftTransformIndexed : { input, output : FunctionalOrnament, fn } -> Tm -> Tm -> Tm -> Tm";
    };

    liftTransform = api.leaf {
      value = args: ornamentedInput:
        self.liftTransformIndexed args H.tt H.tt ornamentedInput;
      description = "liftTransform: lift a base transform through paired input/output functional ornaments at unit indices — convenience wrapper for J = `Unit` on both sides.";
      signature = "liftTransform : { input, output : FunctionalOrnament, fn } -> Tm -> Tm";
    };

    checkSpec = api.leaf {
      value = base: spec:
        (H.ornament base spec)._ornMeta;
      description = "checkSpec: surface `_ornMeta` from a built ornament — exposes `{ base, spec, core, cfg }` for downstream introspection of the ornament's provenance and shape.";
      signature = "checkSpec : DataSpec -> OrnamentSpec -> Attrs";
    };

    validateSpec = api.leaf {
      value = base: spec:
        H.validateOrnament base spec;
      description = "validateSpec: total predicate `{ ok, diagnostics }` over an `(base, spec)` candidate for the user-facing `ornament` surface — never throws.";
      signature = "validateSpec : DataSpec -> OrnamentSpec -> { ok : Bool, diagnostics : [Diagnostic] }";
    };

    tryOrnament = api.leaf {
      value = base: spec:
        H.tryOrnament base spec;
      description = "tryOrnament: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the built ornamented datatype when valid, otherwise diagnostics-only.";
      signature = "tryOrnament : DataSpec -> OrnamentSpec -> { ok : Bool, diagnostics : [Diagnostic], value? : Datatype }";
    };

    diagnoseSpec = api.leaf {
      value = base: spec:
        H.ornamentDiagnostics base spec;
      description = "diagnoseSpec: human-readable diagnostic strings for a candidate `(base, spec)` — derived from `H.ornamentDiagnostics`, suitable for error messages and tests.";
      signature = "diagnoseSpec : DataSpec -> OrnamentSpec -> [String]";
    };

    validateAlgOrn = api.leaf {
      value = args:
        H.validateAlgOrn args;
      description = "validateAlgOrn: total predicate `{ ok, diagnostics }` over candidate `algOrn` args — checks each algebra arm against its description shape without throwing.";
      signature = "validateAlgOrn : Attrs -> { ok : Bool, diagnostics : [Diagnostic] }";
    };

    tryAlgOrn = api.leaf {
      value = args:
        H.tryAlgOrn args;
      description = "tryAlgOrn: total constructor — returns `{ ok, diagnostics, value? }` where `value` is the algebraic ornament when valid, otherwise diagnostics-only.";
      signature = "tryAlgOrn : Attrs -> { ok : Bool, diagnostics : [Diagnostic], value? : Ornament }";
    };

    diagnoseAlgOrn = api.leaf {
      value = args:
        H.algOrnDiagnostics args;
      description = "diagnoseAlgOrn: human-readable diagnostic strings for a candidate algebraic-ornament spec — derived from `H.algOrnDiagnostics`, suitable for error messages and tests.";
      signature = "diagnoseAlgOrn : Attrs -> [String]";
    };

    lift = api.leaf {
      value = {
        list = liftList;
        attrs = liftAttrs;
        maybe = liftMaybe;
        field = liftField;
      };
      description = "lift: functorial container lifts — given an ornament `O : Ornament A A'`, `lift.list` / `lift.attrs` / `lift.maybe` produce `Ornament (F A) (F A')` whose forget is the standard functorial action of `F` on `O.forget`; `lift.field name O` is the elementary product-component move. Inputs may be leaf or decorated μ-ornaments; the μ-case delegates element forget to the meta walker.";
      signature = "lift : { list : Ornament -> Ornament, attrs : Ornament -> Ornament, maybe : Ornament -> Ornament, field : String -> Ornament -> Ornament }";
    };

    # Internal evaluator entry points exposed so tests can pin
    # which side of the dispatch they are exercising. The public
    # `forget` above is the only supported user-facing entry.
    _internal = {
      forgetHoas = forgetHoasApplied;
      forgetMeta = forgetMetaImpl;
    };
  };

  tests = {
    "ornaments-derive-descriptor-small" = {
      expr =
        let
          Box = H.datatype "GenericOrnBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
        in
        (self.deriveDescriptor Tagged).constructors;
      expected = [
        {
          name = "box";
          index = 0;
          targetIndex = true;
          fields = [
            {
              name = "tag";
              kind = "data";
              index = 0;
              level = 0;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = false;
              branchIndex = false;
              dependentType = false;
              type = { kind = "bool"; };
            }
            {
              name = "value";
              kind = "data";
              index = 1;
              level = 0;
              role = null;
              source = null;
              proof = false;
              recursiveIndex = false;
              branchIndex = false;
              dependentType = false;
              type = { kind = "nat"; };
            }
          ];
        }
      ];
    };

    "ornaments-forget-small-checks" = {
      expr =
        let
          Box = H.datatype "GenericOrnForgetBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericForgetTaggedBox";
            constructors.box.fields = [
              { keep = "value"; }
              { insert = "tag"; type = H.bool; }
            ];
          };
          value = H.app (H.app Tagged.box H.zero) H.true_;
        in
          !((H.checkHoas Box.T (self.forget Tagged value)) ? error);
      expected = true;
    };

    "ornaments-indexed-sugar-forget-checks" = {
      expr =
        let
          Base = H.datatype "GenericOrnListNatBase" [
            (H.con "nil" [ ])
            (H.con "cons" [
              (H.field "head" H.nat)
              (H.recField "tail")
            ])
          ];
          erase =
            H.ann
              (H.lam "_" H.nat (_: H.tt))
              (H.forall "_" H.nat (_: H.unit));
          Vec = self.ornament Base {
            name = "GenericOrnVecFromList";
            index = {
              J = H.nat;
              inherit erase;
            };
            constructors.nil = {
              target = _: H.zero;
              fields = [ ];
            };
            constructors.cons = {
              target = prev: H.succ prev.n;
              fields = [
                { insert = "n"; type = H.nat; }
                { keep = "head"; }
                { keep = "tail"; index = prev: prev.n; }
              ];
            };
          };
          nil = Vec.nil;
          cons = H.app (H.app (H.app Vec.cons H.zero) H.zero) nil;
          forgot = H.app (H.app Vec.forget (H.succ H.zero)) cons;
        in
          !((H.checkHoas (HI.muI H.unit Base.D H.tt) forgot) ? error);
      expected = true;
    };

    "ornaments-pullback-small-checks" = {
      expr =
        let
          Box = H.datatype "GenericOrnPullbackBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericPullbackTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
          value = H.app (H.app Tagged.box H.true_) H.zero;
          baseFn = H.ann
            (H.lam "x" Box.T (_: H.true_))
            (H.forall "_" Box.T (_: H.bool));
        in
          !((H.checkHoas H.bool (self.pullback Tagged baseFn value)) ? error);
      expected = true;
    };

    "ornaments-pullbackHoas-small-checks" = {
      expr =
        let
          Box = H.datatype "GenericOrnPullbackHoasBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericPullbackHoasTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
          value = H.app (H.app Tagged.box H.true_) H.zero;
          baseFn = H.ann
            (H.lam "i" H.unit (i:
              H.lam "_" (HI.muI H.unit Box.D i) (_: H.true_)))
            (H.forall "i" H.unit (i:
              H.forall "_" (HI.muI H.unit Box.D i) (_: H.bool)));
          pulled = self.pullbackHoas Tagged (_: H.bool) baseFn;
        in
          !((H.checkHoas H.bool (H.app (H.app pulled H.tt) value)) ? error);
      expected = true;
    };

    "ornaments-liftFold-small-checks" = {
      expr =
        let
          Box = H.datatype "GenericOrnLiftFoldBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericLiftFoldTaggedBox";
            constructors.box.fields = [
              { keep = "value"; }
              { insert = "tag"; type = H.bool; }
            ];
          };
          value = H.app (H.app Tagged.box H.zero) H.false_;
          baseFold = H.ann
            (H.lam "i" H.unit (i:
              H.lam "_" (HI.muI H.unit Box.D i) (_: H.true_)))
            (H.forall "i" H.unit (i:
              H.forall "_" (HI.muI H.unit Box.D i) (_: H.bool)));
          lifted = self.liftFold Tagged (_: H.bool) baseFold;
        in
          !((H.checkHoas H.bool (H.app (H.app lifted H.tt) value)) ? error);
      expected = true;
    };

    "ornaments-functional-build-small-checks" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericFunctionalTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
          baseValue = H.app Box.box H.zero;
          F = self.functional {
            ornament = Tagged;
            chooseIndex = i: _x: i;
            indexProof = _i: _x: H.bootRefl;
            section = _i: _x:
              H.app (H.app Tagged.box H.true_) H.zero;
          };
          built = self.functionalBuild F baseValue;
          forgot = self.forget Tagged built;
        in
          !((H.checkHoas Box.T forgot) ? error);
      expected = true;
    };

    "ornaments-functional-synthesis-missing-builder-diagnostic" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalSynthMissingBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          result = self.validateFunctional {
            base = Box;
            spec = {
              name = "GenericFunctionalSynthMissingTaggedBox";
              constructors.box.fields = [
                { insert = "tag"; type = H.bool; }
                { keep = "value"; }
              ];
            };
            synth = { };
          };
          diagnostic = builtins.head result.diagnostics;
        in
        {
          inherit (result) ok;
          inherit (diagnostic) code severity path message;
        };
      expected = {
        ok = false;
        code = "functional.missing-builder";
        severity = "error";
        path = [ "functional" "constructors" "box" "fields" "tag" ];
        message = "inserted field needs builder";
      };
    };

    "ornaments-functional-synthesis-builds-inserted-field" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalSynthBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          spec = {
            name = "GenericFunctionalSynthTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
          F = self.functional {
            base = Box;
            inherit spec;
            synth.constructors.box.fields.tag = _ctx: true;
          };
          baseValue = H.app Box.box H.zero;
          built = self.functionalBuild F baseValue;
          forgot = self.forget F.meta.ornamented built;
        in
        self.view Box.T forgot;
      expected = { _con = "box"; value = 0; };
    };

    "ornaments-functional-synthesis-unresolved-proof-obligation" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalSynthProofMissingBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          result = self.validateFunctional {
            base = Box;
            spec = {
              name = "GenericFunctionalSynthProofMissingTaggedBox";
              constructors.box.fields = [
                { keep = "value"; }
                { insert = "valid"; type = H.unit; proof = true; }
              ];
            };
            synth = { };
          };
          diagnostic = builtins.head result.diagnostics;
          obligation = builtins.head result.obligations;
        in
        {
          inherit (result) ok;
          diagnostic = {
            inherit (diagnostic) code severity path message;
          };
          obligation = {
            inherit (obligation) code path kind field;
          };
        };
      expected = {
        ok = false;
        diagnostic = {
          code = "functional.unresolved-proof";
          severity = "error";
          path = [ "functional" "constructors" "box" "proofs" "valid" ];
          message = "proof field needs builder";
        };
        obligation = {
          code = "functional.unresolved-proof";
          path = [ "functional" "constructors" "box" "proofs" "valid" ];
          kind = "proof";
          field = "valid";
        };
      };
    };

    "ornaments-functional-synthesis-builds-proof-field" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalSynthProofBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          spec = {
            name = "GenericFunctionalSynthProofTaggedBox";
            constructors.box.fields = [
              { keep = "value"; }
              { insert = "valid"; type = H.unit; proof = true; }
            ];
          };
          F = self.functional {
            base = Box;
            inherit spec;
            synth.constructors.box.proofs.valid = _ctx: null;
          };
          baseValue = H.app Box.box H.zero;
          built = self.functionalBuild F baseValue;
          forgot = self.forget F.meta.ornamented built;
        in
        self.view Box.T forgot;
      expected = { _con = "box"; value = 0; };
    };

    "ornaments-functional-compose-synthesis" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalComposeBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          F1 = self.functional {
            base = Box;
            spec = {
              name = "GenericFunctionalComposeTaggedBox";
              constructors.box.fields = [
                { insert = "tag"; type = H.bool; }
                { keep = "value"; }
              ];
            };
            synth.constructors.box.fields.tag = _ctx: true;
          };
          F2 = self.functional {
            base = F1.meta.ornamented;
            spec = {
              name = "GenericFunctionalComposeLabeledBox";
              constructors.box.fields = [
                { insert = "label"; type = H.string; }
                { keep = "tag"; }
                { keep = "value"; }
              ];
            };
            synth.constructors.box.fields.label = _ctx: "tool";
          };
          F = self.composeFunctional F2 F1;
          baseValue = H.app Box.box H.zero;
          built = self.functionalBuild F baseValue;
          forgot = self.forget F built;
        in
        self.view Box.T forgot;
      expected = { _con = "box"; value = 0; };
    };

    "ornaments-functional-liftProducer-canonicalizes-output" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalLiftProducerBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          F = self.functional {
            base = Box;
            spec = {
              name = "GenericFunctionalLiftProducerTaggedBox";
              constructors.box.fields = [
                { insert = "tag"; type = H.bool; }
                { keep = "value"; }
              ];
            };
            synth.constructors.box.fields.tag = _ctx: true;
          };
          baseFn =
            H.ann
              (H.lam "x" Box.T (_: H.app Box.box H.zero))
              (H.forall "_" Box.T (_: Box.T));
          baseInput = H.app Box.box (H.succ H.zero);
          built = self.liftProducer F baseFn baseInput;
        in
        self.view F.meta.ornamented.T built;
      expected = { _con = "box"; tag = true; value = 0; };
    };

    "ornaments-functional-liftTransform-canonicalizes-output" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalLiftTransformBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericFunctionalLiftTransformTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
          Labeled = self.functional {
            base = Box;
            spec = {
              name = "GenericFunctionalLiftTransformLabeledBox";
              constructors.box.fields = [
                { insert = "label"; type = H.string; }
                { keep = "value"; }
              ];
            };
            synth.constructors.box.fields.label = _ctx: "tool";
          };
          baseFn =
            H.ann
              (H.lam "x" Box.T (x: x))
              (H.forall "_" Box.T (_: Box.T));
          taggedInput = H.app (H.app Tagged.box H.false_) H.zero;
          built = self.liftTransform
            {
              input = Tagged;
              output = Labeled;
              fn = baseFn;
            }
            taggedInput;
        in
        self.view Labeled.meta.ornamented.T built;
      expected = { _con = "box"; label = "tool"; value = 0; };
    };

    "ornaments-functional-metabuilder-pilot-chain" = {
      expr =
        let
          CoreBuilder = H.datatype "GenericFunctionalMetaCoreBuilder" [
            (H.con "builder" [
              ((H.field "name" H.nat) // {
                role = "dependency";
                source = { path = "builder.name"; };
              })
              (H.field "actionCount" H.nat)
            ])
          ];
          CodeGenBuilder = self.functional {
            base = CoreBuilder;
            spec = {
              name = "GenericFunctionalMetaCodeGenBuilder";
              constructors.builder.fields = [
                { insert = "language"; type = H.nat; }
                { keep = "name"; }
                { keep = "actionCount"; }
              ];
            };
            synth.constructors.builder.fields.language = _ctx: 2;
          };
          IdlBuilder = self.functional {
            base = CodeGenBuilder.meta.ornamented;
            spec = {
              name = "GenericFunctionalMetaIdlBuilder";
              constructors.builder.fields = [
                { insert = "idlVersion"; type = H.nat; }
                { keep = "language"; }
                { keep = "name"; }
                { keep = "actionCount"; }
              ];
            };
            synth.constructors.builder.fields.idlVersion = _ctx: 1;
          };
          IdlChain = self.composeFunctional IdlBuilder CodeGenBuilder;
          coreRecord = {
            _con = "builder";
            name = 3;
            actionCount = 5;
          };
          coreValue = self.review CoreBuilder.T coreRecord;
          codeValue = self.functionalBuild CodeGenBuilder coreValue;
          idlValue = self.functionalBuild IdlChain coreValue;
          baseProducer =
            H.ann
              (H.lam "builder" CoreBuilder.T (_:
                self.review CoreBuilder.T {
                  _con = "builder";
                  name = 8;
                  actionCount = 13;
                }))
              (H.forall "_" CoreBuilder.T (_: CoreBuilder.T));
          liftedValue = self.liftProducer IdlChain baseProducer coreValue;
          missingLanguage = self.validateFunctional {
            base = CoreBuilder;
            spec = {
              name = "GenericFunctionalMetaMissingCodeGenBuilder";
              constructors.builder.fields = [
                { insert = "language"; type = H.nat; }
                { keep = "name"; }
                { keep = "actionCount"; }
              ];
            };
            synth = { };
          };
          diagnostic = builtins.head missingLanguage.diagnostics;
        in
        {
          code = self.view CodeGenBuilder.meta.ornamented.T codeValue;
          idl = self.view IdlBuilder.meta.ornamented.T idlValue;
          forgot =
            self.view CoreBuilder.T
              (self.forget IdlChain idlValue);
          lifted =
            self.view IdlBuilder.meta.ornamented.T liftedValue;
          liftedForgot =
            self.view CoreBuilder.T
              (self.forget IdlChain liftedValue);
          diagnostic = {
            inherit (diagnostic) code path message;
          };
        };
      expected = {
        code = {
          _con = "builder";
          language = 2;
          name = 3;
          actionCount = 5;
        };
        idl = {
          _con = "builder";
          idlVersion = 1;
          language = 2;
          name = 3;
          actionCount = 5;
        };
        forgot = {
          _con = "builder";
          name = 3;
          actionCount = 5;
        };
        lifted = {
          _con = "builder";
          idlVersion = 1;
          language = 2;
          name = 8;
          actionCount = 13;
        };
        liftedForgot = {
          _con = "builder";
          name = 8;
          actionCount = 13;
        };
        diagnostic = {
          code = "functional.missing-builder";
          path = [ "functional" "constructors" "builder" "fields" "language" ];
          message = "inserted field needs builder";
        };
      };
    };

    "ornaments-functional-algebraic-measure-builds-field" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalMeasureBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          F = self.functional {
            base = Box;
            spec = {
              name = "GenericFunctionalMeasuredBox";
              constructors.box.fields = [
                { insert = "measure"; type = H.nat; measure = "valueMeasure"; }
                { keep = "value"; }
              ];
            };
            measures.valueMeasure = ctx: ctx.baseRecord.value;
          };
          baseValue = H.app Box.box (H.succ H.zero);
          built = self.functionalBuild F baseValue;
        in
        self.view F.meta.ornamented.T built;
      expected = { _con = "box"; measure = 1; value = 1; };
    };

    "ornaments-functional-algebraic-measure-missing-diagnostic" = {
      expr =
        let
          Box = H.datatype "GenericFunctionalMissingMeasureBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          result = self.validateFunctional {
            base = Box;
            spec = {
              name = "GenericFunctionalMissingMeasureBox";
              constructors.box.fields = [
                { insert = "measure"; type = H.nat; measure = "valueMeasure"; }
                { keep = "value"; }
              ];
            };
            synth = { };
          };
          diagnostic = builtins.head result.diagnostics;
          obligation = builtins.head result.obligations;
        in
        {
          inherit (result) ok;
          diagnostic = {
            inherit (diagnostic) code severity path message;
          };
          obligation = {
            inherit (obligation) code path kind field measure;
          };
        };
      expected = {
        ok = false;
        diagnostic = {
          code = "functional.missing-measure";
          severity = "error";
          path = [ "functional" "constructors" "box" "fields" "measure" "measure" ];
          message = "measure field needs declared measure";
        };
        obligation = {
          code = "functional.missing-measure";
          path = [ "functional" "constructors" "box" "fields" "measure" "measure" ];
          kind = "measure";
          field = "measure";
          measure = "valueMeasure";
        };
      };
    };

    "ornaments-algOrn-builder-summary-checks" = {
      expr =
        let
          baseD = H.descArg H.unit 0 H.nat (_: H.descRet);
          erase =
            H.ann
              (H.lam "_" H.nat (_: H.tt))
              (H.forall "_" H.nat (_: H.unit));
          O = self.algOrn {
            I = H.unit;
            J = H.nat;
            inherit erase;
            D = baseD;
            algebra = H.algArg (count: H.algRet count);
          };
          D = H.ornDesc O;
          forgetTy =
            H.forall "n" H.nat (n:
              H.forall "_" (HI.muI H.nat D n) (_:
                HI.muI H.unit baseD H.tt));
        in
          !((H.checkHoas forgetTy (self.forgetHoas O)) ? error);
      expected = true;
    };

    "ornaments-generic-fold-builder-summary" = {
      expr =
        let
          Builder = H.datatype "GenericBuilderSummary" [
            (H.con "builder" [
              (H.field "actionCount" H.nat)
            ])
          ];
        in
        self.fold Builder.T
          {
            builder = fields: fields.actionCount;
          }
          {
            _con = "builder";
            actionCount = 3;
          };
      expected = 3;
    };

    "ornaments-alg-shape-builder-fold-checked" = {
      expr =
        let
          D = H.descArg H.unit 0 H.nat (_: H.descRet);
          algebra = H.algArg (count: H.algRet count);
        in
        {
          supported = self.algSupportedFragment;
          desc = self.shape D;
          alg = self.algShape algebra;
          checked = (self.checkAlgShape { inherit D algebra; }).tag;
        };
      expected = {
        supported = [ "ret" "arg" "rec" "pi" "plus" ];
        desc = { kind = "arg"; body = { kind = "ret"; }; };
        alg = { kind = "arg"; body = { kind = "ret"; }; };
        checked = "arg";
      };
    };

    "ornaments-alg-shape-diagnostics-nested-mismatch" = {
      expr =
        let
          D = H.descArg H.unit 0 H.nat (_: H.descRec H.descRet);
          algebra = H.algArg (_:
            H.algRec (_:
              H.algArg (x: H.algRet x)));
        in
        builtins.elem
          "generic.ornaments.algShape: path root.arg.rec: desc node descRet expects algebra node 'ret', got 'arg'"
          (self.algShapeDiagnostics { inherit D algebra; });
      expected = true;
    };

    "ornaments-alg-shape-pi-keep-checked" = {
      expr =
        let
          D = H.descPi 0 H.void H.descRet;
          algebra = H.algPiKeep
            {
              branchIndex = x: H.absurd H.nat x;
            }
            (H.algRet H.zero);
        in
        {
          desc = self.shape D;
          alg = self.algShape algebra;
          checked = (self.checkAlgShape { inherit D algebra; }).tag;
        };
      expected = {
        desc = { kind = "pi"; sub = { kind = "ret"; }; };
        alg = { kind = "pi"; sub = { kind = "ret"; }; };
        checked = "pi";
      };
    };

    "ornaments-alg-shape-diagnostics-pi-implicit-aggregation" = {
      expr =
        let
          D = H.descPi 0 H.void H.descRet;
          algebra = H.algRet H.zero;
        in
        builtins.elem
          "generic.ornaments.algShape: path root: desc node descPi expects algebra node 'pi', got 'ret'"
          (self.algShapeDiagnostics { inherit D algebra; });
      expected = true;
    };

    "ornaments-algOrn-pi-keep-public-checked" = {
      expr =
        let
          D = H.descPi 0 H.void H.descRet;
          erase =
            H.ann
              (H.lam "_" H.nat (_: H.tt))
              (H.forall "_" H.nat (_: H.unit));
          O = self.algOrn {
            I = H.unit;
            J = H.nat;
            inherit erase D;
            algebra = H.algPiKeep
              {
                branchIndex = x: H.absurd H.nat x;
              }
              (H.algRet H.zero);
          };
          OD = H.ornDesc O;
          forgetTy =
            H.forall "n" H.nat (n:
              H.forall "_" (HI.muI H.nat OD n) (_:
                HI.muI H.unit D H.tt));
        in
          !((H.checkHoas forgetTy (self.forgetHoas O)) ? error);
      expected = true;
    };

    "ornaments-algOrn-list-to-vec-public-checked" = {
      expr =
        let
          listNatD =
            H.plus H.descRet
              (H.descArg H.unit 0 H.nat (_:
                H.descRec H.descRet));
          listNatLengthAlg =
            H.algPlus
              (H.algRet H.zero)
              (H.algArg (_x:
                H.algRec (n:
                  H.algRet (H.succ n))));
          erase =
            H.ann
              (H.lam "_" H.nat (_: H.tt))
              (H.forall "_" H.nat (_: H.unit));
          O = self.algOrn {
            I = H.unit;
            J = H.nat;
            inherit erase;
            D = listNatD;
            algebra = listNatLengthAlg;
          };
          D = H.ornDesc O;
          forgetTy =
            H.forall "n" H.nat (n:
              H.forall "_" (HI.muI H.nat D n) (_:
                HI.muI H.unit listNatD H.tt));
        in
          !((H.checkHoas forgetTy (self.forgetHoas O)) ? error);
      expected = true;
    };

    "ornaments-derive-schema-small" = {
      expr =
        let
          Box = H.datatype "GenericSchemaBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          Tagged = self.ornament Box {
            name = "GenericSchemaTaggedBox";
            constructors.box.fields = [
              { insert = "tag"; type = H.bool; }
              { keep = "value"; }
            ];
          };
        in
        self.deriveSchema Tagged;
      expected = {
        title = "GenericSchemaTaggedBox";
        oneOf = [
          {
            type = "object";
            additionalProperties = false;
            required = [ "_con" "tag" "value" ];
            properties = {
              _con = { const = "box"; };
              tag = { type = "boolean"; };
              value = { type = "integer"; };
            };
          }
        ];
      };
    };

    "ornaments-checkSpec-rejects-unknown-field" = {
      expr =
        let
          Box = H.datatype "GenericOrnRejectBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        (builtins.tryEval (self.checkSpec Box {
          name = "BadTaggedBox";
          constructors.box.fields = [
            { keep = "missing"; }
          ];
        })).success;
      expected = false;
    };

    "ornaments-checkSpec-rejects-duplicate-output-field" = {
      expr =
        let
          Box = H.datatype "GenericOrnRejectDuplicateBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        (builtins.tryEval (self.checkSpec Box {
          name = "BadDuplicateTaggedBox";
          constructors.box.fields = [
            { insert = "value"; type = H.bool; }
            { keep = "value"; }
          ];
        })).success;
      expected = false;
    };

    "ornaments-validateSpec-structured" = {
      expr =
        let
          Box = H.datatype "GenericOrnValidateBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          result = self.validateSpec Box {
            name = "GenericBadStructuredDiag";
            constructors.box.fields = [{ keep = "missing"; }];
          };
          diagnostic = builtins.head result.diagnostics;
        in
        {
          inherit (result) ok;
          inherit (diagnostic) code severity path message;
        };
      expected = {
        ok = false;
        code = "ornament.unknown-field";
        severity = "error";
        path = [
          "datatype:GenericOrnValidateBoxBase"
          "ornament:GenericBadStructuredDiag"
          "constructor:box"
          "field:missing"
        ];
        message = "unknown kept base field";
      };
    };

    "ornaments-tryOrnament-invalid-is-total" = {
      expr =
        let
          Box = H.datatype "GenericOrnTryBadBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
          result = self.tryOrnament Box {
            name = "GenericBadTryOrnament";
            constructors.box.fields = [{ keep = "missing"; }];
          };
        in
        {
          inherit (result) ok;
          hasValue = result ? value;
          diagnostics = builtins.length result.diagnostics;
        };
      expected = {
        ok = false;
        hasValue = false;
        diagnostics = 2;
      };
    };

    "ornaments-validateAlgOrn-structured" = {
      expr =
        let
          D = H.descArg H.unit 0 H.nat (_: H.descRet);
          erase =
            H.ann
              (H.lam "_" H.nat (_: H.tt))
              (H.forall "_" H.nat (_: H.unit));
          result = self.validateAlgOrn {
            I = H.unit;
            J = H.nat;
            inherit erase D;
            algebra = H.algRet H.zero;
          };
          diagnostic = builtins.head result.diagnostics;
        in
        {
          inherit (result) ok;
          inherit (diagnostic) code severity path message;
        };
      expected = {
        ok = false;
        code = "algOrn.shape-mismatch";
        severity = "error";
        path = "root";
        message = "expected arg algebra for descArg, got ret";
      };
    };

    "ornaments-diagnoseSpec-context" = {
      expr =
        let
          Box = H.datatype "GenericOrnDiagnoseBoxBase" [
            (H.con "box" [ (H.field "value" H.nat) ])
          ];
        in
        builtins.elem
          "hoas.ornament: datatype 'GenericOrnDiagnoseBoxBase' ornament 'GenericBadDiag' constructor 'box' field 'missing': unknown kept base field"
          (self.diagnoseSpec Box {
            name = "GenericBadDiag";
            constructors.box.fields = [{ keep = "missing"; }];
          });
      expected = true;
    };

    "lift-list-forget-maps-elementwise" = {
      expr =
        let
          drvA = { type = "derivation"; name = "a"; outPath = "/nix/store/a"; };
          drvB = { type = "derivation"; name = "b"; outPath = "/nix/store/b"; };
          tOrn = H.thunkOrnament H.derivation;
          lifted = self.lift.list tOrn;
          xs = [ (tOrn.section drvA) (tOrn.section drvB) ];
        in
        map (d: d.outPath) (lifted.forget xs);
      expected = [ "/nix/store/a" "/nix/store/b" ];
    };

    "lift-list-empty" = {
      expr = (self.lift.list (H.thunkOrnament H.derivation)).forget [ ];
      expected = [ ];
    };

    "lift-field-forget-rewrites-named-field" = {
      expr =
        let
          drv = { type = "derivation"; name = "x"; outPath = "/nix/store/x"; };
          tOrn = H.thunkOrnament H.derivation;
          lifted = self.lift.field "derivation" tOrn;
          record = { kind = "s"; derivation = tOrn.section drv; };
          out = lifted.forget record;
        in
        { kind = out.kind; outPath = out.derivation.outPath; };
      expected = { kind = "s"; outPath = "/nix/store/x"; };
    };

    "lift-list-composes-with-lift-field" = {
      expr =
        let
          drvA = { type = "derivation"; name = "a"; outPath = "/nix/store/a"; };
          drvB = { type = "derivation"; name = "b"; outPath = "/nix/store/b"; };
          tOrn = H.thunkOrnament H.derivation;
          fieldOrn = self.lift.field "derivation" tOrn;
          listed = self.lift.list fieldOrn;
          xs = [
            { kind = "s"; name = "a"; derivation = tOrn.section drvA; }
            { kind = "s"; name = "b"; derivation = tOrn.section drvB; }
          ];
        in
        map (r: { n = r.name; p = r.derivation.outPath; }) (listed.forget xs);
      expected = [
        { n = "a"; p = "/nix/store/a"; }
        { n = "b"; p = "/nix/store/b"; }
      ];
    };

    # `lift.list` over a decorated μ-ornament delegates element forget
    # to the meta walker via `forgetMetaImpl`. The forward type is the
    # ornamented datatype's `.T`; section throws on call because the
    # kernel does not expose a Nix-meta μ-section.
    "lift-list-over-mu-ornament" = {
      expr =
        let
          drvA = { type = "derivation"; name = "a"; outPath = "/nix/store/a"; };
          tOrn = H.thunkOrnament H.derivation;
          Box = H.datatype "GenericOrnLiftListMuBoxBase" [
            (H.con "box" [ (H.field "derivation" H.derivation) ])
          ];
          BoxForget = self.ornament Box {
            name = "GenericOrnLiftListMuBoxForget";
            constructors.box.fields = [
              { keep = "derivation"; sub = tOrn; }
            ];
          };
          listed = self.lift.list BoxForget;
          xs = [{ _con = "box"; derivation = tOrn.section drvA; }];
        in
        map (r: { c = r._con; p = r.derivation.outPath; }) (listed.forget xs);
      expected = [{ c = "box"; p = "/nix/store/a"; }];
    };

    "keepSub-forget-applies-sub" = {
      expr =
        let
          idLeafStr = H.leafOrnament {
            primitive = H.string;
            forget = x: x;
            section = x: x;
            meta = { name = "IdString"; inner = H.string; };
          };
          Box = H.datatype "GenericOrnKeepSubBoxBase" [
            (H.con "box" [ (H.field "value" H.string) ])
          ];
          TaggedBox = self.ornament Box {
            name = "GenericOrnKeepSubTaggedBox";
            constructors.box.fields = [
              { keep = "value"; sub = idLeafStr; }
              { insert = "tag"; type = H.bool; }
            ];
          };
        in
        self.forget TaggedBox { _con = "box"; value = "hi"; tag = true; };
      expected = { _con = "box"; value = "hi"; };
    };

    "keepSub-with-thunkOrnament-forces-field" = {
      expr =
        let
          tOrn = H.thunkOrnament H.string;
          Box = H.datatype "GenericOrnKeepSubThunkBoxBase" [
            (H.con "box" [ (H.field "value" H.string) ])
          ];
          ThunkBox = self.ornament Box {
            name = "GenericOrnKeepSubThunkBox";
            constructors.box.fields = [
              { keep = "value"; sub = tOrn; }
            ];
          };
          state = { _con = "box"; value = tOrn.section "hello"; };
        in
        self.forget ThunkBox state;
      expected = { _con = "box"; value = "hello"; };
    };

    "keepSub-with-lift-list-thunkOrn-maps-forceThunk" = {
      expr =
        let
          drvA = { type = "derivation"; name = "a"; outPath = "/nix/store/a"; };
          drvB = { type = "derivation"; name = "b"; outPath = "/nix/store/b"; };
          tOrn = H.thunkOrnament H.derivation;
          listOrn = self.lift.list tOrn;
          Box = H.datatype "GenericOrnKeepSubListBoxBase" [
            (H.con "box" [ (H.field "paths" (H.listOf H.derivation)) ])
          ];
          ListBox = self.ornament Box {
            name = "GenericOrnKeepSubListBox";
            constructors.box.fields = [
              { keep = "paths"; sub = listOrn; }
            ];
          };
          state = {
            _con = "box";
            paths = [ (tOrn.section drvA) (tOrn.section drvB) ];
          };
          out = self.forget ListBox state;
        in
        {
          _con = out._con;
          paths = map (d: d.outPath) out.paths;
        };
      expected = {
        _con = "box";
        paths = [ "/nix/store/a" "/nix/store/b" ];
      };
    };

    "keepSub-rejects-incompatible-sub-type" = {
      expr =
        let
          Box = H.datatype "GenericOrnKeepSubMismatchBoxBase" [
            (H.con "box" [ (H.field "value" H.derivation) ])
          ];
          mismatchedSub = H.thunkOrnament H.string;
        in
        builtins.elem
          "hoas.ornament: datatype 'GenericOrnKeepSubMismatchBoxBase' ornament 'GenericOrnKeepSubMismatchBox' constructor 'box' field 'value': sub-ornament base type 'string' disagrees with kept field type 'derivation'"
          (self.diagnoseSpec Box {
            name = "GenericOrnKeepSubMismatchBox";
            constructors.box.fields = [
              { keep = "value"; sub = mismatchedSub; }
            ];
          });
      expected = true;
    };

    "forgetMeta-drops-inserts" = {
      expr =
        let
          idLeafStr = H.leafOrnament {
            primitive = H.string;
            forget = x: x;
            section = x: x;
            meta = { name = "IdString"; inner = H.string; };
          };
          Box = H.datatype "GenericOrnForgetMetaBoxBase" [
            (H.con "box" [ (H.field "value" H.string) ])
          ];
          TaggedBox = self.ornament Box {
            name = "GenericOrnForgetMetaTaggedBox";
            constructors.box.fields = [
              { keep = "value"; sub = idLeafStr; }
              { insert = "tag"; type = H.bool; }
              { insert = "note"; type = H.string; }
            ];
          };
        in
        self._internal.forgetMeta TaggedBox {
          _con = "box";
          value = "kept";
          tag = false;
          note = "ignored";
        };
      expected = { _con = "box"; value = "kept"; };
    };

    "forget-dispatches-on-_htag-vs-_con" = {
      expr =
        let
          idLeafStr = H.leafOrnament {
            primitive = H.string;
            forget = x: x;
            section = x: x;
            meta = { name = "IdString"; inner = H.string; };
          };
          Box = H.datatype "GenericOrnDispatchBoxBase" [
            (H.con "box" [ (H.field "value" H.string) ])
          ];
          TaggedBox = self.ornament Box {
            name = "GenericOrnDispatchTaggedBox";
            constructors.box.fields = [
              { keep = "value"; sub = idLeafStr; }
              { insert = "tag"; type = H.bool; }
            ];
          };
          metaResult = self.forget TaggedBox {
            _con = "box";
            value = "v";
            tag = true;
          };
          nonAttrs = builtins.tryEval (self.forget TaggedBox "scalar");
          neither = builtins.tryEval (self.forget TaggedBox { other = 1; });
          both = builtins.tryEval (self.forget TaggedBox {
            _htag = "x";
            _con = "box";
            value = "v";
          });
        in
        {
          meta = metaResult;
          nonAttrsOk = nonAttrs.success;
          neitherOk = neither.success;
          bothOk = both.success;
        };
      expected = {
        meta = { _con = "box"; value = "v"; };
        nonAttrsOk = false;
        neitherOk = false;
        bothOk = false;
      };
    };

    "forget-meta-hoas-commute" = {
      expr =
        let
          idLeafStr = H.leafOrnament {
            primitive = H.string;
            forget = x: x;
            section = x: x;
            meta = { name = "IdString"; inner = H.string; };
          };
          Box = H.datatype "GenericOrnCommuteBoxBase" [
            (H.con "box" [ (H.field "value" H.string) ])
          ];
          TaggedBox = self.ornament Box {
            name = "GenericOrnCommuteTaggedBox";
            constructors.box.fields = [
              { keep = "value"; sub = idLeafStr; }
              { insert = "tag"; type = H.bool; }
            ];
          };
          metaInput = { _con = "box"; value = "z"; tag = false; };
          viaMeta = self._internal.forgetMeta TaggedBox metaInput;
          viaPublic = self.forget TaggedBox metaInput;
        in
        viaMeta == viaPublic;
      expected = true;
    };
  };

}
