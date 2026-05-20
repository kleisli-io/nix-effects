{ fx, api, ... }:

let
  M = fx.tc.elaborate.meta;
  C = fx.tc.check;
  V = fx.tc.value;

  positionOf = meta:
    if meta ? _surfacePosition then meta._surfacePosition
    else if meta ? type && meta.type ? surface && meta.type.surface ? position
    then meta.type.surface.position
    else null;

  metaRecord = meta: {
    id = meta.id or null;
    type = meta.type or null;
    position = positionOf meta;
  };

  collectSurfaceMetas = term:
    if builtins.isAttrs term && (term.tag or null) == "meta"
    then [ (metaRecord term) ]
    else term._surfaceMetas or [ ];

  collectImplicitMetas = term:
    if builtins.isAttrs term && (term._surfaceImplicit or false) == true
    then [ (metaRecord term) ]
    else term._surfaceImplicitMetas or [ ];

  unsolvedStateMetas = state:
    if state == null then [ ]
    else
      let
        delta = state.delta or { };
        names = builtins.attrNames delta;
        holes = builtins.filter (name: (delta.${name}.tag or null) == "Hole") names;
      in
      map
        (name: {
          id = delta.${name}.id or null;
          type = delta.${name}.type or null;
          position =
            if delta.${name}.type ? surface && delta.${name}.type.surface ? position
            then delta.${name}.type.surface.position
            else null;
        })
        holes;

  uniqueById = metas:
    let
      step = acc: meta:
        let key = toString (meta.id or "__unknown_${toString (builtins.length acc.order)}");
        in if acc.seen ? ${key}
        then acc
        else {
          seen = acc.seen // { ${key} = true; };
          order = acc.order ++ [ meta ];
        };
    in
    (builtins.foldl' step { seen = { }; order = [ ]; } metas).order;

  firstPosition = fallback: metas:
    let positioned = builtins.filter (meta: meta.position != null) metas;
    in if positioned == [ ] then fallback else (builtins.head positioned).position;

  surfaceType = args:
    let
      base = args.type or { ctx = C.emptyCtx; ty = V.vUnit; };
      position = args.position or null;
    in
    base // {
      surface = (base.surface or { }) // {
        inherit position;
        label = args.label or null;
        surface = args.surface or null;
      };
    };

  implicitMeta = args:
    let
      state = args.state or M.emptyState;
      type = surfaceType args;
      alloc = M.freshMetaInState type state;
      term = (M.mkMeta alloc.meta.id [ ]) // {
        type = alloc.meta.type;
        _surfaceImplicit = true;
        _surfacePosition = args.position or null;
      };
    in
    {
      id = alloc.meta.id;
      value = alloc.meta;
      inherit term;
      state = alloc.state;
    };

  unsolvedImplicitError = args:
    let
      metas = uniqueById (args.metas or [ ]);
      position = firstPosition (args.position or null) metas;
    in
    {
      error = {
        msg = "unsolved implicit metavariable";
        kind = "surface.unsolved-implicit";
        inherit metas position;
        surface = args.surface or null;
        term = args.term or null;
      };
      msg = "unsolved implicit metavariable";
      kind = "surface.unsolved-implicit";
      inherit metas position;
    };

  annotateSurfaceError = args:
    let
      result = args.result;
      position = args.position or null;
      surface = args.surface or null;
      surfaceFields =
        (if position == null then { } else { inherit position; })
        // (if surface == null then { } else { inherit surface; });
      errorFields =
        if builtins.isAttrs result.error then {
          error = result.error // surfaceFields;
        } else { };
    in
    result // surfaceFields // errorFields;

  finalizeSurfaceElab = args:
    let
      result = args.result;
      metas = uniqueById
        (collectImplicitMetas result ++ unsolvedStateMetas (args.state or null));
    in
    if builtins.isAttrs result && result ? error then annotateSurfaceError args
    else if metas != [ ] then
      unsolvedImplicitError
        {
          inherit metas;
          term = args.term or null;
          surface = args.surface or null;
          position = args.position or null;
        }
    else result;
in
{
  scope = {
    collectImplicitMetas = api.leaf {
      value = collectImplicitMetas;
      description = "Collect surface-created implicit metavariable terms from an elaborated overlay term.";
      signature = "ElabTm -> [SurfaceMeta]";
    };
    collectSurfaceMetas = api.leaf {
      value = collectSurfaceMetas;
      description = "Collect explicitly marked overlay metavariable terms from an elaborated surface result.";
      signature = "ElabTm -> [SurfaceMeta]";
    };
    finalizeSurfaceElab = api.leaf {
      value = finalizeSurfaceElab;
      description = "Return a structured unsolved-implicit error when elaboration leaves surface implicit metas unresolved.";
      signature = "{ result, state?, term?, surface?, position? } -> ElabTm | Error";
    };
    implicitMeta = api.leaf {
      value = implicitMeta;
      description = "Allocate an implicit metavariable using the Phase 6 meta-context shape and return both overlay value and term forms.";
      signature = "{ type?, state?, position?, surface?, label? } -> { id, value, term, state }";
    };
    unsolvedImplicitError = api.leaf {
      value = unsolvedImplicitError;
      description = "Build the structured surface error for unresolved implicit metavariables.";
      signature = "{ metas, term?, surface?, position? } -> Error";
    };
    containsImplicitMeta = api.leaf {
      value = term: collectImplicitMetas term != [ ];
      description = "Predicate for unresolved surface-created implicit metavariable terms.";
      signature = "ElabTm -> Bool";
    };
    containsSurfaceMeta = api.leaf {
      value = term: collectSurfaceMetas term != [ ];
      description = "Predicate for any overlay metavariable term inside an elaborated surface result.";
      signature = "ElabTm -> Bool";
    };
  };

  tests = { };
}
