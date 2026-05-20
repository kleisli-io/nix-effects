{ api, ... }:

let
  tag = "nix-effects.surface.registry";

  empty = {
    _surfaceRegistryTag = tag;
    handlers = { };
  };

  isRegistry = registry:
    builtins.isAttrs registry
    && (let registryTag = registry._surfaceRegistryTag or null; in registryTag == tag)
    && builtins.isAttrs (registry.handlers or null);

  normalize = registry:
    if registry == null then empty
    else if isRegistry registry then registry
    else if builtins.isAttrs registry && builtins.isAttrs (registry.handlers or null)
    then empty // registry
    else throw "surface.registry: expected registry";

  checkTag = constructorTag:
    if builtins.isString constructorTag && constructorTag != ""
    then constructorTag
    else throw "surface.registry: constructor tag must be a non-empty string";

  register = registry: constructorTag: handler:
    let
      r = normalize registry;
      t = checkTag constructorTag;
    in
    r // { handlers = r.handlers // { ${t} = handler; }; };

  fromHandlers = handlers:
    builtins.foldl'
      (registry: constructorTag: register registry constructorTag handlers.${constructorTag})
      empty
      (builtins.attrNames handlers);

  lookup = registry: constructorTag:
    let
      r = normalize registry;
      t = checkTag constructorTag;
    in
      r.handlers.${t} or null;

  merge = lhs: rhs:
    let
      l = normalize lhs;
      r = normalize rhs;
      collisions = builtins.filter
        (constructorTag: builtins.hasAttr constructorTag l.handlers)
        (builtins.attrNames r.handlers);
    in
    if collisions != [ ]
    then throw "surface.registry.merge: duplicate handler(s): ${toString collisions}"
    else l // { handlers = l.handlers // r.handlers; };

  withRegistry = registry: node:
    node // { _surfaceRegistry = normalize registry; };

  node = registry: constructorTag: fields:
    withRegistry registry ({ _htag = checkTag constructorTag; } // fields);
in
{
  scope = {
    empty = api.leaf {
      value = empty;
      description = "Empty surface elaboration registry.";
      signature = "Registry";
    };
    fromHandlers = api.leaf {
      value = fromHandlers;
      description = "Build a surface registry from an attrset of constructor-tag handlers.";
      signature = "{ tag : Handler } -> Registry";
    };
    isRegistry = api.leaf {
      value = isRegistry;
      description = "Predicate for surface elaboration registries.";
      signature = "Any -> Bool";
    };
    lookup = api.leaf {
      value = lookup;
      description = "Return the handler registered for a surface constructor tag, or null.";
      signature = "Registry -> String -> Handler | Null";
    };
    merge = api.leaf {
      value = merge;
      description = "Merge two surface registries, rejecting duplicate constructor handlers.";
      signature = "Registry -> Registry -> Registry";
    };
    node = api.leaf {
      value = node;
      description = "Construct a surface AST node carrying its registry.";
      signature = "Registry -> String -> Attrs -> Hoas";
    };
    normalize = api.leaf {
      value = normalize;
      description = "Normalize nullable registry inputs to a registry record.";
      signature = "Registry | Null -> Registry";
    };
    register = api.leaf {
      value = register;
      description = "Register a handler for one surface constructor tag.";
      signature = "Registry -> String -> Handler -> Registry";
    };
    withRegistry = api.leaf {
      value = withRegistry;
      description = "Attach a surface elaboration registry to an existing node.";
      signature = "Registry -> Attrs -> Hoas";
    };
    emptyRegistry = api.leaf {
      value = empty;
      description = "Alias for the empty surface elaboration registry.";
      signature = "Registry";
    };
    handlerFor = api.leaf {
      value = lookup;
      description = "Alias for lookup.";
      signature = "Registry -> String -> Handler | Null";
    };
  };

  tests = {
    "surface-registry-lookup-hit" = {
      expr =
        let
          r = register empty "surface.test" (_: "ok");
        in
        (lookup r "surface.test" { }) == "ok";
      expected = true;
    };

    "surface-registry-lookup-miss" = {
      expr = lookup empty "surface.missing";
      expected = null;
    };

    "surface-registry-node-attaches-registry" = {
      expr =
        let
          n = node empty "surface.node" { value = 1; };
        in
        n._htag;
      expected = "surface.node";
    };
  };

}
