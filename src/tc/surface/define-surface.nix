{ self, api, ... }:

let
  constructorTag = surfaceName: constructorName: spec:
    spec.tag or "${surfaceName}.${constructorName}";

  constructorHandler = surfaceName: constructorName: spec:
    if spec ? handler then spec.handler
    else throw "defineSurface ${surfaceName}: constructor ${constructorName} has no handler";

  defineSurface = args:
    let
      surfaceName = args.name or (throw "defineSurface: missing name");
      constructors = args.constructors or { };
      handlers = builtins.listToAttrs (map
        (constructorName:
          let
            spec = constructors.${constructorName};
          in
          {
            name = constructorTag surfaceName constructorName spec;
            value = constructorHandler surfaceName constructorName spec;
          })
        (builtins.attrNames constructors));
      registry = self.fromHandlers handlers;
      mk = constructorName: fields:
        let
          spec =
            if builtins.hasAttr constructorName constructors
            then constructors.${constructorName}
            else throw "defineSurface ${surfaceName}: unknown constructor ${constructorName}";
          plicityField =
            if spec ? plicity && !(fields ? _plicity)
            then { _plicity = spec.plicity; }
            else { };
        in
        self.node registry (constructorTag surfaceName constructorName spec)
          (fields // {
            _surface = surfaceName;
            _constructor = constructorName;
          } // plicityField);
      terms = builtins.mapAttrs (constructorName: _: fields: mk constructorName fields) constructors;
    in
    {
      _surfaceSpecTag = "nix-effects.surface.spec";
      name = surfaceName;
      description = args.description or "";
      scope = args.scope or { };
      inherit constructors handlers registry mk terms;
    };
in
{
  scope = {
    defineSurface = api.leaf {
      value = defineSurface;
      description = "Define a named surface language with constructor metadata and elaboration handlers.";
      signature = "{ name, description?, scope?, constructors } -> SurfaceSpec";
    };
  };

  tests = { };
}
