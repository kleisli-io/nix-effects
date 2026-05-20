{ self, api, ... }:

let
  surfaceTerm = surface: constructorName: fields:
    surface.mk constructorName fields;

  framework = {
    inherit (self)
      defineSurface defineOrnament deriveElaborator deriveParser derivePrinter
      elaborate parse print;
    inherit surfaceTerm;
  };
in
{
  scope = {
    framework = api.leaf {
      value = framework;
      description = "Convenience bundle for the surface-language definition, ornament, elaboration, parser, and printer APIs.";
    };
    surfaceTerm = api.leaf {
      value = surfaceTerm;
      description = "Construct one term from a surface specification.";
      signature = "SurfaceSpec -> String -> Attrs -> Hoas";
    };
  };

  tests = { };
}
