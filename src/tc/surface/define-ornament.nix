{ api, ... }:

let
  defineOrnament = args:
    let
      mapping = args.mapping or { };
    in
    {
      _surfaceOrnamentTag = "nix-effects.surface.ornament";
      source = args.source or (throw "defineOrnament: missing source");
      target = args.target or (throw "defineOrnament: missing target");
      inherit mapping;
      section = args.section or mapping.section or (term: term);
      forget = args.forget or mapping.forget or (term: term);
    };
in
{
  scope = {
    defineOrnament = api.leaf {
      value = defineOrnament;
      description = "Package a surface-to-target mapping with section and forget morphisms for elaborator derivation.";
      signature = "{ source, target, mapping?, section?, forget? } -> SurfaceOrnament";
    };
  };

  tests = { };
}
