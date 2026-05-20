{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.surface: additive surface-language elaboration framework over HOAS.";
  doc = ''
    Surface specifications define constructor tags and handlers. HOAS
    elaboration consults the attached registry only for nodes that carry
    `_surfaceRegistry`, so existing HOAS terms continue through the built-in
    dispatcher.
  '';
  value = {
    inherit (self)
      defineOrnament defineSurface deriveElaborator deriveParser derivePrinter
      elaborate framework parse prelude print surfaceTerm toy
      collectImplicitMetas collectSurfaceMetas containsImplicitMeta
      containsSurfaceMeta finalizeSurfaceElab handlerContext implicitMeta
      unsolvedImplicitError withSurfaceContext;

    registry = api.namespace {
      description = "Surface elaborator registry operations.";
      value = {
        inherit (self)
          empty emptyRegistry fromHandlers handlerFor isRegistry lookup merge node
          normalize register withRegistry;
      };
    };
  };
  tests = partTests;
}
