{ self, api, ... }:

let
  positionOf = h:
    if h ? _surfacePosition then h._surfacePosition
    else if h ? position then h.position
    else null;

  handlerContext = args:
    let
      h = args.h;
      position = args.position or positionOf h;
      expectedType = args.expectedType or (h._surfaceExpectedType or null);
      surface = h._surface or null;
      constructor = h._constructor or null;
      context = {
        inherit expectedType position surface constructor;
        term = h;
        implicitMeta = metaArgs:
          self.implicitMeta (metaArgs // {
            position = metaArgs.position or position;
            surface = metaArgs.surface or surface;
          });
      };
    in
    args // {
      inherit context expectedType position;
    };

  withSurfaceContext = args:
    let
      term = args.term or (throw "withSurfaceContext: missing term");
      position =
        if args ? position then args.position
        else if builtins.isAttrs term && term ? _surfacePosition then term._surfacePosition
        else null;
    in
    if builtins.isAttrs term then term // {
      _surfaceExpectedType = args.expectedType or null;
      _surfacePosition = position;
    }
    else term;
in
{
  scope = {
    handlerContext = api.leaf {
      value = handlerContext;
      description = "Build the argument record passed to surface elaboration handlers, adding expected type, source position, and implicit-meta helpers.";
      signature = "{ h, depth, elaborate, hoas, fx, ... } -> HandlerArgs";
    };
    withSurfaceContext = api.leaf {
      value = withSurfaceContext;
      description = "Attach root expected-type and position metadata to a surface AST node before elaboration.";
      signature = "{ term, expectedType?, position? } -> Hoas";
    };
  };

  tests = { };
}
