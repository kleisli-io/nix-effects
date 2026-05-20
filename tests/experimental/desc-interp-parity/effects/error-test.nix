{ lib, fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) error;

  H  = fx.tc.hoas;
  K  = fx.experimental.descInterp.kernel;
  T  = fx.experimental.descInterp.trampoline;
  DE = fx.experimental.descInterp.effects.error;

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);
  pureD    = K.pure testEff testResp H.nat;
  bindD    = K.bind testEff testResp H.nat H.nat;
  handleD  = T.handle testEff testResp H.nat;

  errorCollecting = {
    prod =
      let
        comp = bind (error.raiseWith "parser" "unexpected token") (_:
          bind (error.raiseWith "parser" "missing semicolon") (_:
            pure "ok"));
        result = handle { handlers = error.collecting; state = []; } comp;
      in builtins.length result.state;
    desc =
      let
        comp = bindD (DE.raiseWith "parser" "unexpected token") (_:
          bindD (DE.raiseWith "parser" "missing semicolon") (_:
            pureD "ok"));
        result = handleD { handlers = DE.collecting; state = []; } comp;
      in builtins.length result.state;
  };

  errorContext = {
    prod =
      let
        comp = error.raiseWith "validator" "field required";
        result = handle { handlers = error.collecting; state = []; } comp;
      in (builtins.head result.state).context;
    desc =
      let
        comp = DE.raiseWith "validator" "field required";
        result = handleD { handlers = DE.collecting; state = []; } comp;
      in (builtins.head result.state).context;
  };

  parityOf = name: t: { inherit name; expr = t.desc; expected = t.prod; };

  testCases = {
    errorCollectingParity = parityOf "errorCollecting" errorCollecting;
    errorContextParity    = parityOf "errorContext"    errorContext;
  };

  results = builtins.mapAttrs (_: t:
    let actual = t.expr; in
    { inherit actual; expected = t.expected; pass = actual == t.expected; }
  ) testCases;

  failed = lib.filterAttrs (_: r: !r.pass) results;

in testCases // {
  allPass = (builtins.length (builtins.attrNames failed)) == 0;
}
