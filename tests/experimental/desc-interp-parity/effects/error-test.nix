{ lib, fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) error;

  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  Elab = fx.tc.elaborate;

  errorMod = fx.experimental.descInterp.effects.error;
  errCol = errorMod.atType_collecting H.string;
  pureD = K.pure errCol.eff errCol.resp H.nat;
  bindD = K.bind errCol.eff errCol.resp H.nat H.nat;

  # Two raises; final pure. Collecting handler accumulates payloads
  # into `List E`. Parity is on the count of collected errors — prod
  # uses `{msg; context;}` records, desc uses bare strings, so the
  # extracted lists differ in element shape but agree in length.
  errorCollecting = {
    prod =
      let
        comp = bind (error.raiseWith "parser" "unexpected token") (_:
          bind (error.raiseWith "parser" "missing semicolon") (_:
            pure "ok"));
        result = handle { handlers = error.collecting; state = [ ]; } comp;
      in
      builtins.length result.state;
    desc =
      let
        comp = bindD (errCol.raise (H.stringLit "unexpected token")) (_:
          bindD (errCol.raise (H.stringLit "missing semicolon")) (_:
            pureD (H.stringLit "ok")));
        result = T.handle errCol.eff errCol.resp H.nat
          {
            inherit (errCol) handler dispatch;
            state = HI.nilAtExplicit H.string;
          }
          comp;
      in
      builtins.length (Elab.extract (H.listOf H.string) result.state);
  };

  parityOf = name: t: { inherit name; expr = t.desc; expected = t.prod; };

  testCases = {
    errorCollectingParity = parityOf "errorCollecting" errorCollecting;
  };

in
testCases
