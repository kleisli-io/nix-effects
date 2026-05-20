# Error effect over `experimental.desc-interp.kernel.send`. One op
# (`error`); three handler strategies (`strict`, `collecting`, `result`).
{ fx, ... }:
let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;

  testEff   = H.bool;
  testResp  = H.lam "_" H.bool (_: H.nat);

  send_     = K.send testEff testResp;
  prod      = fx.effects.error;

  raise     = message: send_ { _opTag = "error"; param = { inherit message; context = ""; }; };
  raiseWith = context: message: send_ { _opTag = "error"; param = { inherit message context; }; };

  mkHandler = strategy: { param, state }:
    if param._opTag == "error"
    then strategy.error { param = param.param; inherit state; }
    else throw "experimental.descInterp.effects.error.<handler>: unknown op tag '${toString (param._opTag or "?")}'";

  strict     = mkHandler prod.strict;
  collecting = mkHandler prod.collecting;
  result     = mkHandler prod.result;

in {
  inherit raise raiseWith strict collecting result;

  __docs._self = {
    description = "error effect over descInterp's FreeFx kernel — raise/raiseWith with strict/collecting/result handlers.";
    doc = ''
      Pair with `experimental.descInterp.trampoline.handle`:

      ```nix
      handle testEff testResp H.nat
        { handlers = error.collecting; state = []; }
        program
      ```
    '';
  };
}
