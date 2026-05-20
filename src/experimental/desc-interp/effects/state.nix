# State effect over `experimental.desc-interp.kernel.send`. Op identity is
# carried in a Nix sentinel attrset `{ _opTag = ...; ... }` because the
# trampoline never inspects `op`'s structure — only the handler does.
# `(Eff, Resp, A)` indices are uniformly `H.bool / _ → H.nat / H.nat`;
# the descInterp runtime is type-agnostic at this layer.
{ fx, ... }:
let
  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;

  testEff   = H.bool;
  testResp  = H.lam "_" H.bool (_: H.nat);

  send_     = K.send testEff testResp;
  pure_     = K.pure testEff testResp H.nat;
  bind_     = K.bind testEff testResp H.nat H.nat;

  prod      = fx.effects.state;

  get       = send_ { _opTag = "get"; };
  put       = s: send_ { _opTag = "put"; param = s; };
  modify    = f: send_ { _opTag = "modify"; fn = f; };

  gets      = f: bind_ get (s: pure_ (f s));

  update    = f:
    bind_ get (state:
      bind_ (f state) ({ state, value }:
        bind_ (put state) (_:
          pure_ value)));

  handler = { param, state }:
    if      param._opTag == "get"    then prod.handler.get    { inherit state; param = null; }
    else if param._opTag == "put"    then prod.handler.put    { inherit state; param = param.param; }
    else if param._opTag == "modify" then prod.handler.modify { inherit state; param = param.fn; }
    else throw "experimental.descInterp.effects.state.handler: unknown op tag '${toString (param._opTag or "?")}'";

in {
  inherit get put modify gets update handler;

  __docs._self = {
    description = "state effect over descInterp's FreeFx kernel — get/put/modify with the standard handler.";
    doc = ''
      Pair with `experimental.descInterp.trampoline.handle`:

      ```nix
      handle testEff testResp H.nat
        { handlers = state.handler; state = initial; }
        program
      ```
    '';
  };
}
