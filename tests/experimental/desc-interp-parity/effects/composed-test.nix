# Composed state + error over `{ counter; errors; }`. The descInterp side
# hand-rolls the unified handler instead of using `adaptHandlers` — production
# `adaptHandlers` has no descInterp analogue yet, but production handler bodies
# are still re-used inside each branch.
{ lib, fx }:

let
  inherit (fx) bind handle adaptHandlers;
  inherit (fx.effects) state error;

  H  = fx.tc.hoas;
  K  = fx.experimental.descInterp.kernel;
  T  = fx.experimental.descInterp.trampoline;
  DS = fx.experimental.descInterp.effects.state;
  DE = fx.experimental.descInterp.effects.error;

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);
  bindD    = K.bind testEff testResp H.nat H.nat;
  handleD  = T.handle testEff testResp H.nat;

  prodErrorBody = fx.effects.error.collecting.error;
  prodStateH    = fx.effects.state.handler;

  composedHandlerD = { param, state }:
    if param._opTag == "get"
    then
      let r = prodStateH.get { state = state.counter; param = null; };
      in { resume = r.resume; state = state // { counter = r.state; }; }
    else if param._opTag == "put"
    then
      let r = prodStateH.put { state = state.counter; param = param.param; };
      in { resume = r.resume; state = state // { counter = r.state; }; }
    else if param._opTag == "modify"
    then
      let r = prodStateH.modify { state = state.counter; param = param.fn; };
      in { resume = r.resume; state = state // { counter = r.state; }; }
    else if param._opTag == "error"
    then
      let r = prodErrorBody { param = param.param; state = state.errors; };
      in { resume = r.resume; state = state // { errors = r.state; }; }
    else throw "composed handler: unknown op tag '${toString (param._opTag or "?")}'";

  composed = {
    prod =
      let
        adaptedState = adaptHandlers {
          get = s: s.counter;
          set = s: c: s // { counter = c; };
        } state.handler;

        adaptedError = adaptHandlers {
          get = s: s.errors;
          set = s: e: s // { errors = e; };
        } error.collecting;

        comp = bind (state.modify (n: n + 1)) (_:
          bind (error.raiseWith "step2" "bad value") (_:
            bind (state.modify (n: n + 10)) (_:
              state.get)));

        result = handle {
          handlers = adaptedState // adaptedError;
          state = { counter = 0; errors = []; };
        } comp;
      in {
        value = result.value;
        errors = result.state.errors;
        counter = result.state.counter;
      };
    desc =
      let
        comp = bindD (DS.modify (n: n + 1)) (_:
          bindD (DE.raiseWith "step2" "bad value") (_:
            bindD (DS.modify (n: n + 10)) (_:
              DS.get)));

        result = handleD {
          handlers = composedHandlerD;
          state = { counter = 0; errors = []; };
        } comp;
      in {
        value = result.value;
        errors = result.state.errors;
        counter = result.state.counter;
      };
  };

  parityOf = name: t: { inherit name; expr = t.desc; expected = t.prod; };

  testCases = {
    composedAdaptedParity = parityOf "composedAdapted" composed;
  };

  results = builtins.mapAttrs (_: t:
    let actual = t.expr; in
    { inherit actual; expected = t.expected; pass = actual == t.expected; }
  ) testCases;

  failed = lib.filterAttrs (_: r: !r.pass) results;

in testCases // {
  allPass = (builtins.length (builtins.attrNames failed)) == 0;
}
