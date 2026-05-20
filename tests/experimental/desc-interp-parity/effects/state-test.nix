# Each test runs the same program through `fx.handle` and through
# `fx.experimental.descInterp.trampoline.handle`, then asserts `==`.
{ lib, fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) state;

  H  = fx.tc.hoas;
  K  = fx.experimental.descInterp.kernel;
  T  = fx.experimental.descInterp.trampoline;
  DS = fx.experimental.descInterp.effects.state;

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);
  pureD    = K.pure testEff testResp H.nat;
  bindD    = K.bind testEff testResp H.nat H.nat;
  handleD  = T.handle testEff testResp H.nat;

  stateCounter = {
    prod =
      let
        comp = bind state.get (n:
          bind (state.put (n + 1)) (_:
            bind state.get (n2:
              pure n2)));
      in handle { handlers = state.handler; state = 0; } comp;
    desc =
      let
        comp = bindD DS.get (n:
          bindD (DS.put (n + 1)) (_:
            bindD DS.get (n2:
              pureD n2)));
      in handleD { handlers = DS.handler; state = 0; } comp;
  };

  stateModify = {
    prod =
      let
        comp = bind (state.modify (n: n * 3)) (_:
          bind (state.modify (n: n + 2)) (_:
            state.get));
      in handle { handlers = state.handler; state = 10; } comp;
    desc =
      let
        comp = bindD (DS.modify (n: n * 3)) (_:
          bindD (DS.modify (n: n + 2)) (_:
            DS.get));
      in handleD { handlers = DS.handler; state = 10; } comp;
  };

  stateGets = {
    prod =
      let
        comp = bind (state.put { x = 42; y = 99; }) (_:
          state.gets (s: s.x));
      in handle { handlers = state.handler; state = null; } comp;
    desc =
      let
        comp = bindD (DS.put { x = 42; y = 99; }) (_:
          DS.gets (s: s.x));
      in handleD { handlers = DS.handler; state = null; } comp;
  };

  stateFinalState = {
    prod =
      let
        comp = bind (state.modify (n: n + 5)) (_:
          bind (state.modify (n: n * 2)) (_:
            pure "done"));
      in handle { handlers = state.handler; state = 10; } comp;
    desc =
      let
        comp = bindD (DS.modify (n: n + 5)) (_:
          bindD (DS.modify (n: n * 2)) (_:
            pureD "done"));
      in handleD { handlers = DS.handler; state = 10; } comp;
  };

  parityOf = name: t: { inherit name; expr = t.desc; expected = t.prod; };

  testCases = {
    stateCounterParity    = parityOf "stateCounter"    stateCounter;
    stateModifyParity     = parityOf "stateModify"     stateModify;
    stateGetsParity       = parityOf "stateGets"       stateGets;
    stateFinalStateParity = parityOf "stateFinalState" stateFinalState;
  };

  results = builtins.mapAttrs (_: t:
    let actual = t.expr; in
    { inherit actual; expected = t.expected; pass = actual == t.expected; }
  ) testCases;

  failed = lib.filterAttrs (_: r: !r.pass) results;

in testCases // {
  allPass = (builtins.length (builtins.attrNames failed)) == 0;
}
