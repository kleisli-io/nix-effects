# Bind-chain stress for the FreeFx description-universe kernel. A single
# `send` heads a `foldl'`-built chain of `bind (… pure (x + 1))`; the
# kontQueue grows to length N but host stack stays at O(1).
{ fx }:

let
  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);

  pureD = K.pure testEff testResp H.nat;
  bindD = K.bind testEff testResp H.nat H.nat;
  sendD = K.send testEff testResp;
  runD  = T.run testEff testResp H.nat;

  mkBindChain = n:
    let
      sendInit    = sendD { _opTag = "init"; };
      initHandler = { param, state }: { resume = 0; inherit state; };

      comp = builtins.foldl'
        (acc: _: bindD acc (x: pureD (x + 1)))
        sendInit
        (builtins.genList (x: x) n);

      r = runD initHandler comp null;
    in r.value;

in {
  s100k = mkBindChain 100000;
}
