# Generic Desc-payload checker workloads.
{ fx }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  C = fx.tc.check;
  G = fx.tc.generic;

  n = 5000;
  ids = builtins.genList (x: x) n;
  mod = x: y: x - x / y * y;

  retD = { tag = "DViewRet"; idx = 0; j = V.vTt; };

  argD = sub: {
    tag = "DViewArg";
    idx = 1;
    sTy = V.vUnit;
    tFn = { tag = "VDescViewFn"; kind = "const"; result = sub; };
  };

  recD = sub: {
    tag = "DViewRec";
    idx = 2;
    j = V.vTt;
    inherit sub;
  };

  piD = sub: {
    tag = "DViewPi";
    idx = 3;
    sTy = V.vUnit;
    fn = V.vLam "_" V.vUnit (V.mkClosure [ ] T.mkTt);
    inherit sub;
  };

  layer = i: sub:
    let k = mod i 3; in
    if k == 0 then argD sub
    else if k == 1 then recD sub
    else piD sub;

  headTm = i:
    if mod i 3 == 2
    then T.mkLam "x" T.mkUnit T.mkTt
    else T.mkTt;

  chainD = builtins.foldl' (acc: i: layer i acc) retD ids;
  payloadCore = builtins.foldl'
    (acc: i: T.mkPair (headTm i) acc)
    T.mkBootRefl
    ids;

  plusD = {
    tag = "DViewPlus";
    idx = 4;
    A = retD;
    B = chainD;
  };

  payload = T.mkBootInr T.mkUnit T.mkUnit payloadCore;

  X_unit = V.vLam "_" V.vUnit (V.mkClosure [ ] T.mkUnit);

  spec = {
    level = V.vLevelZero;
    I = V.vUnit;
    D = plusD;
    X = X_unit;
    i = V.vTt;
  };

in
{
  mixed-chain-5000 =
    (C.runCheck (G.checkD.checkDAt C.emptyCtx spec payload)).tag;
}
