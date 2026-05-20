# State effect laws under `stateAtNat`. Each law runs both sides
# through `T.run` and asserts `deepEqualDesc` on `.value` and `.state`.
#
#   get-get : bind get (λ_. bind get (λn. pure n))  ≡  bind get (λn. pure n)
#   get-put : bind get (λn. put n)                  ≡  pure tt
#   put-get : bind (put v) (λ_. get)                ≡  bind (put v) (λ_. pure v)
#
# Raw μ-trees of LHS/RHS differ structurally (queue shape, bind
# depth); after `T.run` both reduce to Pure leaves carrying conv-equal
# Vals.
{ lib, fx }:

let
  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  G = fx.tc.generic.desc;
  Elab = fx.tc.elaborate;

  stateMod = fx.experimental.descInterp.effects.state;
  stateAtNat = stateMod.atType H.nat H.nat;

  pureD = K.pure stateAtNat.eff stateAtNat.resp H.nat;
  bindNN = K.bind stateAtNat.eff stateAtNat.resp H.nat H.nat;
  bindUN = K.bind stateAtNat.eff stateAtNat.resp H.unit H.nat;

  # `result.value` may be HOAS or a Val depending on the program;
  # `asHoas` normalises to HOAS so `deepEqualDesc` evaluates both sides
  # uniformly.
  asHoas = x: if x ? _htag then x else Elab.embedVal x;

  lawEq = lhs: rhs: G.deepEqualDesc (asHoas lhs) (asHoas rhs);

  runProg = A: prog: initS:
    T.run stateAtNat.eff stateAtNat.resp A
      { inherit (stateAtNat) handler dispatch; }
      prog
      initS;

  getGetLhs = bindNN stateAtNat.get (_:
    bindNN stateAtNat.get (n: pureD n));
  getGetRhs = bindNN stateAtNat.get (n: pureD n);

  getGet = {
    initS = H.succ (H.succ (H.succ H.zero));
    A = H.nat;
    lhs = getGetLhs;
    rhs = getGetRhs;
  };

  getPutLhs = bindNN stateAtNat.get (n: stateAtNat.put (asHoas n));
  getPutRhs = K.pure stateAtNat.eff stateAtNat.resp H.unit H.tt;

  getPut = {
    initS = H.succ H.zero;
    A = H.unit;
    lhs = getPutLhs;
    rhs = getPutRhs;
  };

  putGetVal = H.succ (H.succ H.zero);

  putGetLhs = bindUN (stateAtNat.put putGetVal) (_: stateAtNat.get);
  putGetRhs = bindUN (stateAtNat.put putGetVal) (_: pureD putGetVal);

  putGet = {
    initS = H.zero;
    A = H.nat;
    lhs = putGetLhs;
    rhs = putGetRhs;
  };

  proveLaw = law:
    let
      rL = runProg law.A law.lhs law.initS;
      rR = runProg law.A law.rhs law.initS;
    in
    lawEq rL.value rR.value && lawEq rL.state rR.state;

  testCases = {
    "state-law-get-get" = { expr = proveLaw getGet; expected = true; };
    "state-law-get-put" = { expr = proveLaw getPut; expected = true; };
    "state-law-put-get" = { expr = proveLaw putGet; expected = true; };
  };

in
testCases
