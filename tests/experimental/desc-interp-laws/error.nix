# Error algebraicity (Plotkin & Pretnar):
#   bind (raise e) k₁  ≡  bind (raise e) k₂   for any k₁, k₂
#
# Once an error is raised the continuation is discarded; output depends
# only on the raised payload. Uses `result` strategy (abort action)
# rather than `strict` (throw action) so both sides reach a Pure leaf
# rather than `builtins.throw`-ing inside the trampoline.
{ lib, fx }:

let
  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  G = fx.tc.generic.desc;
  Elab = fx.tc.elaborate;

  errorMod = fx.experimental.descInterp.effects.error;
  errResult = errorMod.atType_result H.string H.unit H.nat;

  pureD = K.pure errResult.eff errResult.resp H.nat;
  bindVN = K.bind errResult.eff errResult.resp H.void H.nat;

  asHoas = x: if x ? _htag then x else Elab.embedVal x;
  lawEq = lhs: rhs: G.deepEqualDesc (asHoas lhs) (asHoas rhs);

  runProg = prog: initS:
    T.run errResult.eff errResult.resp H.nat
      { inherit (errResult) handler dispatch; }
      prog
      initS;

  raiseProgK = k: bindVN (errResult.raise (H.stringLit "boom")) k;
  k1 = _: pureD (H.intLit 42);
  k2 = _: pureD (H.intLit 99);

  algebraicity = {
    lhs = raiseProgK k1;
    rhs = raiseProgK k2;
    initS = H.tt;
  };

  proveAlgebraicity = law:
    let
      rL = runProg law.lhs law.initS;
      rR = runProg law.rhs law.initS;
    in
    lawEq rL.value rR.value && lawEq rL.state rR.state;

  testCases = {
    "error-law-algebraicity" = {
      expr = proveAlgebraicity algebraicity;
      expected = true;
    };
  };

in
testCases
