# Bind associativity on Impure m:
#   bind (bind m f) g  ≡  bind m (λx. bind (f x) g)
#
# Raw μ-trees diverge: LHS builds `qNode (qLeaf f) (qLeaf g)`, RHS
# builds `qLeaf (composed-continuation)`. Under `T.run` both collapse
# to the same Pure leaf — `deepEqualDesc` on the post-run carriers
# decides.
#
# Witness: m = `get`, f = `λn. put (succ n)`, g = `λ_. get`. From
# initial state `s` both sides yield `value = state = s + 1`.
{ lib, fx }:

let
  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  G = fx.tc.generic.desc;
  Elab = fx.tc.elaborate;

  stateMod = fx.experimental.descInterp.effects.state;
  stateAtNat = stateMod.atType H.nat H.nat;

  bindNN = K.bind stateAtNat.eff stateAtNat.resp H.nat H.nat;
  bindNU = K.bind stateAtNat.eff stateAtNat.resp H.nat H.unit;
  bindUN = K.bind stateAtNat.eff stateAtNat.resp H.unit H.nat;

  asHoas = x: if x ? _htag then x else Elab.embedVal x;
  lawEq = lhs: rhs: G.deepEqualDesc (asHoas lhs) (asHoas rhs);

  runProg = prog: initS:
    T.run stateAtNat.eff stateAtNat.resp H.nat
      { inherit (stateAtNat) handler dispatch; }
      prog
      initS;

  m = stateAtNat.get;
  f = x: stateAtNat.put (H.succ (asHoas x));
  g = _: stateAtNat.get;

  bindMF = bindNU m f;
  bindAssocLhs = bindUN bindMF g;
  bindAssocRhs = bindNN m (x: bindUN (f x) g);

  bindAssoc = {
    lhs = bindAssocLhs;
    rhs = bindAssocRhs;
    initS = H.zero;
  };

  proveBindAssoc = law:
    let
      rL = runProg law.lhs law.initS;
      rR = runProg law.rhs law.initS;
    in
    lawEq rL.value rR.value && lawEq rL.state rR.state;

  testCases = {
    "bind-assoc-impure-m" = {
      expr = proveBindAssoc bindAssoc;
      expected = true;
    };
  };

in
testCases
