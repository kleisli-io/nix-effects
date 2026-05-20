# Ornament workloads.
#
# These force the public ornament surface at downstream adoption points:
# description generation, forget elaboration/checking,
# composition, and algebraic List-to-Vec indexing.
{ fx }:

let
  H = fx.types.hoas;
  G = fx.types.generic;

  Box = H.datatype "BenchOrnBox" [
    (H.con "box" [ (H.field "value" H.nat) ])
  ];

  Tagged = H.ornament Box {
    name = "BenchTaggedBox";
    constructors.box.fields = [
      { insert = "tag"; type = H.bool; }
      { keep = "value"; }
    ];
  };

  Labeled = H.ornament Tagged {
    name = "BenchLabeledTaggedBox";
    constructors.box.fields = [
      { insert = "label"; type = H.string; }
      { keep = "tag"; }
      { keep = "value"; }
    ];
  };

  taggedValue = H.app (H.app Tagged.box H.true_) H.zero;
  labeledValue = H.app (H.app (H.app Labeled.box "bench") H.true_) H.zero;

  FunctionalTagged = G.ornaments.functional {
    base = Box;
    spec = {
      name = "BenchFunctionalTaggedBox";
      constructors.box.fields = [
        { insert = "tag"; type = H.bool; }
        { keep = "value"; }
      ];
    };
    synth.constructors.box.fields.tag = _ctx: true;
  };
  functionalBaseValue = H.app Box.box H.zero;
  functionalProducer =
    H.ann
      (H.lam "x" Box.T (_: H.app Box.box H.zero))
      (H.forall "_" Box.T (_: Box.T));

  listNatD =
    H.plus H.descRet
      (H.descArg H.unit 0 H.nat (_:
        H.descRec H.descRet));
  listNatLengthAlg =
    H.algPlus
      (H.algRet H.zero)
      (H.algArg (_x:
        H.algRec (n:
          H.algRet (H.succ n))));
  eraseNatToUnit =
    H.ann
      (H.lam "_" H.nat (_: H.tt))
      (H.forall "_" H.nat (_: H.unit));
  ListVec = G.ornaments.algOrn {
    I = H.unit;
    J = H.nat;
    erase = eraseNatToUnit;
    D = listNatD;
    algebra = listNatLengthAlg;
  };

  piVoidD = H.descPi 0 H.void H.descRet;
  PiKeep = G.ornaments.algOrn {
    I = H.unit;
    J = H.nat;
    erase = eraseNatToUnit;
    D = piVoidD;
    algebra = H.algPiKeep {
      branchIndex = x: H.absurd H.nat x;
    } (H.algRet H.zero);
  };

in {
  ornDesc-normalize = (H.elab (H.ornDesc Tagged.ornament)).tag;

  ornForget-elaborate = (H.elab Tagged.forget0).tag;

  ornForget-check =
    (H.checkHoas Box.T (G.ornaments.forget Tagged taggedValue)).tag;

  ornCompose-check =
    let
      composed = G.ornaments.compose Labeled Tagged;
      forget = H.ornForget composed;
      D = H.ornDesc composed;
      ty = H.forall "i" H.unit (i:
        H.forall "_" (H.muI H.unit D i) (_:
          Box.T));
    in (H.checkHoas ty forget).tag;

  functional-synthesis-build =
    let
      built = G.ornaments.build FunctionalTagged functionalBaseValue;
      forgot = G.ornaments.forget FunctionalTagged built;
    in (H.checkHoas Box.T forgot).tag;

  functional-diagnostics-missing-builder =
    builtins.length (G.ornaments.validateFunctional {
      base = Box;
      spec = {
        name = "BenchFunctionalMissingTaggedBox";
        constructors.box.fields = [
          { insert = "tag"; type = H.bool; }
          { keep = "value"; }
        ];
      };
      synth = {};
    }).diagnostics;

  functional-liftProducer-check =
    let
      built =
        G.ornaments.liftProducer
          FunctionalTagged
          functionalProducer
          functionalBaseValue;
    in (H.checkHoas FunctionalTagged.meta.ornamented.T built).tag;

  alg-list-to-vec-check =
    let
      D = H.ornDesc ListVec;
      forgetTy =
        H.forall "n" H.nat (n:
          H.forall "_" (H.muI H.nat D n) (_:
            H.muI H.unit listNatD H.tt));
    in (H.checkHoas forgetTy (G.ornaments.forgetHoas ListVec)).tag;

  alg-pi-keep-check =
    let
      D = H.ornDesc PiKeep;
      forgetTy =
        H.forall "n" H.nat (n:
          H.forall "_" (H.muI H.nat D n) (_:
            H.muI H.unit piVoidD H.tt));
    in (H.checkHoas forgetTy (G.ornaments.forgetHoas PiKeep)).tag;
}
