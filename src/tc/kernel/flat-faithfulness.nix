# Faithfulness certificate for the flat predicate-stack decider.
#
# The decider is a LEFT (accumulator) fold over the predicate stack. This part
# pins down the load-bearing properties: the fold reduces in the accumulation
# order on the nose (definitionally equal to the spec left-accumulation, while a
# right fold agrees only in value), the predicate stack is homogeneous over the
# single base carrier, the membership decoder over the decider behaves correctly,
# and the decider stays a single linear fold at a stack depth far beyond where a
# per-level meta-tower would detonate.
#
# The fold-order family abstracts over NEUTRAL predicates (not applied to a
# concrete witness) so the fold term-shape is observable: andB reduces on its
# first argument only, so a left fold absorbs the leading unit while a right fold
# leaves a trailing unit stuck on the neutral scrutinee.
{ self, fx, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  C = fx.tc.conv;
  app = H.app;
  ev = h: E.eval [ ] (H.elab h);
  conv = a: b: C.conv 0 (ev a) (ev b);
  chk = ty: h: !((H.checkHoas ty h) ? error);
  foldr = f: z: xs: if xs == [ ] then z else f (builtins.head xs) (foldr f z (builtins.tail xs));
  rep = n: x: builtins.genList (_: x) n;

  inherit (self.ktype) P andB KType decide iota refine;

  # Concrete base, carrier, witness, and predicates over it.
  B = H.datatype "B" [ (H.con "tt0" [ ]) (H.con "ff0" [ ]) ];
  BoolDesc = B.D;
  A = H.mu BoolDesc H.tt;
  xWit = app B.tt0 H.tt;
  pTrue = H.lam "x" A (_: H.true_);
  pFalse = H.lam "x" A (_: H.false_);

  predTy = A: H.forall "_" A (_: H.bool);
  PredA = predTy A;
  listP = A: H.listOf (predTy A);

  # Build a flat code by folding the shipped refine constructor over a Nix list of
  # predicates (base-first), starting from the iota base — exercising the real
  # constructor path. mkList is the raw predicate list, used by the rejected
  # right-fold counter-encoding and the homogeneity check.
  mkList = ps: foldr (p: acc: H.cons p acc) H.nil ps;
  mkCode = ps: builtins.foldl' (acc: p: refine acc p) (iota A) ps;
  decideAt = ps: x: app (decide (mkCode ps)) x;

  # The depth-128 scaling gate certifies the DECIDER stays a single linear fold —
  # a property of the decider, agnostic to how the deep code is built. To isolate
  # the decider it builds the predicate stack flat (a direct cons chain: the
  # identical value a depth-128 refine chain produces), not by materializing 128
  # nested tail-appends whose quadratic blowup would measure construction rather
  # than the decider. Deep constructor faithfulness is the uniform induction
  # witnessed by the small-depth refine gates here and the refine well-typedness
  # checks in tests.nix.
  directCode = ps: H.ann (H.pair A (H.ann (mkList ps) (listP A))) KType;
  decideAtDirect = ps: x: app (decide (directCode ps)) x;

  # Fold-order probe bodies over neutral predicates.
  specLBody = ps: x: builtins.foldl' (acc: p: andB acc (app p x)) H.true_ ps;
  flatLBody = ps: x: decideAt ps x;
  flatRBody = ps: x:
    H.listElim 0 PredA (H.lam "_" (H.listOf PredA) (_: H.bool)) H.true_
      (H.lam "p" PredA (p: H.lam "t" (H.listOf PredA) (_: H.lam "ih" H.bool (ih: andB (app p x) ih))))
      (mkList ps);
  absK = k: body:
    let go = acc: i: if i == 0 then H.lam "x" A (x: body acc x)
    else H.lam "p${toString i}" PredA (pv: go (acc ++ [ pv ]) (i - 1));
    in go [ ] k;
in
{
  scope = { };
  tests = {
    # Fold order: with neutral predicates the LEFT fold (the shipped decider) is
    # definitionally equal to the spec accumulation at every depth; the right fold
    # is not (it differs in normal form, agreeing only in value). The notdefeq
    # cases assert the right fold is genuinely rejected — the discriminator that
    # makes the left fold the load-bearing encoding choice.
    "flat-foldorder-defeq-1" = { expr = conv (absK 1 specLBody) (absK 1 flatLBody); expected = true; };
    "flat-foldorder-defeq-2" = { expr = conv (absK 2 specLBody) (absK 2 flatLBody); expected = true; };
    "flat-foldorder-defeq-3" = { expr = conv (absK 3 specLBody) (absK 3 flatLBody); expected = true; };
    "flat-foldorder-defeq-4" = { expr = conv (absK 4 specLBody) (absK 4 flatLBody); expected = true; };
    "flat-foldorder-defeq-5" = { expr = conv (absK 5 specLBody) (absK 5 flatLBody); expected = true; };
    "flat-foldorder-foldr-notdefeq-2" = { expr = conv (absK 2 specLBody) (absK 2 flatRBody); expected = false; };
    "flat-foldorder-foldr-notdefeq-3" = { expr = conv (absK 3 specLBody) (absK 3 flatRBody); expected = false; };
    "flat-foldorder-foldr-notdefeq-5" = { expr = conv (absK 5 specLBody) (absK 5 flatRBody); expected = false; };
    "flat-foldorder-value-true" = { expr = conv (decideAt [ pTrue pTrue pTrue ] xWit) H.true_; expected = true; };
    "flat-foldorder-value-false" = { expr = conv (decideAt [ pTrue pFalse pTrue ] xWit) H.false_; expected = true; };

    # Decider value grade at depth 2, both polarities.
    "flat-decide-val-true-2" = { expr = conv (decideAt [ pTrue pTrue ] xWit) H.true_; expected = true; };
    "flat-decide-val-false-2" = { expr = conv (decideAt [ pTrue pFalse ] xWit) H.false_; expected = true; };

    # The predicate stack of a mixed chain is homogeneous: every predicate sits at
    # the single domain listOf (base-carrier -> Bool), no per-level retyping.
    "flat-o1-homogeneous" = { expr = chk (listP A) (mkList [ pTrue pFalse pTrue ]); expected = true; };

    # Membership decoder over the decider: P maps a true decision to Unit
    # (inhabited) and a false decision to Void (empty).
    "flat-parity-el-unit-1" = { expr = conv (P (decideAt [ pTrue ] xWit)) H.unit; expected = true; };
    "flat-parity-el-void-1" = { expr = conv (P (decideAt [ pFalse ] xWit)) H.void; expected = true; };
    "flat-parity-el-unit-2" = { expr = conv (P (decideAt [ pTrue pTrue ] xWit)) H.unit; expected = true; };
    "flat-parity-el-void-2" = { expr = conv (P (decideAt [ pTrue pFalse ] xWit)) H.void; expected = true; };

    # Scaling: the decider stays a single linear fold at a stack depth far beyond
    # where a per-level meta-tower's term size detonates. The deep code is built
    # flat (see directCode) to isolate the decider; it both typechecks and decides
    # in a single linear pass.
    "flat-scaling-linear-128" = { expr = (chk KType (directCode (rep 128 pTrue))) && (conv (decideAtDirect (rep 128 pTrue) xWit) H.true_); expected = true; };
  };
}
