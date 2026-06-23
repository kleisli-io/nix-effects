# End-to-end soundness of the kernel-internalized refinement surface.
#
# The authoritative check of an internalized refinement derives its decision
# from a kernel predicate stack, so its faithfulness rests on a small set of
# load-bearing properties pinned here:
#
#   - the int_ literal bridge is order- and equality-faithful: the host-backed
#     intLe/intEq primitives decide bridged literals exactly as the host
#     comparison does, across sign quadrants and the zero boundary, at O(1)
#     regardless of magnitude;
#   - predicate-stack composition is conjunction, both as the kernel decision
#     of the composed code and as the derived guard (the one mechanized fold
#     lemma in flat-faithfulness.nix supplies the AND-accumulation for free);
#   - the authoritative check equals the host carrier gate conjoined with the
#     kernel decision at the bridged value;
#   - the kernel decision of a compound's carrier agrees with its structural
#     check against ground truth, over record / list / option / sum / variant;
#   - the degradation arms fail closed: an opaque guard yields no internalized
#     code, and an over-approximate carrier decides everything;
#   - the kernel decision, the collecting validate run, and the strict validate
#     run agree on membership.
{ self, fx, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  Cv = fx.tc.conv;
  R = self.reflect;
  inherit (self.ktype) KType decide andB;

  app = H.app;
  true_ = H.true_;
  false_ = H.false_;
  intLit = H.intLit;
  ev = h: E.eval [ ] (H.elab h);
  conv = a: b: Cv.conv 0 (ev a) (ev b);
  chk = ty: h: !((H.checkHoas ty h) ? error);
  D = fx.tc.elaborate.decide;

  F = fx.types.foundation;
  Ref = fx.types.refinement;
  Con = fx.types.constructors;
  FP = fx.types.primitives;

  boolLit = b: if b then true_ else false_;
  every = f: xs: builtins.all f xs;

  # Decision of an int_-carriered code at a bridged Nix integer.
  kdecAt = kt: v: conv (app (decide kt) (intLit v)) true_;

  # Primitive-bridge faithfulness over a signed grid: the int_ order/equality
  # primitives decide bridged literals exactly as the host <=/==.
  pairGrid = [ (-2) (-1) 0 1 2 ];
  intLeFaithful = a: b: conv (H.intLe (intLit a) (intLit b)) (boolLit (a <= b));
  intEqFaithful = a: b: conv (H.intEq (intLit a) (intLit b)) (boolLit (a == b));

  # Stack composition: a nonnegative bound conjoined with a symmetric range.
  w1 = R.intNonNegative;
  w2 = R.intInRange (-5) 5;
  comp = R.andKP w1 w2;
  comp3 = R.andKP comp (R.intEq 3);
  compGrid = [ (-7) (-5) (-1) 0 3 5 6 ];
  decideCompose = v:
    conv
      (app (decide (R.ktypeOf comp)) (intLit v))
      (andB
        (app (decide (R.ktypeOf w1)) (intLit v))
        (app (decide (R.ktypeOf w2)) (intLit v)));
  guardCompose = v:
    (R.deriveGuard comp) v == ((R.deriveGuard w1 v) && (R.deriveGuard w2 v));
  guardCompose3 = v:
    (R.deriveGuard comp3) v == ((R.deriveGuard comp v) && (R.deriveGuard (R.intEq 3) v));

  # Authoritative check law on internalized refinements.
  posInt = F.mkType { name = "PosInt"; kernelType = H.int_; guard = R.intPositive; };
  Bounded = Ref.refined "Bounded" (Ref.refined "Pos" FP.Int Ref.positiveInt) (Ref.inRangeInt 1 10);
  signedGrid = [ (-3) (-2) (-1) 0 1 2 3 ];
  checkLaw = T: v: (T.check v) == (builtins.isInt v && kdecAt T.ktype v);

  # The kernel decider, taken directly (not via the derived guard), agrees with
  # the host predicate. A bare carrier decides constant-true (empty stack); a
  # refinement decides its predicate.
  iotaInt = R.reflect H.int_;
  posIntCode = R.reflectRefine H.int_ R.positiveInt;
  rangeIntCode = R.reflectRefine H.int_ (R.inRangeInt (-2) 3);
  carrierGrid = [ (-3) 0 5 "x" true null ];

  # Compound carriers with ground-truth membership grids.
  Rec = Con.Record { n = FP.Int; b = FP.Bool; };
  recGrid = [
    { v = { n = 1; b = true; }; ok = true; }
    { v = { n = 0; b = false; }; ok = true; }
    { v = { n = "x"; b = true; }; ok = false; }
    { v = { n = 1; }; ok = false; }
    { v = 5; ok = false; }
  ];
  Lst = Con.ListOf FP.Int;
  lstGrid = [
    { v = [ 1 2 3 ]; ok = true; }
    { v = [ ]; ok = true; }
    { v = [ 1 "x" 3 ]; ok = false; }
    { v = 5; ok = false; }
  ];
  Myb = Con.Maybe FP.Int;
  mybGrid = [
    { v = null; ok = true; }
    { v = 42; ok = true; }
    { v = "x"; ok = false; }
  ];
  Eth = Con.Either FP.Int FP.Bool;
  ethGrid = [
    { v = { _tag = "Left"; value = 1; }; ok = true; }
    { v = { _tag = "Right"; value = true; }; ok = true; }
    { v = { _tag = "Left"; value = "x"; }; ok = false; }
    { v = { _tag = "Other"; value = 1; }; ok = false; }
    { v = 5; ok = false; }
  ];
  Var = Con.Variant { a = FP.Int; b = FP.Bool; };
  varGrid = [
    { v = { _tag = "a"; value = 1; }; ok = true; }
    { v = { _tag = "b"; value = true; }; ok = true; }
    { v = { _tag = "a"; value = "x"; }; ok = false; }
    { v = { _tag = "c"; value = 1; }; ok = false; }
  ];
  soundDecide = T: grid: every (g: D T._kernel g.v == g.ok) grid;
  soundCheck = T: grid: every (g: T.check g.v == g.ok) grid;

  # A raw-lambda refinement: the kernel sees the base carrier only.
  RawNat = Ref.refined "Nat" FP.Int (x: x >= 0);
  clause3Grid = [
    { v = 5; base = true; guard = true; }
    { v = (-1); base = true; guard = false; }
    { v = "x"; base = false; guard = false; }
  ];

  # An over-approximate type: no carrier, decides everything.
  Appr = F.mkType { name = "Appr"; };
  apprGrid = [ 5 "x" null [ 1 ] { a = 1; } true ];

  # Kernel decision, collecting validate, and strict validate must agree.
  collectingPass = T: v:
    (fx.trampoline.handle
      { handlers = fx.effects.typecheck.collecting; state = [ ]; }
      (T.validate v)).state == [ ];
  # The strict policy's rejection throws lazily inside the result; force it.
  strictNoThrow = T: v:
    (builtins.tryEval
      (builtins.deepSeq
        (fx.trampoline.handle
          { handlers = fx.effects.typecheck.strict; state = [ ]; }
          (T.validate v))
        true)).success;
  agree = T: grid: every
    (g:
      let pass = collectingPass T g.v; in
      pass == (strictNoThrow T g.v) && pass == g.ok && (D T._kernel g.v == g.ok))
    grid;
  # For a refinement the kernel carrier sees only base-hood, so the 3-way law
  # closes on the guarded `.check`, not `D T._kernel`.
  agreeRefined = T: grid: every
    (g:
      let pass = collectingPass T g.v; in
      pass == (strictNoThrow T g.v) && pass == g.ok && (T.check g.v == g.ok))
    grid;

  # A String literal-enum refinement, internalized via its kernel witness.
  stringLit = H.stringLit;
  StrEnum = Ref.refined "StrEnum" FP.String (Ref.oneOfStr [ "a" "b" ]);
  kdecAtStr = kt: v: conv (app (decide kt) (stringLit v)) true_;
  strGrid = [ "a" "b" "c" "" ];
  strLitFaithful = a: b: conv (H.strEq (stringLit a) (stringLit b)) (boolLit (a == b));
  posIntGrid = [
    { v = 1; ok = true; }
    { v = 5; ok = true; }
    { v = 0; ok = false; }
    { v = (-3); ok = false; }
    { v = "x"; ok = false; }
  ];
  enumGrid = [
    { v = "a"; ok = true; }
    { v = "b"; ok = true; }
    { v = "c"; ok = false; }
    { v = 5; ok = false; }
  ];
  # A nested/range refinement (positive, then bounded to [1,10]).
  boundedGrid = [
    { v = 1; ok = true; }
    { v = 5; ok = true; }
    { v = 10; ok = true; }
    { v = 0; ok = false; }
    { v = 11; ok = false; }
    { v = (-3); ok = false; }
    { v = "x"; ok = false; }
  ];
  # Guarded compounds: a child type carries an internalized refinement. The
  # child guard is invisible to the compound's structural kernel carrier, so
  # the 3-way law closes on `.check`, not `D T._kernel`.
  Pos = Ref.refined "Pos" FP.Int Ref.positiveInt;
  ListOfPos = Con.ListOf Pos;
  listOfPosGrid = [
    { v = [ 1 2 3 ]; ok = true; }
    { v = [ ]; ok = true; }
    { v = [ 1 0 3 ]; ok = false; }
    { v = [ 1 (-2) ]; ok = false; }
    { v = [ 1 "x" ]; ok = false; }
    { v = 5; ok = false; }
  ];
  RecordOfPos = Con.Record { p = Pos; b = FP.Bool; };
  recordOfPosGrid = [
    { v = { p = 1; b = true; }; ok = true; }
    { v = { p = 0; b = true; }; ok = false; }
    { v = { p = 5; b = "x"; }; ok = false; }
    { v = { p = 1; }; ok = false; }
    { v = 5; ok = false; }
  ];
  EitherOfPos = Con.Either Pos FP.Bool;
  eitherOfPosGrid = [
    { v = { _tag = "Left"; value = 1; }; ok = true; }
    { v = { _tag = "Right"; value = true; }; ok = true; }
    { v = { _tag = "Left"; value = 0; }; ok = false; }
    { v = { _tag = "Other"; value = 1; }; ok = false; }
    { v = 5; ok = false; }
  ];
  VariantOfPos = Con.Variant { a = Pos; b = FP.Bool; };
  variantOfPosGrid = [
    { v = { _tag = "a"; value = 1; }; ok = true; }
    { v = { _tag = "b"; value = true; }; ok = true; }
    { v = { _tag = "a"; value = 0; }; ok = false; }
    { v = { _tag = "c"; value = 1; }; ok = false; }
  ];
in
{
  scope = { };
  tests = {
    # The int_ literal bridge is order- and equality-faithful: the host-backed
    # intLe/intEq primitives decide bridged literals exactly as the host
    # comparison, over every sign quadrant and the zero boundary.
    "bridge-intle-faithful" = { expr = every (a: every (b: intLeFaithful a b) pairGrid) pairGrid; expected = true; };
    "bridge-inteq-faithful" = { expr = every (a: every (b: intEqFaithful a b) pairGrid) pairGrid; expected = true; };
    "bridge-intle-negative" = { expr = conv (H.intLe (intLit (-3)) (intLit (-1))) true_; expected = true; };
    "bridge-inteq-cross-sign" = { expr = conv (H.intEq (intLit 2) (intLit (-2))) false_; expected = true; };
    # The O(1) intLit bridge decides a 10^8-magnitude positivity check with no
    # unary tower — the regression this internalization exists to prevent.
    "bridge-intle-large-magnitude" = { expr = conv (H.intLe (intLit 1) (intLit 100000000)) true_; expected = true; };

    # Stack composition is conjunction, as a kernel decision and as the guard.
    "compose-decide-conjoins" = { expr = every decideCompose compGrid; expected = true; };
    "compose-guard-conjoins" = { expr = every guardCompose compGrid; expected = true; };
    "compose-guard-three-deep" = { expr = every guardCompose3 [ 3 0 (-6) 100 ]; expected = true; };
    "compose-ktype-checks" = { expr = chk KType (R.ktypeOf comp3); expected = true; };

    # The authoritative check equals the host carrier gate conjoined with the
    # kernel decision at the bridged value.
    "check-law-positive" = { expr = every (checkLaw posInt) signedGrid; expected = true; };
    "check-law-noninteger" = { expr = posInt.check "x" == false; expected = true; };
    "check-law-bounded-composition" = { expr = every (checkLaw Bounded) signedGrid; expected = true; };
    "check-law-internalized-ktype-nonnull" = { expr = posInt.ktype != null; expected = true; };

    # Kernel decider == host predicate, directly. A bare reflect decides true; a
    # refinement tracks its predicate; the int_ carrier gate is integer-hood.
    "bridge-iota-decides-true" = { expr = every (v: kdecAt iotaInt v) signedGrid; expected = true; };
    "bridge-refine-decides-positive" = { expr = every (v: kdecAt posIntCode v == (v > 0)) signedGrid; expected = true; };
    "bridge-refine-decides-range" = { expr = every (v: kdecAt rangeIntCode v == (v >= (-2) && v <= 3)) signedGrid; expected = true; };
    "bridge-host-carrier-is-isint" = { expr = every (v: D H.int_ v == builtins.isInt v) carrierGrid; expected = true; };

    # The kernel decision of a compound carrier agrees with its structural check
    # against ground truth; the structural check itself agrees with ground truth.
    "decide-agrees-record" = { expr = soundDecide Rec recGrid; expected = true; };
    "check-agrees-record" = { expr = soundCheck Rec recGrid; expected = true; };
    "decide-agrees-listof" = { expr = soundDecide Lst lstGrid; expected = true; };
    "check-agrees-listof" = { expr = soundCheck Lst lstGrid; expected = true; };
    "decide-agrees-maybe" = { expr = soundDecide Myb mybGrid; expected = true; };
    "check-agrees-maybe" = { expr = soundCheck Myb mybGrid; expected = true; };
    "decide-agrees-either" = { expr = soundDecide Eth ethGrid; expected = true; };
    "check-agrees-either" = { expr = soundCheck Eth ethGrid; expected = true; };
    "decide-agrees-variant" = { expr = soundDecide Var varGrid; expected = true; };
    "check-agrees-variant" = { expr = soundCheck Var varGrid; expected = true; };

    # A refinement's check conjoins base and predicate; the kernel carrier sees
    # the base only (the opaque guard is invisible to it).
    "refined-check-conjoins-guard" = { expr = every (g: RawNat.check g.v == (g.base && g.guard)) clause3Grid; expected = true; };
    "refined-kernel-ignores-guard" = { expr = every (g: D RawNat._kernel g.v == g.base) clause3Grid; expected = true; };

    # An over-approximate type carries the top carrier and decides everything.
    "approximate-carrier-is-top" = { expr = conv Appr._kernel H.any; expected = true; };
    "approximate-decides-true" = { expr = every (v: D Appr._kernel v == true) apprGrid; expected = true; };

    # Degradation: an opaque guard (raw lambda, or a non-internalizable string
    # predicate) yields no internalized code.
    "degrade-rawlambda-no-ktype" = { expr = (Ref.refined "P" FP.Int (x: x > 0)).ktype == null; expected = true; };
    "degrade-string-predicate-no-ktype" = { expr = (Ref.refined "NE" FP.String Ref.nonEmpty).ktype == null; expected = true; };

    # Kernel decision, collecting validate, and strict validate agree.
    "decide-validate-handler-agree-record" = { expr = agree Rec recGrid; expected = true; };
    "decide-validate-handler-agree-listof" = { expr = agree Lst lstGrid; expected = true; };

    # The string-literal bridge is equality-faithful: strEq decides bridged
    # literals exactly as host string equality, over a grid incl. the empty
    # string and a non-member.
    "bridge-strlit-faithful" = { expr = every (a: every (b: strLitFaithful a b) strGrid) strGrid; expected = true; };
    # Kernel decider of a String literal-enum code == host membership, directly.
    "bridge-stronof-decides-membership" = {
      expr = every (v: kdecAtStr (R.ktypeOf (R.strOneOf [ "a" "b" ])) v == builtins.elem v [ "a" "b" ]) strGrid;
      expected = true;
    };
    # A witness-internalized String refinement: authoritative check == host
    # ground truth, ktype non-null, and decide/collecting/strict agree.
    "check-law-strenum" = { expr = every (v: StrEnum.check v == builtins.elem v [ "a" "b" ]) strGrid; expected = true; };
    "check-law-strenum-noncarrier" = { expr = StrEnum.check 5 == false; expected = true; };
    "check-law-strenum-ktype-nonnull" = { expr = StrEnum.ktype != null; expected = true; };
    "agree-refined-posint" = { expr = agreeRefined posInt posIntGrid; expected = true; };
    "agree-refined-strenum" = { expr = agreeRefined StrEnum enumGrid; expected = true; };
    # The 3-way law over a nested/range refinement and over a guarded compound
    # (a list of a refined Int) — collecting/strict/`.check` all agree.
    "agree-refined-bounded" = { expr = agreeRefined Bounded boundedGrid; expected = true; };
    "agree-refined-listof-guarded" = { expr = agreeRefined ListOfPos listOfPosGrid; expected = true; };
    "agree-refined-record-guarded" = { expr = agreeRefined RecordOfPos recordOfPosGrid; expected = true; };
    "agree-refined-either-guarded" = { expr = agreeRefined EitherOfPos eitherOfPosGrid; expected = true; };
    "agree-refined-variant-guarded" = { expr = agreeRefined VariantOfPos variantOfPosGrid; expected = true; };
  };
}
