# Type-checking kernel: Term constructors (Tm)
#
# Core term language with de Bruijn indices. All binding uses indices.
# Name annotations are cosmetic (for error messages only).
# Uses `tag` (not `_tag`) to distinguish from effect system nodes.
#
# Spec reference: kernel-spec.md §2
{ api, ... }:

let
  inherit (api) mk;

  # Smart constructors — validate structure at construction time.
  # Each returns an attrset with `tag` field.

  # -- Variables and binding --
  mkVar = i: { tag = "var"; idx = i; };
  mkLet = name: type: val: body: { tag = "let"; inherit name type val body; };
  mkAnn = term: type: { tag = "ann"; inherit term type; };

  # -- Functions --
  mkPi = name: domain: codomain: { tag = "pi"; inherit name domain codomain; };
  mkLam = name: domain: body: { tag = "lam"; inherit name domain body; };
  mkApp = fn: arg: { tag = "app"; inherit fn arg; };

  # -- Pairs --
  mkSigma = name: fst: snd: { tag = "sigma"; inherit name fst snd; };
  mkPair = fst: snd: ann: { tag = "pair"; inherit fst snd ann; };
  mkFst = pair: { tag = "fst"; inherit pair; };
  mkSnd = pair: { tag = "snd"; inherit pair; };

  # -- Natural numbers --
  mkNat = { tag = "nat"; };
  mkZero = { tag = "zero"; };
  mkSucc = pred: { tag = "succ"; inherit pred; };
  mkNatElim = motive: base: step: scrut:
    { tag = "nat-elim"; inherit motive base step scrut; };

  # -- Booleans --
  mkBool = { tag = "bool"; };
  mkTrue = { tag = "true"; };
  mkFalse = { tag = "false"; };
  mkBoolElim = motive: onTrue: onFalse: scrut:
    { tag = "bool-elim"; inherit motive onTrue onFalse scrut; };

  # -- Lists --
  mkList = elem: { tag = "list"; inherit elem; };
  mkNil = elem: { tag = "nil"; inherit elem; };
  mkCons = elem: head: tail: { tag = "cons"; inherit elem head tail; };
  mkListElim = elem: motive: nil: cons: scrut:
    { tag = "list-elim"; inherit elem motive nil cons scrut; };

  # -- Unit --
  mkUnit = { tag = "unit"; };
  mkTt = { tag = "tt"; };

  # -- Void --
  mkVoid = { tag = "void"; };
  mkAbsurd = type: term: { tag = "absurd"; inherit type term; };

  # -- Sum --
  mkSum = left: right: { tag = "sum"; inherit left right; };
  mkInl = left: right: term: { tag = "inl"; inherit left right term; };
  mkInr = left: right: term: { tag = "inr"; inherit left right term; };
  mkSumElim = left: right: motive: onLeft: onRight: scrut:
    { tag = "sum-elim"; inherit left right motive onLeft onRight scrut; };

  # -- Identity --
  mkEq = type: lhs: rhs: { tag = "eq"; inherit type lhs rhs; };
  mkRefl = { tag = "refl"; };
  mkJ = type: lhs: motive: base: rhs: eq:
    { tag = "j"; inherit type lhs motive base rhs eq; };

  # -- Universes --
  mkU = level: { tag = "U"; inherit level; };

in mk {
  doc = ''
    Core term constructors for the type-checking kernel.
    All terms use de Bruijn indices. `tag` field (not `_tag`)
    distinguishes kernel terms from effect system nodes.
  '';
  value = {
    inherit mkVar mkLet mkAnn;
    inherit mkPi mkLam mkApp;
    inherit mkSigma mkPair mkFst mkSnd;
    inherit mkNat mkZero mkSucc mkNatElim;
    inherit mkBool mkTrue mkFalse mkBoolElim;
    inherit mkList mkNil mkCons mkListElim;
    inherit mkUnit mkTt;
    inherit mkVoid mkAbsurd;
    inherit mkSum mkInl mkInr mkSumElim;
    inherit mkEq mkRefl mkJ;
    inherit mkU;
  };
  tests = {
    "var-tag" = { expr = (mkVar 0).tag; expected = "var"; };
    "var-idx" = { expr = (mkVar 3).idx; expected = 3; };
    "pi-tag" = { expr = (mkPi "x" mkNat mkNat).tag; expected = "pi"; };
    "lam-tag" = { expr = (mkLam "x" mkNat (mkVar 0)).tag; expected = "lam"; };
    "app-tag" = { expr = (mkApp (mkVar 0) mkZero).tag; expected = "app"; };
    "sigma-tag" = { expr = (mkSigma "x" mkNat mkBool).tag; expected = "sigma"; };
    "pair-tag" = { expr = (mkPair mkZero mkTrue mkNat).tag; expected = "pair"; };
    "fst-tag" = { expr = (mkFst (mkVar 0)).tag; expected = "fst"; };
    "snd-tag" = { expr = (mkSnd (mkVar 0)).tag; expected = "snd"; };
    "nat-tag" = { expr = mkNat.tag; expected = "nat"; };
    "zero-tag" = { expr = mkZero.tag; expected = "zero"; };
    "succ-tag" = { expr = (mkSucc mkZero).tag; expected = "succ"; };
    "succ-pred" = { expr = (mkSucc mkZero).pred.tag; expected = "zero"; };
    "nat-elim-tag" = {
      expr = (mkNatElim (mkVar 0) mkZero (mkVar 1) mkZero).tag;
      expected = "nat-elim";
    };
    "bool-tag" = { expr = mkBool.tag; expected = "bool"; };
    "true-tag" = { expr = mkTrue.tag; expected = "true"; };
    "false-tag" = { expr = mkFalse.tag; expected = "false"; };
    "list-tag" = { expr = (mkList mkNat).tag; expected = "list"; };
    "nil-tag" = { expr = (mkNil mkNat).tag; expected = "nil"; };
    "cons-tag" = { expr = (mkCons mkNat mkZero (mkNil mkNat)).tag; expected = "cons"; };
    "unit-tag" = { expr = mkUnit.tag; expected = "unit"; };
    "tt-tag" = { expr = mkTt.tag; expected = "tt"; };
    "void-tag" = { expr = mkVoid.tag; expected = "void"; };
    "absurd-tag" = { expr = (mkAbsurd mkNat (mkVar 0)).tag; expected = "absurd"; };
    "sum-tag" = { expr = (mkSum mkNat mkBool).tag; expected = "sum"; };
    "inl-tag" = { expr = (mkInl mkNat mkBool mkZero).tag; expected = "inl"; };
    "inr-tag" = { expr = (mkInr mkNat mkBool mkTrue).tag; expected = "inr"; };
    "eq-tag" = { expr = (mkEq mkNat mkZero mkZero).tag; expected = "eq"; };
    "refl-tag" = { expr = mkRefl.tag; expected = "refl"; };
    "j-tag" = {
      expr = (mkJ mkNat mkZero (mkVar 0) (mkVar 1) mkZero mkRefl).tag;
      expected = "j";
    };
    "U-tag" = { expr = (mkU 0).tag; expected = "U"; };
    "U-level" = { expr = (mkU 1).level; expected = 1; };
    "let-tag" = { expr = (mkLet "x" mkNat mkZero (mkVar 0)).tag; expected = "let"; };
    "ann-tag" = { expr = (mkAnn mkZero mkNat).tag; expected = "ann"; };
  };
}
