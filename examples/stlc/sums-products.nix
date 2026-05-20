# STLC sums and products surface example.
#
# This file extends `core.nix` with the next ordinary typed-language forms:
#
#   Product type:  A * B
#   Product term:  (a, b)
#   Projection:    fst p, snd p
#
#   Sum type:      A + B
#   Sum terms:     inl a, inr b
#   Case split:    case s of inl x -> ... | inr y -> ...
#
# The implementation follows the same rule as the core example: the surface
# adds source-language syntax and diagnostics, while the existing HOAS and
# kernel checker provide the semantics. Products elaborate to Sigma, sums
# elaborate to the generated `SumDT` encoding exposed by `H.sum`, and case
# analysis elaborates to `H.sumElim`.
{ fx, core, ... }:

let
  H = fx.types.hoas;
  S = fx.surface;
  Core = core.stlc;

  # Surface definition for the product/sum fragment.
  #
  # The constructors here intentionally do not duplicate the core language
  # constructors. Nested terms can freely mix registries: a product projection
  # can contain a core annotation, and the recursive HOAS elaborator dispatches
  # each node through the registry attached to that node.
  surface = S.defineSurface {
    name = "STLC-SumsProducts";
    description = "STLC surface extension for products and sums.";
    constructors = {
      # Dependent pair type:
      #
      #   sigma "x" A (x: B x)
      #
      # The non-dependent product `A * B` below is just
      # `sigma "_" A (_: B)`.
      sigma = {
        tag = "stlc.sigma";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.sigma h.name h.fst h.snd);
      };

      # Pair introduction `(a, b)`.
      pair = {
        tag = "stlc.pair";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.pair h.fst h.snd);
      };

      # Product projections. These infer through annotated pairs in the
      # examples below, so errors come from the normal kernel projection rules.
      fst = {
        tag = "stlc.fst";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.fst_ h.pair);
      };
      snd = {
        tag = "stlc.snd";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.snd_ h.pair);
      };

      # Binary sum type `A + B`.
      sum = {
        tag = "stlc.sum";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.sum h.left h.right);
      };

      # Sum introductions. The left and right types are explicit so each
      # injection remains inferable enough for the underlying generated
      # datatype constructors.
      inl = {
        tag = "stlc.inl";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.inlAtExplicit 0 h.left h.right h.term);
      };
      inr = {
        tag = "stlc.inr";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.inrAtExplicit 0 h.left h.right h.term);
      };

      # Case analysis into a non-dependent result type.
      #
      # `H.sumElim` expects a motive over the scrutinee. For the STLC fragment,
      # the motive is constant: every branch returns `result`.
      case = {
        tag = "stlc.case";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth
            (hoas.sumElim 0 h.left h.right
              (hoas.lam "_" (hoas.sum h.left h.right) (_: h.result))
              (hoas.lam "left" h.left h.onLeft)
              (hoas.lam "right" h.right h.onRight)
              h.scrut);
      };
    };
  };

  # Smart constructors for this fragment. They intentionally mirror ordinary
  # STLC notation while still making dependencies explicit where HOAS needs
  # them.
  sigma = name: fst: snd: surface.mk "sigma" { inherit name fst snd; };
  prod = fst: snd: sigma "_" fst (_: snd);
  pair = fst: snd: surface.mk "pair" { inherit fst snd; };
  fst_ = pair: surface.mk "fst" { inherit pair; };
  snd_ = pair: surface.mk "snd" { inherit pair; };

  sum = left: right: surface.mk "sum" { inherit left right; };
  inl = left: right: term: surface.mk "inl" { inherit left right term; };
  inr = left: right: term: surface.mk "inr" { inherit left right term; };
  case_ = left: right: result: scrut: onLeft: onRight:
    surface.mk "case" { inherit left right result scrut onLeft onRight; };

  # Root checking for terms from this extension. Core STLC terms keep their own
  # registry, so this checker can accept mixed terms built from both modules.
  check = term: expectedType: position:
    S.elaborate {
      inherit surface term expectedType position;
    };

  natBoolProduct = prod H.nat H.bool;
  natBoolPair = pair H.zero H.true_;
  natBoolPairAnn = Core.ann natBoolPair natBoolProduct;

  natBoolSum = sum H.nat H.bool;
  leftZero = inl H.nat H.bool H.zero;
  rightTrue = inr H.nat H.bool H.true_;
  leftZeroAnn = Core.ann leftZero natBoolSum;
in
rec {
  __example = {
    title = "STLC Sums and Products";
    description = "Extend the STLC surface with product and sum syntax while reusing the existing HOAS kernel.";
    introduction = ''
      This extension adds ordinary product and coproduct forms. The surface
      layer still only translates syntax: products elaborate to Sigma, sums
      elaborate to the generated sum datatype, and case analysis elaborates to
      `sumElim`.
    '';
    sections = [
      {
        title = "Products";
        prose = ''
          A product type is a non-dependent Sigma. Pair introduction and
          projections reuse the existing HOAS pair, fst, and snd terms.
        '';
        code = ''
          sigma = name: fst: snd: surface.mk "sigma" { inherit name fst snd; };
          prod = fst: snd: sigma "_" fst (_: snd);
          pair = fst: snd: surface.mk "pair" { inherit fst snd; };
          fst_ = pair: surface.mk "fst" { inherit pair; };
          snd_ = pair: surface.mk "snd" { inherit pair; };

          natBoolProduct = prod H.nat H.bool;
          natBoolPair = pair H.zero H.true_;
          natBoolPairAnn = Core.ann natBoolPair natBoolProduct;
        '';
        tests = [
          "stlcProductPairChecks"
          "stlcProductProjectionChecks"
          "stlcBadProjectionHasSurfaceBlame"
        ];
      }
      {
        title = "Sums";
        prose = ''
          Sum injections keep both sides of the type explicit so the generated
          datatype constructors are inferable. Case analysis uses a constant
          motive for the STLC fragment.
        '';
        code = ''
          sum = left: right: surface.mk "sum" { inherit left right; };
          inl = left: right: term: surface.mk "inl" { inherit left right term; };
          inr = left: right: term: surface.mk "inr" { inherit left right term; };
          case_ = left: right: result: scrut: onLeft: onRight:
            surface.mk "case" { inherit left right result scrut onLeft onRight; };

          stlcSumCaseChecks =
            let
              term = case_ H.nat H.bool H.nat leftZeroAnn
                (n: n)
                (_: H.zero);
              r = check term H.nat { path = [ "sum" "case" ]; };
            in
            !(r ? error);
        '';
        tests = [
          "stlcSumInjectionChecks"
          "stlcSumCaseChecks"
          "stlcBadBranchHasSurfaceBlame"
        ];
      }
    ];
  };

  # Public extension API. It includes the core STLC vocabulary plus the
  # product/sum forms from this file.
  stlc = Core // {
    inherit surface sigma prod pair fst_ snd_ sum inl inr case_;
  };

  # `(0, true)` checks against `Nat * Bool`.
  stlcProductPairChecks =
    let r = check natBoolPair natBoolProduct { path = [ "product" "pair" ]; };
    in !(r ? error) && r.tag == "pair";

  # `fst ((0, true) : Nat * Bool)` checks against Nat, and `snd` checks
  # against Bool. The annotation gives projections an inferable pair type.
  stlcProductProjectionChecks =
    let
      fstResult = check (fst_ natBoolPairAnn) H.nat { path = [ "product" "fst" ]; };
      sndResult = check (snd_ natBoolPairAnn) H.bool { path = [ "product" "snd" ]; };
    in
    !(fstResult ? error)
    && !(sndResult ? error)
    && fstResult.tag == "fst"
    && sndResult.tag == "snd";

  # Both injections check against `Nat + Bool`.
  stlcSumInjectionChecks =
    let
      leftResult = check leftZero natBoolSum { path = [ "sum" "inl" ]; };
      rightResult = check rightTrue natBoolSum { path = [ "sum" "inr" ]; };
    in
    !(leftResult ? error)
    && !(rightResult ? error)
    && leftResult.tag == "desc-con"
    && rightResult.tag == "desc-con";

  # `case (inl 0) of inl n -> n | inr b -> 0` checks against Nat.
  stlcSumCaseChecks =
    let
      term = case_ H.nat H.bool H.nat leftZeroAnn
        (n: n)
        (_: H.zero);
      r = check term H.nat { path = [ "sum" "case" ]; };
    in
      !(r ? error);

  # Projecting from a Nat is invalid. Surface finalization attaches the source
  # position to the lower-level checker error.
  stlcBadProjectionHasSurfaceBlame =
    let
      r = check (fst_ (Core.ann H.zero H.nat)) H.nat
        { path = [ "bad" "projection" ]; };
    in
    (r ? error)
    && (r.position or null) == { path = [ "bad" "projection" ]; };

  # A branch returning Bool where the case result is Nat is invalid, and the
  # surface position identifies the case expression as the failing source form.
  stlcBadBranchHasSurfaceBlame =
    let
      term = case_ H.nat H.bool H.nat leftZeroAnn
        (n: n)
        (_: H.true_);
      r = check term H.nat { path = [ "bad" "branch" ]; };
    in
    (r ? error)
    && (r.position or null) == { path = [ "bad" "branch" ]; };
}
