# STLC refinements and diagnostics surface example.
#
# This file adds a small refinement layer to the STLC examples:
#
#   Type syntax:  { x : A | P x }
#   Term syntax:  refine T v proof
#   Forget:       forget r
#
# The underlying HOAS library already has `refinementPred`. It represents a
# refinement as a dependent pair:
#
#   Sigma (x : A) (Dec (P x))
#
# A value therefore contains both the witness `x` and a positive decision for
# the predicate at that witness. Users supply the ordinary proof; the surface
# wraps it as `yes (P x) proof` because `refinementPred` stores a decidable
# predicate. This example does not add new kernel rules. It only gives the
# existing carrier a source-language spelling and a more readable surface
# error when the proof component does not match the witness.
#
# Diagnostics are the second half of the example. The tests distinguish three
# user-facing failure classes:
#
#   surface.unsolved-implicit       omitted information could not be inferred
#   ordinary checker error          the kernel rejected an ordinary STLC term
#   stlc.refinement-failure         a refinement witness/proof pair mismatched
#
# Keeping those cases distinct matters for editors and command-line tools:
# they can offer different fixes for "add an annotation", "fix the term", and
# "supply a proof for the exact refined value".
{ fx, core, ... }:

let
  H = fx.types.hoas;
  S = fx.surface;
  Core = core.stlc;

  refinementShape = expectedType:
    if builtins.isAttrs expectedType
      && (expectedType._htag or null) == "stlc.refinement"
    then {
      name = expectedType.name or "anonymous refinement";
      domain = expectedType.domain;
      predicate = expectedType.predicate;
    }
    else null;

  expectedRefinementError = context: {
    error = {
      msg = "refine requires a refinement type";
      kind = "stlc.expected-refinement";
      position = context.position or null;
      expectedType = context.expectedType or null;
      term = context.term or null;
    };
    msg = "refine requires a refinement type";
    kind = "stlc.expected-refinement";
    position = context.position or null;
  };

  refinementFailureError = context: checker: shape: {
    error = {
      msg = "refinement witness does not match predicate";
      kind = "stlc.refinement-failure";
      position = context.position or null;
      surface = context.surface or "STLC-RefinementsDiagnostics";
      refinement = shape.name;
      checker = {
        msg = checker.msg or null;
        expected = checker.expected or null;
        got = checker.got or null;
      };
      term = context.term or null;
    };
    msg = "refinement witness does not match predicate";
    kind = "stlc.refinement-failure";
    position = context.position or null;
  };

  # Refinement introduction gets a small surface pre-check. The explicit type
  # argument supplies the predicate needed to turn a proof into a positive
  # decision, and an expected type can still catch accidental mismatches.
  refineFromExpected = { context, type, value, proof, hoas ? H }:
    let
      expectedType = context.expectedType or null;
      typeShape = refinementShape type;
      expectedShape = if expectedType == null then null else refinementShape expectedType;
      targetShape = if expectedShape != null then expectedShape else typeShape;
      term =
        if typeShape == null
        then null
        else
          let proofTy = typeShape.predicate value; in
          hoas.pair value (hoas.yes proofTy (hoas.ann proof proofTy));
    in
    if typeShape == null || (expectedType != null && expectedShape == null)
    then expectedRefinementError context
    else
      let
        target = hoas.refinementPred targetShape.domain targetShape.predicate;
        checked = hoas.checkHoas target term;
      in
      if builtins.isAttrs checked && checked ? error
      then refinementFailureError context checked targetShape
      else { inherit term checked; };

  surface = S.defineSurface {
    name = "STLC-RefinementsDiagnostics";
    description = "STLC surface extension for refinements and diagnostics.";
    constructors = {
      # Refinement type:
      #
      #   refinement "AtLeastOne" Nat (n: Le 1 n)
      #
      # The predicate is a Nix function from a HOAS variable to a HOAS
      # proposition. That matches the convention used by `sigma`, `pi`, and
      # `lam` throughout the HOAS surface.
      refinement = {
        tag = "stlc.refinement";
        handler = { depth, h, lower, hoas, ... }:
          lower depth (hoas.refinementPred h.domain h.predicate);
      };

      # Refinement introduction:
      #
      #   refine AtLeastOne one proofThatOneSatisfiesPredicate
      #
      # At the root, an expected refinement type lets the handler report a
      # source-language diagnostic before the low-level Sigma mismatch leaks
      # through. Away from the root, the explicit refinement type gives the
      # handler enough information to build the positive decision.
      refine = {
        tag = "stlc.refine";
        handler = { context, depth, h, lower, hoas, ... }:
          let
            r = refineFromExpected {
              inherit context hoas;
              inherit (h) type value proof;
            };
          in
          if r ? error then r else lower depth r.term;
      };

      # Forgetting a refinement is first projection from the dependent pair.
      #
      # The proof stays in the term for checking, but consumers that only need
      # the underlying value can project it out with ordinary Sigma reduction.
      forget = {
        tag = "stlc.refinement-forget";
        handler = { depth, h, lower, hoas, ... }:
          lower depth (hoas.fst_ h.term);
      };
    };
  };

  refinement = name: domain: predicate:
    surface.mk "refinement" { inherit name domain predicate; };
  refine = type: value: proof:
    surface.mk "refine" { inherit type value proof; };
  forget = term:
    surface.mk "forget" { inherit term; };

  check = term: expectedType: position:
    S.elaborate {
      inherit surface term expectedType position;
    };

  elaborate = term: position:
    S.elaborate {
      inherit surface term position;
    };

  one = H.succ H.zero;

  # AtLeastOne = { n : Nat | 1 <= n }.
  atLeastOneNat =
    refinement "AtLeastOne" H.nat (n: H.le one n);

  # A proof that 1 <= 1. `refine` wraps this as an inhabitant of
  # `Dec (1 <= 1)`, which is the second component expected by
  # `refinementPred`.
  oneLeOne = H.leSS H.leZ;
  oneAtLeastOne = refine atLeastOneNat one oneLeOne;

  # The witness is zero, but the proof is still for one. The refinement
  # checker must reject that mismatch and report it at the source term.
  zeroWithOneProof = refine atLeastOneNat H.zero oneLeOne;

  annotatedOneAtLeastOne = Core.ann oneAtLeastOne atLeastOneNat;
in
rec {
  __example = {
    title = "STLC Refinements and Diagnostics";
    description = "Add refinement syntax to the STLC surface while preserving source-level diagnostic classes.";
    introduction = ''
      The refinement surface gives a source-language spelling to the HOAS
      refinement carrier and preserves diagnostic intent. A missing annotation,
      an ordinary type mismatch, and a failed refinement proof are distinct
      failures.
    '';
    sections = [
      {
        title = "Refinement values";
        prose = ''
          A refinement type is represented as a dependent pair whose second
          component is a positive decision. The surface `refine` form packages
          the witness and proof into that carrier.
        '';
        code = ''
          atLeastOneNat =
            refinement "AtLeastOne" H.nat (n: H.le one n);

          oneLeOne = H.leSS H.leZ;
          oneAtLeastOne = refine atLeastOneNat one oneLeOne;

          stlcRefinementValueChecks =
            let
              r = check oneAtLeastOne atLeastOneNat
                { path = [ "refinement" "value" ]; };
            in
            !(r ? error) && r.tag == "pair";
        '';
        tests = [
          "stlcRefinementTypeChecks"
          "stlcRefinementValueChecks"
          "stlcRefinementForgetChecks"
        ];
      }
      {
        title = "Refinement failure";
        prose = ''
          If the witness and proof do not match, the surface reports a
          refinement-specific diagnostic instead of exposing the raw Sigma
          mismatch as the main error.
        '';
        code = ''
          zeroWithOneProof = refine atLeastOneNat H.zero oneLeOne;

          stlcBadRefinementHasSurfaceDiagnostic =
            let
              position = { path = [ "bad" "refinement" ]; };
              r = check zeroWithOneProof atLeastOneNat position;
            in
            (r ? error)
            && (r.kind or null) == "stlc.refinement-failure"
            && (r.position or null) == position;
        '';
        tests = [
          "stlcBadRefinementHasSurfaceDiagnostic"
        ];
      }
      {
        title = "Diagnostic classes";
        prose = ''
          The examples keep three failure classes separate: unsolved implicit
          information, ordinary checker errors, and refinement failures. That
          gives editors and command-line tools enough structure to suggest the
          right repair.
        '';
        code = ''
          stlcDiagnosticUnsolvedImplicitIsDistinct =
            let
              position = { path = [ "diagnostic" "implicit" ]; };
              r = elaborate (Core.holeLam "x" (x: Core.var x)) position;
            in
            (r ? error)
            && (r.kind or null) == "surface.unsolved-implicit"
            && (r.position or null) == position;

          stlcDiagnosticRefinementFailureIsDistinct =
            let
              position = { path = [ "diagnostic" "refinement" ]; };
              r = check zeroWithOneProof atLeastOneNat position;
            in
            (r ? error)
            && (r.kind or null) == "stlc.refinement-failure";
        '';
        tests = [
          "stlcDiagnosticUnsolvedImplicitIsDistinct"
          "stlcDiagnosticTypeMismatchIsDistinct"
          "stlcDiagnosticRefinementFailureIsDistinct"
        ];
      }
    ];
  };

  # Public extension API. It includes the core STLC vocabulary plus the
  # refinement forms introduced here.
  stlc = Core // {
    inherit surface refinement refine forget refineFromExpected;
  };

  # The refinement type itself is a type in U0.
  stlcRefinementTypeChecks =
    let r = check atLeastOneNat (H.u 0) { path = [ "refinement" "type" ]; };
    in !(r ? error) && r.tag == "sigma";

  # `refine AtLeastOne 1 proof` checks against AtLeastOne.
  stlcRefinementValueChecks =
    let
      r = check oneAtLeastOne atLeastOneNat
        { path = [ "refinement" "value" ]; };
    in
    !(r ? error) && r.tag == "pair";

  # `forget (refine 1 proof : AtLeastOne)` checks as Nat.
  stlcRefinementForgetChecks =
    let
      r = check (forget annotatedOneAtLeastOne) H.nat
        { path = [ "refinement" "forget" ]; };
    in
    !(r ? error) && r.tag == "fst";

  # The source-level refinement node receives a readable diagnostic instead
  # of exposing the underlying Sigma/Desc mismatch as the main message.
  stlcBadRefinementHasSurfaceDiagnostic =
    let
      position = { path = [ "bad" "refinement" ]; };
      r = check zeroWithOneProof atLeastOneNat position;
    in
    (r ? error)
    && (r.kind or null) == "stlc.refinement-failure"
    && (r.msg or null) == "refinement witness does not match predicate"
    && (r.position or null) == position
    && (r.error.position or null) == position
    && (r.error.checker.msg or null) != null;

  # Omitted lambda domains without an expected function type are implicit
  # problems, not ordinary type mismatches.
  stlcDiagnosticUnsolvedImplicitIsDistinct =
    let
      position = { path = [ "diagnostic" "implicit" ]; };
      r = elaborate (Core.holeLam "x" (x: Core.var x)) position;
    in
    (r ? error)
    && (r.kind or null) == "surface.unsolved-implicit"
    && (r.position or null) == position;

  # Applying Nat as a function remains an ordinary checker error. It is still
  # positioned, but it must not be classified as an implicit or refinement
  # diagnostic.
  stlcDiagnosticTypeMismatchIsDistinct =
    let
      position = { path = [ "diagnostic" "type-mismatch" ]; };
      r = check (Core.app H.zero H.zero) H.nat position;
    in
    (r ? error)
    && (r.position or null) == position
    && (r.kind or null) != "surface.unsolved-implicit"
    && (r.kind or null) != "stlc.refinement-failure"
    && (r.msg or null) != "unsolved implicit metavariable";

  # Refinement failures carry their own kind, so tooling can route them away
  # from both implicit-hole repair and ordinary type-mismatch hints.
  stlcDiagnosticRefinementFailureIsDistinct =
    let
      position = { path = [ "diagnostic" "refinement" ]; };
      r = check zeroWithOneProof atLeastOneNat position;
    in
    (r ? error)
    && (r.kind or null) == "stlc.refinement-failure"
    && (r.kind or null) != "surface.unsolved-implicit"
    && (r.msg or null) != "unsolved implicit metavariable";
}
