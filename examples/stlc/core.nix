# STLC core surface example.
#
# This file is intentionally more heavily commented than library code. It is
# meant to be read as a small guide to building a surface language on top of
# nix-effects, not only as a regression test.
#
# The language here is the simply typed lambda calculus fragment that the
# later examples build on:
#
#   Type syntax:  A -> B        encoded as a non-dependent Pi
#   Term syntax:  \x : A. t     encoded as a HOAS lambda
#                 f a           encoded as application
#                 t : A         encoded as annotation
#
# There is no parser in this example. Users construct terms directly with Nix
# functions such as `lam "x" H.nat (x: x)`. That keeps the example focused on
# elaboration: surface nodes translate to the existing HOAS layer, and the
# existing kernel checker decides whether the term is well typed.
{ fx, ... }:

let
  # `H` is the target language. Every STLC form elaborates into one of these
  # HOAS combinators, then HOAS elaboration produces kernel terms.
  H = fx.types.hoas;

  # `S` is the surface framework. It provides constructor registration,
  # derived elaboration, and the surface-aware implicit metavariable helper.
  S = fx.surface;

  # These lower-level modules are used only by the implicit lambda example.
  # A plain STLC surface with explicit binder types only needs `H` and `S`.
  C = fx.tc.check;
  E = fx.tc.eval;
  M = fx.tc.elaborate.meta;
  V = fx.tc.value;

  # Extract the domain from an expected function type.
  #
  # Two shapes are accepted:
  #
  #   1. `stlc.pi` is this example's own surface-level Pi node.
  #   2. `pi` is the underlying HOAS Pi node.
  #
  # Accepting both lets users pass either an STLC arrow built below or a
  # direct HOAS function type from existing nix-effects code.
  piDomain = expectedType:
    if builtins.isAttrs expectedType && (expectedType._htag or null) == "stlc.pi"
    then expectedType.domain
    else if builtins.isAttrs expectedType && (expectedType._htag or null) == "pi"
    then expectedType.domain
    else null;

  expectedFunctionError = context: {
    error = {
      msg = "expected a function type";
      kind = "stlc.expected-function";
      position = context.position or null;
      expectedType = context.expectedType or null;
      term = context.term or null;
    };
    msg = "expected a function type";
    kind = "stlc.expected-function";
    position = context.position or null;
  };

  # Elaborate `\x. body` when the domain annotation is omitted, by reading
  # the expected function type and solving the missing domain metavariable
  # from it. Distinct from implicit binders in the plicity sense: this is a
  # surface-level "domain hole", not a binder whose presence the elaborator
  # auto-inserts.
  #
  #   expected type is Nat -> Nat
  #   term is          \x. x
  #   solve domain metavariable as Nat
  #
  # Data flow:
  #   1. Allocate a surface implicit metavariable for the missing domain.
  #   2. Read the expected type from the handler context.
  #   3. Extract the Pi domain from the expected type.
  #   4. Solve the metavariable with that domain value.
  #   5. Elaborate the lambda as an ordinary typed HOAS lambda.
  holeLambdaFromExpected = { context, name, body, hoas ? H }:
    let
      implicit = context.implicitMeta {
        type = { ctx = C.emptyCtx; ty = V.vU V.vLevelZero; };
        label = "stlc.lambda-domain";
      };
      expectedType = context.expectedType or null;
      domain = if expectedType == null then null else piDomain expectedType;
    in
    if expectedType == null
    then
      S.unsolvedImplicitError
        {
          metas = [{
            id = implicit.id;
            type = implicit.value.type;
            position = context.position or null;
          }];
          surface = context.surface or "STLC";
          term = context.term or null;
          position = context.position or null;
        }
    else if domain == null
    then expectedFunctionError context
    else
      let
        domainVal = E.eval [ ] (hoas.elab domain);
        solvedState = M.solveMeta implicit.id domainVal implicit.state;
      in
      {
        term = hoas.lam name domain body;
        inherit domain domainVal implicit solvedState;
      };

  # Surface definition.
  #
  # `defineSurface` registers handlers by constructor tag. The HOAS elaborator
  # calls the matching handler whenever it sees a surface node carrying this
  # registry. Each handler receives:
  #
  #   h         the current surface node
  #   depth     current binder depth for HOAS elaboration
  #   elaborate recursive HOAS elaboration function
  #   hoas      the HOAS API
  #   context   expected type, source position, and implicit-meta helper
  #
  # Most handlers below are one-line translations into HOAS. That is the main
  # architectural point: this example adds surface syntax, not new typing
  # rules.
  surface = S.defineSurface {
    name = "STLC";
    description = "Small typed lambda-calculus surface example.";
    constructors = {
      # Dependent function type:
      #
      #   pi "x" A (x: B x)
      #
      # For the non-dependent STLC arrow, use `arrow A B` below. It is encoded
      # as `pi "_" A (_: B)`.
      pi = {
        tag = "stlc.pi";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.forall h.name h.domain h.body);
      };

      # Explicitly typed lambda:
      #
      #   lam "x" H.nat (x: x)
      #
      # Variables are not looked up by string name. The binder body is a Nix
      # function, and the argument `x` is the HOAS variable marker supplied by
      # the HOAS elaborator. This avoids a separate name-resolution pass.
      lam = {
        tag = "stlc.lam";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.lam h.name h.domain h.body);
      };

      # Lambda with omitted domain:
      #
      #   holeLam "x" (x: x)
      #
      # This checks only when an expected function type is available. Without
      # expected type information, the missing domain is ambiguous and the
      # surface layer reports an unsolved implicit metavariable. Unrelated to
      # plicity-style implicit binders (see `implicitLam` below).
      holeLam = {
        tag = "stlc.hole-lam";
        handler = { context, depth, h, elaborate, hoas, ... }:
          let
            r = holeLambdaFromExpected {
              inherit context hoas;
              inherit (h) name body;
            };
          in
          if r ? error then r else elaborate depth r.term;
      };

      # Implicit Pi binder (plicity sidecar):
      #
      #   implicitPi "A" H.universe (A: arrow A A)
      #
      # The kernel Pi is unchanged; only the `_plicity` sidecar marks the
      # binder as implicit so that the bidirectional elaborator inserts a
      # fresh metavariable at every explicit application site whose
      # function inhabits this type.
      implicitPi = {
        tag = "stlc.implicit-pi";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.implicitForall h.name h.domain h.body);
      };

      # Implicit lambda (plicity sidecar):
      #
      #   implicitLam "A" H.universe (A: body)
      #
      # Wraps the body in an implicit binder that the check rule will
      # descend through when the expected type begins with an implicit Pi.
      implicitLam = {
        tag = "stlc.implicit-lam";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.implicitLam h.name h.domain h.body);
      };

      # Implicit application — caller passes the implicit argument
      # explicitly, bypassing automatic insertion at this site.
      implicitApp = {
        tag = "stlc.implicit-app";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.implicitApp h.fn h.arg);
      };

      # Type annotation. This is useful around lambdas because application
      # needs an inferable function type. The underlying checker can infer
      # from `ann term type`, then application proceeds normally.
      ann = {
        tag = "stlc.ann";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.ann h.term h.type);
      };

      # Function application. No special STLC-specific checking is done here;
      # the kernel checker handles the application rule after elaboration.
      app = {
        tag = "stlc.app";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.app h.fn h.arg);
      };
    };
  };

  # Smart constructors for users of the example.
  #
  # These hide `surface.mk` and give the examples a small source-language
  # vocabulary. The return values are still surface nodes, not kernel terms.
  pi = name: domain: body: surface.mk "pi" { inherit name domain body; };
  arrow = domain: codomain: pi "_" domain (_: codomain);
  lam = name: domain: body: surface.mk "lam" { inherit name domain body; };
  holeLam = name: body: surface.mk "holeLam" { inherit name body; };
  implicitPi = name: domain: body: surface.mk "implicitPi" { inherit name domain body; };
  implicitLam = name: domain: body: surface.mk "implicitLam" { inherit name domain body; };
  implicitApp = fn: arg: surface.mk "implicitApp" { inherit fn arg; };
  ann = term: type: surface.mk "ann" { inherit term type; };
  app = fn: arg: surface.mk "app" { inherit fn arg; };

  # `var` is intentionally the identity function. Binder variables are already
  # HOAS variables, so a user can write either `x` or `var x` in a body. Keeping
  # the helper in the public example makes the source-language intent explicit:
  # this position is a variable reference, not a Nix binding trick.
  var = x: x;

  # Check one STLC surface term against an expected type.
  #
  # The `position` field is a tiny source-location stand-in. Real parsers would
  # put file/line/column or an AST path here. The surface framework preserves it
  # on errors so diagnostics point back to source terms, not just kernel terms.
  check = term: expectedType: position:
    S.elaborate {
      inherit surface term expectedType position;
    };

  # Shared fixtures.
  #
  #   idNatTy  = Nat -> Nat
  #   idNat    = \x : Nat. x
  #   idNatAnn = (\x : Nat. x) : Nat -> Nat
  #
  # The annotation is used in the application test because an unannotated
  # lambda checks against a function type, while application first infers the
  # function position.
  idNatTy = arrow H.nat H.nat;
  idNat = lam "x" H.nat (x: var x);
  idNatAnn = ann idNat idNatTy;

  # A small context fixture for testing `holeLambdaFromExpected` directly.
  # The real elaborator builds this shape through `handlerContext`; exposing it
  # here makes the metavariable state transition visible in the test below.
  holeContext = term: expectedType: position: {
    inherit expectedType position term;
    surface = "STLC";
    constructor = "holeLam";
    implicitMeta = metaArgs:
      S.implicitMeta (metaArgs // {
        position = metaArgs.position or position;
        surface = metaArgs.surface or "STLC";
      });
  };

  # Worked examples for plicity-style implicit binders.
  #
  #   polyIdTy    : {A : U(0)} → A → A
  #   polyId      : λ{A : U(0)}. λ(x : A). x
  #   polyIdAnn   : polyId : polyIdTy (annotation makes the head inferable)
  #
  #   polyConstTy : {A B : U(0)} → A → B → A
  #   polyConst   : λ{A : U(0)}. λ{B : U(0)}. λ(x : A). λ(_ : B). x
  #   polyConstAnn: polyConst : polyConstTy
  #
  # End-to-end walkthrough — `app polyIdAnn H.zero` checked at `H.nat`:
  #
  # 1. Surface dispatch. `check (app polyIdAnn H.zero) H.nat pos` calls
  #    `S.elaborate`, which routes the `stlc.app` node through the
  #    elaborator overlay's check rule with expected type `vNat`.
  #
  # 2. Check rule. `elabCheck ctx (app polyIdAnn zero) vNat`
  #    (src/tc/elaborate/check.nix). Forces the expected type — not an
  #    implicit Pi, not a meta — so falls through to `rigidOrSub`.
  #    `rigidOrSub` recognises the term as an App (`isAppTm`) and routes
  #    it through `elabSub` so synthesis can peel implicit binders. The
  #    rigid checker is bypassed deliberately: it would otherwise feed
  #    `zero` into the head's `U(0)` domain and report a spurious "type
  #    mismatch: expected U, got Nat".
  #
  # 3. Synthesis (Sub-rule). `elabSub` synthesises the term's type via
  #    `elabInfer ctx (app polyIdAnn zero)`. `elabInfer` sees an App and
  #    dispatches to `elabInferApp` (src/tc/elaborate/infer.nix).
  #
  # 4. Head inference. `elabInferApp` recursively infers the head:
  #    `elabInfer ctx polyIdAnn`. `polyIdAnn` is an `ann` term; it is not
  #    a meta and not an App, so it falls through to the kernel's rigid
  #    `fx.tc.check.inferTm`. The kernel checks the annotation's type
  #    expression, returning the evaluated type with its `_plicity`
  #    sidecar preserved (src/tc/check/type.nix:pi). Result type:
  #    `VPi A U(0) (_: VPi _ A (_: A))` with the outer `_plicity =
  #    "implicit"` marker still attached.
  #
  # 5. Implicit insertion. The outer App is explicit (no plicity sidecar
  #    on `app`), so `elabInferApp` calls `insertImplicits ctx fTm fTy`
  #    (src/tc/elaborate/insertion.nix). The head's type is an implicit
  #    Pi, so `insertImplicits` allocates a fresh metavariable
  #    `?A : U(0)`, applies it to the head term (`fTm' = mkApp fTm ?A`),
  #    instantiates the closure (`fTy' = ?A → ?A`), and recurses. `?A → ?A`
  #    is not implicit, so insertion stops. The residual head is the
  #    explicit `polyIdAnn ?A` of type `?A → ?A`.
  #
  # 6. Argument check. `elabInferApp` checks the explicit argument
  #    `zero` against the residual domain `?A` via `elabCheck`.
  #    `?A` is a `VMeta` type, so `elabCheck` emits a `plicity-await`
  #    marker and routes through `rigidOrSub`. `rigidOrSub` sees
  #    `containsMetaVal ?A = true` and routes through `elabSub`, which
  #    synthesises `inferTm zero = (zero, Nat)` and posts a conv
  #    constraint `?A ≡ Nat : U(0)`. `simplifyConv` direct-solves the
  #    meta: `?A := Nat`.
  #
  # 7. Result type. `elabInferApp` builds the return value
  #    `{ term = mkApp (polyIdAnn ?A) zero; type = instantiate (?A→?A) zero }`.
  #    `?A` is solved to `Nat` in the meta context, so the residual type
  #    is `Nat` (via `forceMeta` when next walked).
  #
  # 8. Outer conv. Back in `elabSub`, conv compares the synthesised
  #    `Nat` against the expected `Nat`. No metas remain, so this
  #    delegates to kernel `C.conv` and succeeds rigidly. Final term
  #    tag: `app`. Final type: `Nat`.
  #
  # Worked variant — `app polyConstAnn H.zero` at `Nat → Nat`:
  #
  # Same flow as above, but with two implicit binders. `insertImplicits`
  # peels `A` (allocates `?A`) and `B` (allocates `?B`), yielding the
  # residual head `polyConstAnn ?A ?B` of type `?A → ?B → ?A`. Step 6
  # solves `?A := Nat` from the explicit argument `zero`. The result
  # type after step 7 is `?B → Nat` (with `?A` forced to `Nat`).
  # Step 8's conv compares `?B → Nat ≡ Nat → Nat`: both sides are VPi
  # *types* (not values), and at least one carries a meta, so
  # `elabConv` dispatches to `elabConvPiTypes`
  # (src/tc/elaborate/conv.nix), which recurses on the domains
  # (`?B ≡ Nat` solves `?B := Nat`) and on the codomains under a fresh
  # var (`Nat ≡ Nat` rigid). This is the structural Pi-type equality
  # rule, distinct from `elabConvPi`'s η-rule for values of Pi type;
  # it mirrors the kernel's own `VPi == VPi` rule (src/tc/conv.nix).
  #
  # Surface position survives every overlay hop: `S.elaborate` carries
  # `position` on the constraint and error frames, so a downstream
  # failure (e.g. `app H.zero H.zero` — Nat applied as a function)
  # still reports the original surface path, even though the head has
  # gone through the inferring overlay where insertion could otherwise
  # have erased position information. See
  # `stlcInsertionPreservesSurfaceBlame` below.
  universe0 = H.u H.levelZero;
  polyIdTy = implicitPi "A" universe0 (A: arrow A A);
  polyId = implicitLam "A" universe0 (A: lam "x" A (x: var x));
  polyIdAnn = ann polyId polyIdTy;

  polyConstTy = implicitPi "A" universe0 (A:
    implicitPi "B" universe0 (B:
      arrow A (arrow B A)));
  polyConst = implicitLam "A" universe0 (A:
    implicitLam "B" universe0 (B:
      lam "x" A (x:
        lam "_" B (_: var x))));
  polyConstAnn = ann polyConst polyConstTy;
in
rec {
  __example = {
    title = "STLC Core Surface";
    description = "A simply typed lambda-calculus surface over the HOAS kernel.";
    introduction = ''
      This example builds a small source language over the existing HOAS
      checker. The surface adds syntax and source positions; the kernel still
      owns typing and normalization.
    '';
    sections = [
      {
        title = "Define the surface";
        prose = ''
          `defineSurface` maps each source constructor to a HOAS expression.
          The core STLC fragment has Pi types, lambdas, annotations, and
          applications.
        '';
        code = ''
          surface = S.defineSurface {
            name = "STLC";
            description = "Small typed lambda-calculus surface example.";
            constructors = {
              lam = {
                tag = "stlc.lam";
                handler = { depth, h, elaborate, hoas, ... }:
                  elaborate depth (hoas.lam h.name h.domain h.body);
              };

              app = {
                tag = "stlc.app";
                handler = { depth, h, elaborate, hoas, ... }:
                  elaborate depth (hoas.app h.fn h.arg);
              };
            };
          };
        '';
        tests = [
          "stlcIdentityChecks"
          "stlcApplicationChecks"
          "stlcBadApplicationHasSurfaceBlame"
        ];
      }
      {
        title = "Smart constructors";
        prose = ''
          Users construct source terms with small Nix functions. The values are
          surface nodes until `check` elaborates them into HOAS.
        '';
        code = ''
          arrow = domain: codomain: pi "_" domain (_: codomain);
          lam = name: domain: body: surface.mk "lam" { inherit name domain body; };
          ann = term: type: surface.mk "ann" { inherit term type; };
          app = fn: arg: surface.mk "app" { inherit fn arg; };

          idNatTy = arrow H.nat H.nat;
          idNat = lam "x" H.nat (x: var x);
          idNatAnn = ann idNat idNatTy;
        '';
        tests = [ ];
      }
      {
        title = "Expected-type holes";
        prose = ''
          `holeLam` omits a lambda domain. The handler reads the expected type,
          solves a surface implicit metavariable with the Pi domain, and then
          elaborates an ordinary typed lambda.
        '';
        code = ''
          holeLambdaFromExpected = { context, name, body, hoas ? H }:
            let
              implicit = context.implicitMeta {
                type = { ctx = C.emptyCtx; ty = V.vU V.vLevelZero; };
                label = "stlc.lambda-domain";
              };
              expectedType = context.expectedType or null;
              domain = if expectedType == null then null else piDomain expectedType;
            in
            if expectedType == null
            then S.unsolvedImplicitError { metas = [{ id = implicit.id; }]; }
            else if domain == null
            then expectedFunctionError context
            else {
              term = hoas.lam name domain body;
              solvedState = M.solveMeta implicit.id (E.eval [ ] (hoas.elab domain)) implicit.state;
            };
        '';
        tests = [
          "stlcHoleLambdaSolvesDomain"
        ];
      }
      {
        title = "Implicit insertion";
        prose = ''
          Plicity-style implicit binders are carried as sidecars on Pi and
          lambda nodes. During application, the elaborator inserts fresh metas
          for implicit arguments and solves them from explicit arguments or
          the expected residual type.
        '';
        code = ''
          polyIdTy = implicitPi "A" universe0 (A: arrow A A);
          polyId = implicitLam "A" universe0 (A: lam "x" A (x: var x));
          polyIdAnn = ann polyId polyIdTy;

          stlcPolyIdAppliedSolvesImplicit =
            let
              position = { path = [ "poly" "id" "zero" ]; };
              r = check (app polyIdAnn H.zero) H.nat position;
            in
            !(r ? error) && r.tag == "app";
        '';
        tests = [
          "stlcPolyIdAppliedSolvesImplicit"
          "stlcPolyConstPartialAppPostpones"
          "stlcPolyConstFullySaturatedChecks"
          "stlcInsertionPreservesSurfaceBlame"
        ];
      }
    ];
  };

  # Public example API. Import this file and use `stlc.*` to construct terms:
  #
  #   let E = (import ./examples/stlc { inherit fx; }).core;
  #   in E.stlc.app (E.stlc.ann ...) ...
  stlc = {
    inherit surface pi arrow lam holeLam implicitPi implicitLam implicitApp
      ann app var holeLambdaFromExpected;
    inherit (H) nat bool zero true_ false_;
    universe = universe0;
    inherit polyIdTy polyId polyIdAnn polyConstTy polyConst polyConstAnn;
  };

  # `\x : Nat. x` checks against `Nat -> Nat`.
  stlcIdentityChecks =
    let r = check idNat idNatTy { path = [ "id" ]; };
    in !(r ? error) && r.tag == "lam";

  # `((\x : Nat. x) : Nat -> Nat) 0` checks against `Nat`.
  stlcApplicationChecks =
    let r = check (app idNatAnn H.zero) H.nat { path = [ "id" "apply" ]; };
    in !(r ? error) && r.tag == "app";

  # `0 0` is not an application of a function. The interesting part for this
  # example is not that it fails, but that the surface position survives the
  # lower-level checker error.
  stlcBadApplicationHasSurfaceBlame =
    let r = check (app H.zero H.zero) H.nat { path = [ "bad" "apply" ]; };
    in (r ? error)
      && (r.position or null) == { path = [ "bad" "apply" ]; };

  # `\x. x` checks against `Nat -> Nat` by solving the omitted domain from
  # the expected type. The test inspects both the initial hole and the solved
  # state so the metavariable path is visible to readers.
  stlcHoleLambdaSolvesDomain =
    let
      term = holeLam "x" (x: var x);
      expected = arrow H.nat H.nat;
      position = { path = [ "hole" "id" ]; };
      solved = holeLambdaFromExpected {
        context = holeContext term expected position;
        name = "x";
        body = x: var x;
      };
      checked = check term expected position;
    in
    !(checked ? error)
    && checked.tag == "lam"
    && solved.implicit.state.delta."0".tag == "Hole"
    && solved.solvedState.delta."0".tag == "Solved"
    && solved.solvedState.delta."0".tm.tag == "VMu";

  # `polyIdAnn 0` checked against `Nat`. The elaborator infers the head's
  # implicit-Pi type, peels `A` by inserting a fresh metavariable, then
  # checks `0` against the residual explicit Pi. Conv solves `A := Nat`.
  stlcPolyIdAppliedSolvesImplicit =
    let
      position = { path = [ "poly" "id" "zero" ]; };
      r = check (app polyIdAnn H.zero) H.nat position;
    in
    !(r ? error) && r.tag == "app";

  # `polyConstAnn 0` checked against `Nat -> Nat`. Two implicit binders
  # peel into fresh metavariables; A is solved Nat from the first
  # explicit argument (`0`), and B is solved Nat from the residual
  # expected `Nat -> Nat` via structural Pi-vs-Pi conv on the residual
  # `B -> Nat` against the explicit `Nat -> Nat`. The elaborated term is
  # the partial application as an `app`; success is the absence of an
  # `unsolved implicit metavariable` diagnostic, which would otherwise
  # fire if B were never reached by conv decomposition.
  stlcPolyConstPartialAppPostpones =
    let
      position = { path = [ "poly" "const" "zero" ]; };
      r = check (app polyConstAnn H.zero) (arrow H.nat H.nat) position;
    in
    !(r ? error) && r.tag == "app";

  # `polyConstAnn 0 true` checked against `Nat`. The second argument
  # forces `B := Bool`; the residual type matches `Nat`.
  stlcPolyConstFullySaturatedChecks =
    let
      position = { path = [ "poly" "const" "full" ]; };
      r = check (app (app polyConstAnn H.zero) H.true_) H.nat position;
    in
    !(r ? error) && r.tag == "app";

  # Surface blame survives insertion. The bad application `0 0` (Nat
  # applied as a function) still reports its surface path, even though
  # the head goes through the inferring overlay where insertion could
  # otherwise have erased position information.
  stlcInsertionPreservesSurfaceBlame =
    let
      position = { path = [ "insertion" "bad-apply" ]; };
      r = check (app H.zero H.zero) H.nat position;
    in
    (r ? error)
    && (r.position or null) == position;
}
