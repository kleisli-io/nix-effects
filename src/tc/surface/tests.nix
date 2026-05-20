{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  El = fx.tc.elaborate;
  M = fx.tc.elaborate.meta;
  C = fx.tc.check;
  V = fx.tc.value;

  boolIf = hoas: condition: onTrue: onFalse:
    hoas.boolElim 0 (hoas.lam "_" hoas.bool (_: hoas.bool)) onTrue onFalse condition;

  Toy = self.defineSurface {
    name = "ToyBool";
    description = "Boolean expression surface used by the elaboration registry tests.";
    constructors = {
      lit = {
        tag = "toy.lit";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (if h.value then hoas.true_ else hoas.false_);
      };
      not = {
        tag = "toy.not";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (boolIf hoas h.term hoas.false_ hoas.true_);
      };
      and = {
        tag = "toy.and";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (boolIf hoas h.lhs h.rhs hoas.false_);
      };
      or = {
        tag = "toy.or";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (boolIf hoas h.lhs hoas.true_ h.rhs);
      };
    };
  };

  lit = value: Toy.mk "lit" { inherit value; };
  not_ = term: Toy.mk "not" { inherit term; };
  and_ = lhs: rhs: Toy.mk "and" { inherit lhs rhs; };
  or_ = lhs: rhs: Toy.mk "or" { inherit lhs rhs; };

  Plicit = self.defineSurface {
    name = "PlicitToy";
    constructors = {
      explicitLam = {
        tag = "plicit.explicit-lam";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.lam h.name h.domain h.body);
      };
      implicitLam = {
        tag = "plicit.implicit-lam";
        plicity = "implicit";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.lam h.name h.domain h.body);
      };
    };
  };

  evalBool = term:
    El.extract H.bool (E.eval [ ] (H.elab term));

  badRegistry = self.register self.empty "toy.bad" ({ depth, elaborate, hoas, ... }:
    elaborate depth hoas.zero);
  badTerm = self.node badRegistry "toy.bad" { };

  RawToy = self.defineSurface {
    name = "RawToyBool";
    constructors = { };
  };

  rawOrnament = self.defineOrnament {
    source = RawToy;
    target = H.bool;
    mapping = { };
    section = term: if term.value then H.true_ else H.false_;
    forget = term: { value = evalBool term; };
  };

  ContextToy = self.defineSurface {
    name = "ContextToy";
    constructors = {
      expected = {
        tag = "context.expected";
        handler = { context, hoas, elaborate, depth, ... }:
          elaborate depth
            (if context.expectedType != null && (context.expectedType._htag or null) == "unit"
            then hoas.tt
            else hoas.zero);
      };
      positioned = {
        tag = "context.positioned";
        handler = { context, hoas, elaborate, depth, ... }:
          elaborate depth
            (if context.position == { path = [ "root" "term" ]; }
            then hoas.tt
            else hoas.zero);
      };
      explicitMeta = {
        tag = "context.explicit-meta";
        handler = { context, ... }:
          (M.mkMeta 0 [ ]) // {
            type = { ctx = C.emptyCtx; ty = V.vUnit; };
            _surfacePosition = context.position;
          };
      };
      implicit = {
        tag = "context.implicit";
        handler = { context, ... }:
          (context.implicitMeta {
            type = { ctx = C.emptyCtx; ty = V.vUnit; };
          }).term;
      };
    };
  };

  contextTerm = name: fields:
    ContextToy.mk name fields;
in
{
  scope = {
    toy = api.leaf {
      value = {
        inherit Toy lit not_ and_ or_ evalBool;
      };
      description = "Toy boolean surface used as an end-to-end elaboration fixture.";
    };
  };

  tests = {
    "surface-empty-registry-preserves-hoas-elaboration" = {
      expr = (H.elab H.tt).tag;
      expected = "tt";
    };

    "surface-constructor-spec-plicity-defaults-to-absent" = {
      expr =
        let n = Plicit.mk "explicitLam" { name = "x"; domain = H.nat; body = (x: x); };
        in n ? _plicity;
      expected = false;
    };

    "surface-constructor-spec-plicity-injects-implicit-sidecar" = {
      expr = (Plicit.mk "implicitLam" { name = "x"; domain = H.nat; body = (x: x); })._plicity;
      expected = "implicit";
    };

    "surface-constructor-spec-plicity-respects-caller-override" = {
      expr = (Plicit.mk "implicitLam" {
        name = "x";
        domain = H.nat;
        body = (x: x);
        _plicity = "explicit";
      })._plicity;
      expected = "explicit";
    };

    "surface-constructor-spec-implicit-lam-elaborates-identically-to-explicit" = {
      expr =
        let
          e = Plicit.mk "explicitLam" { name = "x"; domain = H.nat; body = (x: x); };
          i = Plicit.mk "implicitLam" { name = "x"; domain = H.nat; body = (x: x); };
        in
        H.elab e == H.elab i;
      expected = true;
    };

    "surface-empty-registry-missing-handler-errors" = {
      expr = (builtins.tryEval (H.elab (self.node self.empty "toy.missing" { }))).success;
      expected = false;
    };

    "surface-toy-literal-elaborates" = {
      expr = H.checkHoas H.bool (lit true) ? error;
      expected = false;
    };

    "surface-toy-not-evaluates" = {
      expr = evalBool (not_ (lit true));
      expected = false;
    };

    "surface-toy-and-evaluates" = {
      expr = evalBool (and_ (lit true) (lit false));
      expected = false;
    };

    "surface-toy-or-evaluates" = {
      expr = evalBool (or_ (lit false) (lit true));
      expected = true;
    };

    "surface-derived-elaborator-checks-expected-type" = {
      expr = self.elaborate { surface = Toy; term = lit true; expectedType = H.bool; } ? error;
      expected = false;
    };

    "surface-derived-elaborator-reports-check-error" = {
      expr = self.elaborate { surface = Toy; term = badTerm; expectedType = H.bool; } ? error;
      expected = true;
    };

    "surface-derived-elaborator-attaches-position-to-check-error" = {
      expr =
        let
          r = self.elaborate {
            surface = Toy;
            term = badTerm;
            expectedType = H.bool;
            position = { path = [ "bad" ]; };
          };
        in
        {
          hasError = r ? error;
          position = r.position or null;
          errorPosition = r.error.position or null;
        };
      expected = {
        hasError = true;
        position = { path = [ "bad" ]; };
        errorPosition = { path = [ "bad" ]; };
      };
    };

    "surface-ornament-section-elaborates" = {
      expr = self.elaborate
        {
          surface = RawToy;
          ornament = rawOrnament;
          term = { value = true; };
          expectedType = H.bool;
        } ? error;
      expected = false;
    };

    "surface-ornament-forget-is-exposed" = {
      expr = rawOrnament.forget (lit false);
      expected = { value = false; };
    };

    "surface-derived-printer-renders-constructor" = {
      expr = self.print { surface = Toy; term = lit true; };
      expected = "ToyBool.lit";
    };

    "surface-derived-parser-accepts-ast-input" = {
      expr = (self.parse { surface = Toy; input = lit false; })._htag;
      expected = "toy.lit";
    };

    "surface-handler-context-exposes-expected-type" = {
      expr = self.elaborate
        {
          surface = ContextToy;
          term = contextTerm "expected" { };
          expectedType = H.unit;
        } ? error;
      expected = false;
    };

    "surface-handler-context-exposes-position" = {
      expr = self.elaborate
        {
          surface = ContextToy;
          term = contextTerm "positioned" { };
          expectedType = H.unit;
          position = { path = [ "root" "term" ]; };
        } ? error;
      expected = false;
    };

    "surface-explicit-meta-routes-through-meta-check" = {
      expr = (self.elaborate {
        surface = ContextToy;
        term = contextTerm "explicitMeta" { };
        expectedType = H.unit;
      }).tag;
      expected = "meta";
    };

    "surface-implicit-meta-helper-allocates-hole" = {
      expr =
        let
          r = self.implicitMeta {
            type = { ctx = C.emptyCtx; ty = V.vUnit; };
            position = { path = [ "implicit" ]; };
          };
        in
        {
          termTag = r.term.tag;
          valueTag = r.value._vTag;
          hole = r.state.delta."0".tag;
          position = r.state.delta."0".type.surface.position;
        };
      expected = {
        termTag = "meta";
        valueTag = "VMeta";
        hole = "Hole";
        position = { path = [ "implicit" ]; };
      };
    };

    "surface-implicit-meta-without-expected-type-errors" = {
      expr =
        let
          r = self.elaborate {
            surface = ContextToy;
            term = contextTerm "implicit" { };
            position = { path = [ "ambiguous" ]; };
          };
        in
        {
          hasError = r ? error;
          kind = r.kind or null;
          position = r.error.position or null;
        };
      expected = {
        hasError = true;
        kind = "surface.unsolved-implicit";
        position = { path = [ "ambiguous" ]; };
      };
    };

    "surface-prelude-nil-checks-against-list-nat" = {
      expr =
        let
          r = self.elaborate {
            surface = self.prelude.surface;
            term = self.prelude.nil;
            expectedType = H.listOf H.nat;
            position = { path = [ "nil" ]; };
          };
        in
        "${r.tag}/${r.d.tag}";
      expected = "desc-con/boot-inl";
    };

    "surface-prelude-nil-solves-element-implicit" = {
      expr =
        let
          r = self.prelude.nilFromExpected {
            context = {
              expectedType = H.listOf H.nat;
              position = { path = [ "nil" ]; };
              surface = "Prelude";
              constructor = "nil";
              term = self.prelude.nil;
              implicitMeta = metaArgs:
                self.implicitMeta (metaArgs // {
                  position = metaArgs.position or { path = [ "nil" ]; };
                  surface = metaArgs.surface or "Prelude";
                });
            };
          };
        in
        {
          state = r.implicit.state.delta."0".tag;
          solved = r.solvedState.delta."0".tag;
          solutionTag = r.solvedState.delta."0".tm.tag;
        };
      expected = {
        state = "Hole";
        solved = "Solved";
        solutionTag = "VMu";
      };
    };

    "surface-prelude-nil-ambiguous-reports-unsolved-implicit" = {
      expr =
        let
          r = self.elaborate {
            surface = self.prelude.surface;
            term = self.prelude.nil;
            position = { path = [ "nil" "ambiguous" ]; };
          };
        in
        {
          hasError = r ? error;
          kind = r.kind or null;
          position = r.position or null;
        };
      expected = {
        hasError = true;
        kind = "surface.unsolved-implicit";
        position = { path = [ "nil" "ambiguous" ]; };
      };
    };

    "surface-prelude-nil-rejects-non-list-expected-type" = {
      expr =
        let
          r = self.elaborate {
            surface = self.prelude.surface;
            term = self.prelude.nil;
            expectedType = H.nat;
            position = { path = [ "nil" "mismatch" ]; };
          };
        in
        {
          hasError = r ? error;
          kind = r.kind or null;
          position = r.position or null;
        };
      expected = {
        hasError = true;
        kind = "surface.expected-list";
        position = { path = [ "nil" "mismatch" ]; };
      };
    };
  };
}
