{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  M = fx.tc.elaborate.meta;
  C = fx.tc.check;
  V = fx.tc.value;

  List = A: H.listOf A;

  listElement = expectedType:
    if builtins.isAttrs expectedType
      && (expectedType._htag or null) == "app"
      && ((expectedType.fn._dtypeMeta.name or null) == "List")
    then expectedType.arg
    else null;

  expectedListError = context: {
    error = {
      msg = "nil requires an expected List type";
      kind = "surface.expected-list";
      position = context.position or null;
      expectedType = context.expectedType or null;
      term = context.term or null;
    };
    msg = "nil requires an expected List type";
    kind = "surface.expected-list";
    position = context.position or null;
  };

  nilFromExpected = { context, hoas ? H }:
    let
      implicit = context.implicitMeta {
        type = { ctx = C.emptyCtx; ty = V.vU V.vLevelZero; };
        label = "List.element";
      };
      expectedType = context.expectedType or null;
      elem = if expectedType == null then null else listElement expectedType;
    in
    if expectedType == null
    then {
      term = implicit.term;
      inherit implicit;
    }
    else if elem == null
    then expectedListError context
    else
      let
        elemVal = E.eval [ ] (hoas.elab elem);
        solvedState = M.solveMeta implicit.id elemVal implicit.state;
      in
      {
        term = hoas.nilAtExplicit elem;
        inherit elemVal implicit solvedState;
        element = elem;
      };

  surface = self.defineSurface {
    name = "Prelude";
    description = "Minimal surface prelude used by reference DSL proof tests.";
    constructors = {
      nil = {
        tag = "prelude.nil";
        handler = { context, hoas, lower, depth, ... }:
          let r = nilFromExpected { inherit context hoas; };
          in
          if r ? error then r
          else if context.expectedType == null then r.term
          else lower depth r.term;
      };
    };
  };

  nil = surface.mk "nil" { };
in
{
  scope = {
    prelude = api.leaf {
      value = {
        inherit List listElement nil nilFromExpected surface;
      };
      description = "Minimal surface prelude with List and an implicit-argument nil proof fixture.";
    };
  };

  tests = { };
}
