# nix-effects scopconst integration tests
#
# Validates computation-scoped handlers via effect rotation:
# - Host/users example: different paths get different handler bindings
# - State isolation: scope state does not leak to outer state
# - Escape effects: unhandled effects rotate to outer handler
# - Nesting: scopes compose correctly
{ lib, fx }:

let
  inherit (fx) pure bind send handle;
  scope = fx.effects.scope;

  getUser = send "user" null;
  getHost = send "host" null;

  greet = bind getUser (user:
    bind getHost (host:
      pure "${user}@${host}"));

  hostHandler = {
    host = { state, ... }: { resume = "myhost"; inherit state; };
  };

  constScope = name: value:
    scope.run {
      handlers.${name} = { param, state }: { inherit state; resume = value; };
    };

  twoUsersTest = {
    expr =
      let
        comp =
          bind (constScope "user" "alice" greet) (a:
          bind (constScope "user" "bob"   greet) (b:
            pure { alice = a; bob = b; }));
        result = handle { handlers = hostHandler; } comp;
      in result.value;
    expected = { alice = "alice@myhost"; bob = "bob@myhost"; };
  };

  scopeStateIsolation = {
    expr =
      let
        incComp = bind (send "inc" 1) (_: send "inc" 1);
        scoped = scope.runWith {
          handlers.inc = { param, state }: { resume = null; state = state + param; };
          state = 0;
        } incComp;
        result = handle { state = "outer-untouched"; handlers = {}; } scoped;
      in { innerState = result.value.state; outerState = result.state; };
    expected = { innerState = 2; outerState = "outer-untouched"; };
  };

  scopeEscapeEffects = {
    expr =
      let
        comp = bind getUser (user:
          bind (send "log" user) (_:
            pure user));
        scoped = constScope "user" "alice" comp;
        result = handle {
          handlers.log = { param, state }: { resume = null; state = state ++ [param]; };
          state = [];
        } scoped;
      in { value = result.value; logs = result.state; };
    expected = { value = "alice"; logs = [ "alice" ]; };
  };

  nestedScopes = {
    expr =
      let
        comp = bind (send "env" null) (env:
          bind (send "user" null) (user:
            pure "${env}/${user}"));
        inner = constScope "user" "bob" comp;
        outer = constScope "env" "prod" inner;
        result = handle { handlers = {}; } outer;
      in result.value;
    expected = "prod/bob";
  };

  scopeWithStatefulHandler = {
    expr =
      let
        visitComp = bind (send "visit" null) (_: send "visit" null);
        aliceScope = scope.runWith {
          handlers.visit = { state, ... }: { resume = null; state = state + 1; };
          state = 0;
        } visitComp;
        bobScope = scope.runWith {
          handlers.visit = { state, ... }: { resume = null; state = state + 1; };
          state = 0;
        } visitComp;
        comp = bind aliceScope (a: bind bobScope (b:
          pure { aliceVisits = a.state; bobVisits = b.state; }));
        result = handle { handlers = {}; } comp;
      in result.value;
    expected = { aliceVisits = 2; bobVisits = 2; };
  };

  scopeDoesNotCorruptUserState = {
    expr =
      let
        comp =
          bind (send "inc" 1) (_:
          bind (constScope "user" "alice" (
            bind (send "inc" 1) (_: getUser)
          )) (user:
          bind (send "inc" 1) (_:
            pure user)));
        result = handle {
          handlers.inc = { param, state }: { resume = null; state = state + param; };
          state = 0;
        } comp;
      in { value = result.value; outerState = result.state; };
    expected = { value = "alice"; outerState = 3; };
  };

  dynamicHandlerFromEffect = {
    expr =
      let
        comp =
          bind (send "getHandler" null) (userName:
            constScope "user" userName getUser);
        result = handle {
          handlers.getHandler = { state, ... }: { resume = "dynamic-user"; inherit state; };
        } comp;
      in result.value;
    expected = "dynamic-user";
  };

  abortInsideScope = {
    expr =
      let
        comp = bind (send "fail" "boom") (_: pure "unreachable");
        scoped = scope.run {
          handlers.fail = { param, state }: { abort = { error = param; }; inherit state; };
        } comp;
        outer = bind scoped (v: pure { got = v; });
        result = handle { handlers = {}; } outer;
      in result.value;
    expected = { got = { error = "boom"; }; };
  };

  threeUsersFanOut = {
    expr =
      let
        users = [ "alice" "bob" "carol" ];
        perUser = builtins.map (u: constScope "user" u greet) users;
        comp = builtins.foldl' (acc: sc:
          bind acc (results: bind sc (v: pure (results ++ [v])))
        ) (pure []) perUser;
        result = handle { handlers = hostHandler; } comp;
      in result.value;
    expected = [ "alice@myhost" "bob@myhost" "carol@myhost" ];
  };

  scopeOverrideInNested = {
    expr =
      let
        comp = bind getUser (u1:
          bind (constScope "user" "inner" getUser) (u2:
            pure { outer = u1; inner = u2; }));
        scoped = constScope "user" "outer" comp;
        result = handle { handlers = {}; } scoped;
      in result.value;
    expected = { outer = "outer"; inner = "inner"; };
  };

  allPass = twoUsersTest.expr == twoUsersTest.expected
    && scopeStateIsolation.expr == scopeStateIsolation.expected
    && scopeEscapeEffects.expr == scopeEscapeEffects.expected
    && nestedScopes.expr == nestedScopes.expected
    && scopeWithStatefulHandler.expr == scopeWithStatefulHandler.expected
    && scopeDoesNotCorruptUserState.expr == scopeDoesNotCorruptUserState.expected
    && dynamicHandlerFromEffect.expr == dynamicHandlerFromEffect.expected
    && abortInsideScope.expr == abortInsideScope.expected
    && threeUsersFanOut.expr == threeUsersFanOut.expected
    && scopeOverrideInNested.expr == scopeOverrideInNested.expected;

in {
  inherit twoUsersTest scopeStateIsolation scopeEscapeEffects nestedScopes
          scopeWithStatefulHandler scopeDoesNotCorruptUserState
          dynamicHandlerFromEffect abortInsideScope threeUsersFanOut
          scopeOverrideInNested allPass;
}
