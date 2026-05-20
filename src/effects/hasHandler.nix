# nix-effects hasHandler: runtime handler existence check
#
# Send "has-handler" query to check if a handler exists in current scope.
{ fx, api, lib, ... }:

let
  inherit (fx.kernel) send;
  inherit (fx.trampoline) handle;

  hasHandler = send "has-handler";

in {
  inherit hasHandler;
  __docs._self = {
    description = "hasHandler: ask the runtime whether a handler with the given effect name exists in the surrounding scope; impure query.";
    signature = "hasHandler : String -> Computation Bool";
    doc = ''
      Check if a handler with given name exists in current scope.
    '';
    tests = {
      "hasHandler-is-impure" = {
        expr = (fx.comp.isPure (hasHandler "foo"));
        expected = false;
      };
      "hasHandler-finds-root-handler" = {
        expr =
          let
            comp = hasHandler "myEffect";
            result = handle {
              handlers.myEffect = { state, ... }: { resume = 42; inherit state; };
              state = null;
            } comp;
          in result.value;
        expected = true;
      };
      "hasHandler-missing-handler-returns-false" = {
        expr =
          let
            comp = hasHandler "missing";
            result = handle {
              handlers.myEffect = { state, ... }: { resume = 42; inherit state; };
              state = null;
            } comp;
          in result.value;
        expected = false;
      };
      "hasHandler-nested-scope" = {
        expr =
          let
            scope = fx.effects.scope;
            scoped = scope.run {
              handlers.inner = { state, ... }: { resume = null; inherit state; };
            } (hasHandler "inner");
            result = handle { handlers = {}; } scoped;
          in result.value;
        expected = true;
      };
      "hasHandler-escapes-scope" = {
        expr =
          let
            scope = fx.effects.scope;
            comp = hasHandler "outer";
            scoped = scope.run {
              handlers.inner = { state, ... }: { resume = null; inherit state; };
            } comp;
            result = handle {
              handlers.outer = { state, ... }: { resume = null; inherit state; };
            } scoped;
          in result.value;
        expected = true;
      };
    };
  };
}
