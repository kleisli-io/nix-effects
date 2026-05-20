{ fx, ... }:

{
  scope = {
    operators = { __div = fx.kernel.bind; };
  };

  tests = {};

  __docs = {
    operators = {
      description = "operators: sugar operator overloads — currently `__div` aliasing `fx.kernel.bind` so `c / k` reads as `bind c k` in expression context.";
      doc = ''
        Opt-in operator-style monadic composition. The attrset's
        `__div` field is invoked by Nix's `/` operator when the LHS
        is an attrset carrying `__div`. Use sparingly: operator
        overloading is non-idiomatic in Nix and obscures dataflow for
        readers unfamiliar with the convention. The combinator forms
        (`bind`, `do`, `kleisli`) remain the canonical entry points.
      '';
    };
  };
}
