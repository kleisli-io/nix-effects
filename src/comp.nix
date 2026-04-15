# nix-effects comp: Computation ADT
#
# Abstract data type for the freer monad (Kiselyov & Ishii 2015):
#   Computation a = Pure a | Impure (Effect x) (FTCQueue x a)
#
# Pure: computation finished with a value
# Impure: computation suspended at an effect, with a queue of continuations
#
# This module is the single source of truth for the Computation
# representation. All construction and destruction of Computation
# values goes through these functions.
{ api, ... }:

let
  inherit (api) mk;

  # -- Introduction forms (constructors) --

  pure = mk {
    doc = "Lift a value into a pure computation (Return constructor).";
    value = value: { _tag = "Pure"; inherit value; };
    tests = {
      "creates-pure" = {
        expr = (pure 42).value;
        expected = 42;
      };
      "pure-is-pure" = {
        expr = isPure (pure 42);
        expected = true;
      };
    };
  };

  impure = mk {
    doc = "Create a suspended computation (OpCall constructor). Takes an effect and a continuation queue.";
    value = effect: queue: {
      _tag = "Impure";
      inherit effect queue;
    };
    tests = {
      "creates-impure" = {
        expr = (impure { name = "test"; param = null; } null).effect.name;
        expected = "test";
      };
      "impure-is-not-pure" = {
        expr = isPure (impure { name = "test"; param = null; } null);
        expected = false;
      };
    };
  };

  # -- Elimination forms --

  match = mk {
    doc = ''
      Eliminate a computation by cases.

      ```
      match comp { pure = a: ...; impure = effect: queue: ...; }
      ```

      Every function that consumes a Computation should go through
      match or isPure — never inspect _tag directly.
    '';
    value = comp: cases:
      if comp._tag == "Pure" then cases.pure comp.value
      else cases.impure comp.effect comp.queue;
    tests = {
      "match-pure" = {
        expr = match (pure 42) {
          pure = v: v * 2;
          impure = _: _: 0;
        };
        expected = 84;
      };
      "match-impure" = {
        expr = match (impure { name = "get"; param = null; } null) {
          pure = _: "wrong";
          impure = e: _: e.name;
        };
        expected = "get";
      };
      "match-impure-queue" = {
        expr = match (impure { name = "x"; param = 1; } "myqueue") {
          pure = _: null;
          impure = _: q: q;
        };
        expected = "myqueue";
      };
    };
  };

  isComp = mk {
    doc = "Test whether a value is a computation.";
    value = comp: (comp._tag or null == "Pure") || (comp._tag or null == "Impure");
    tests = {
      "pure-returns-true" = {
        expr = isComp (pure 1);
        expected = true;
      };
      "impure-returns-true" = {
        expr = isComp (impure { name = "x"; param = null; } null);
        expected = true;
      };
      "empty-returns-false" = {
        expr = isComp { };
        expected = false;
      };
    };
  };

  isPure = mk {
    doc = "Test whether a computation is Pure. For hot-path conditionals where match would allocate.";
    value = comp: comp._tag == "Pure";
    tests = {
      "pure-returns-true" = {
        expr = isPure (pure 1);
        expected = true;
      };
      "impure-returns-false" = {
        expr = isPure (impure { name = "x"; param = null; } null);
        expected = false;
      };
    };
  };

in mk {
  doc = "Computation ADT: introduction and elimination forms for Pure | Impure.";
  value = { inherit pure impure match isPure isComp; };
}
