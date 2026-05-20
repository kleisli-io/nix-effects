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
{ ... }:

let
  pure = value: { _tag = "Pure"; inherit value; };

  impure = effect: queue: {
    _tag = "Impure";
    inherit effect queue;
  };

  match = comp: cases:
    if comp._tag == "Pure" then cases.pure comp.value
    else cases.impure comp.effect comp.queue;

  isComp = comp: (comp._tag or null == "Pure") || (comp._tag or null == "Impure");

  isPure = comp: comp._tag == "Pure";

in {
  inherit pure impure match isPure isComp;

  __docs = {
    _self = {
      description = "Computation ADT: `pure`/`impure` constructors plus `match`/`isComp`/`isPure` eliminators — the freer-monad value representation other modules build on.";
      doc = "Computation ADT: introduction and elimination forms for `Pure | Impure`.";
    };

    pure = {
      description = "pure: lift a value into a pure computation (`Pure` constructor); the trivial computation that returns the value without performing any effect.";
      signature = "pure : a -> Computation a";
      doc = "Lift a value into a pure computation. The Return constructor of the freer monad.";
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

    impure = {
      description = "impure: build a suspended computation (`Impure` constructor) carrying an effect request and a continuation queue to resume against.";
      signature = "impure : { name, param } -> FTCQueue -> Computation a";
      doc = "Create a suspended computation. The OpCall constructor of the freer monad — pairs an effect with the continuation queue.";
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

    match = {
      description = "match: eliminate a computation by cases, dispatching to `pure` or `impure` clauses; consumers should use this instead of inspecting `_tag` directly.";
      signature = "match : Computation a -> { pure : a -> b, impure : Effect -> FTCQueue -> b } -> b";
      doc = ''
        Eliminate a computation by cases:

        ```
        match comp { pure = a: ...; impure = effect: queue: ...; }
        ```

        Every function that consumes a `Computation` should go through
        `match` or `isPure` — never inspect `_tag` directly.
      '';
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

    isComp = {
      description = "isComp: test whether a value is a computation (has `_tag` of `Pure` or `Impure`); returns `false` for any other Nix value.";
      signature = "isComp : a -> Bool";
      doc = "Test whether a value is a computation. Returns `true` iff `_tag` is `Pure` or `Impure`.";
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

    isPure = {
      description = "isPure: hot-path predicate for `_tag == \"Pure\"`; cheaper than `match` for branching since it avoids the case-record allocation.";
      signature = "isPure : Computation a -> Bool";
      doc = "Test whether a computation is `Pure`. For hot-path conditionals where `match` would allocate a case record.";
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
  };
}

