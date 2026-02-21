# nix-effects choice: Non-deterministic choice effect
#
# Provides choose/fail for non-deterministic computation.
# The handler collects all successful branches into a list.
#
# In algebraic effects, non-determinism is modeled as:
#   choose : [a] -> Computation a
#   fail   : Computation a  (abort with empty result)
#
# The listAll handler runs the computation for each choice,
# collecting all results. This is the list monad semantics.
{ fx, api, ... }:

let
  queue = fx.queue;
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  choose = mk {
    doc = ''
      Non-deterministic choice from a list of alternatives.
      The handler determines how alternatives are explored.

      choose : [a] -> Computation a
    '';
    value = alternatives: send "choose" alternatives;
    tests = {
      "choose-is-impure" = {
        expr = (choose.value [ 1 2 3 ])._tag;
        expected = "Impure";
      };
      "choose-effect-name" = {
        expr = (choose.value [ 1 2 3 ]).effect.name;
        expected = "choose";
      };
    };
  };

  fail = mk {
    doc = ''
      Fail the current branch of non-deterministic computation.
      Equivalent to choose [].

      fail : Computation a
    '';
    value = send "choose" [];
    tests = {
      "fail-is-impure" = {
        expr = fail.value._tag;
        expected = "Impure";
      };
      "fail-has-empty-alternatives" = {
        expr = fail.value.effect.param;
        expected = [];
      };
    };
  };

  guard = mk {
    doc = ''
      Guard a condition: continue if true, fail if false.

      guard : bool -> Computation null
    '';
    value = cond: if cond then pure null else fail.value;
    tests = {
      "guard-true-is-pure" = {
        expr = (guard.value true)._tag;
        expected = "Pure";
      };
      "guard-false-is-impure" = {
        expr = (guard.value false)._tag;
        expected = "Impure";
      };
    };
  };

  # The listAll handler uses a worklist to explore all branches.
  # For each "choose" effect, it forks the continuation for each alternative.
  # Results are accumulated into a list.
  listAll = mk {
    doc = ''
      Handler that explores all non-deterministic branches and returns
      a list of all results. Empty choices abort that branch.

      State is { results : [a], pending : [Computation a] }.
      After handling, results are in state.results.

        let r = handle { handlers = choice.listAll; state = choice.initialState; } comp;
        in r.state.results
    '';
    value = {
      choose = { param, state }:
        if param == [] then
          # No alternatives: abort this branch
          { abort = null; inherit state; }
        else
          # Resume with first alternative, queue rest as pending
          let
            first = builtins.head param;
            rest = builtins.tail param;
          in {
            resume = first;
            state = state // {
              pending = state.pending ++ rest;
            };
          };
    };
    tests = {
      "choose-resumes-with-first" = {
        expr = (listAll.value.choose {
          param = [ 10 20 30 ];
          state = { results = []; pending = []; };
        }).resume;
        expected = 10;
      };
      "choose-empty-aborts" = {
        expr = (listAll.value.choose {
          param = [];
          state = { results = []; pending = []; };
        }) ? abort;
        expected = true;
      };
      "choose-queues-rest" = {
        expr = builtins.length (listAll.value.choose {
          param = [ 10 20 30 ];
          state = { results = []; pending = []; };
        }).state.pending;
        expected = 2;
      };
    };
  };

  initialState = mk {
    doc = "Initial state for the listAll handler.";
    value = { results = []; pending = []; };
  };

in mk {
  doc = "Non-deterministic choice effect: choose/fail/guard with list handler.";
  value = {
    inherit choose fail guard listAll initialState;
  };
}
