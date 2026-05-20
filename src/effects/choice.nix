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
  choose = alternatives: send "choose" alternatives;

  fail = send "choose" [ ];

  guard = cond: if cond then pure null else fail;

  # The listAll handler uses a worklist to explore all branches.
  # For each "choose" effect, it forks the continuation for each alternative.
  # Results are accumulated into a list.
  listAll = {
    choose = { param, state }:
      if param == [ ] then
      # No alternatives: abort this branch
        { abort = null; inherit state; }
      else
      # Resume with first alternative, queue rest as pending
        let
          first = builtins.head param;
          rest = builtins.tail param;
        in
        {
          resume = first;
          state = state // {
            pending = state.pending ++ rest;
          };
        };
  };

  initialState = { results = [ ]; pending = [ ]; };

in
api.namespace {
  description = "choice effect: non-deterministic computation via choose/fail/guard with a listAll handler that explores every branch (list-monad semantics).";
  doc = "Non-deterministic choice effect: choose/fail/guard with list handler.";
  value = {
    choose = api.leaf {
      value = choose;
      description = "choose: non-deterministic selection from a list of alternatives; the handler determines exploration strategy (e.g. listAll for all branches).";
      signature = "choose : [a] -> Computation a";
      doc = ''
        Non-deterministic choice from a list of alternatives. The handler
        determines how alternatives are explored.
      '';
      tests = {
        "choose-is-impure" = {
          expr = fx.comp.isPure (choose [ 1 2 3 ]);
          expected = false;
        };
        "choose-effect-name" = {
          expr = (choose [ 1 2 3 ]).effect.name;
          expected = "choose";
        };
      };
    };

    fail = api.leaf {
      value = fail;
      description = "fail: abort the current non-deterministic branch; equivalent to `choose []` with an empty-alternatives short-circuit.";
      signature = "fail : Computation a";
      doc = ''
        Fail the current branch of non-deterministic computation.
        Equivalent to `choose []`.
      '';
      tests = {
        "fail-is-impure" = {
          expr = fx.comp.isPure fail;
          expected = false;
        };
        "fail-has-empty-alternatives" = {
          expr = fail.effect.param;
          expected = [ ];
        };
      };
    };

    guard = api.leaf {
      value = guard;
      description = "guard: continue when the predicate is true, fail the branch when false; threads boolean predicates into non-deterministic search.";
      signature = "guard : bool -> Computation null";
      doc = ''
        Guard a condition: continue if true, fail if false.
      '';
      tests = {
        "guard-true-is-pure" = {
          expr = fx.comp.isPure (guard true);
          expected = true;
        };
        "guard-false-is-impure" = {
          expr = fx.comp.isPure (guard false);
          expected = false;
        };
      };
    };

    listAll = api.leaf {
      value = listAll;
      description = "choice.listAll: handler exploring every non-deterministic branch and accumulating results into `state.results`; list-monad semantics.";
      doc = ''
        Handler that explores all non-deterministic branches and returns
        a list of all results. Empty choices abort that branch.

        State is `{ results : [a], pending : [Computation a] }`.
        After handling, results are in `state.results`.

        ```nix
        let r = handle { handlers = choice.listAll; state = choice.initialState; } comp;
        in r.state.results
        ```
      '';
      tests = {
        "choose-resumes-with-first" = {
          expr = (listAll.choose {
            param = [ 10 20 30 ];
            state = { results = [ ]; pending = [ ]; };
          }).resume;
          expected = 10;
        };
        "choose-empty-aborts" = {
          expr = (listAll.choose {
            param = [ ];
            state = { results = [ ]; pending = [ ]; };
          }) ? abort;
          expected = true;
        };
        "choose-queues-rest" = {
          expr = builtins.length (listAll.choose {
            param = [ 10 20 30 ];
            state = { results = [ ]; pending = [ ]; };
          }).state.pending;
          expected = 2;
        };
      };
    };

    initialState = api.leaf {
      value = initialState;
      description = "choice.initialState: starting state `{ results = []; pending = []; }` for the listAll handler; pair with `handle` to run.";
      doc = "Initial state for the listAll handler.";
    };

  };
}
