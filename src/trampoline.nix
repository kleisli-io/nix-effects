# nix-effects trampoline: O(1) stack depth interpreter
#
# Uses builtins.genericClosure as a worklist-style trampoline.
# This is the key innovation: defunctionalize the recursive handler
# into an iterative loop via Nix's only built-in iterative primitive.
#
# Theory: Reynolds (1972) defunctionalization; Van Horn & Might (2010) store-allocated
# continuations + worklist iteration = bounded stack.
# Gibbons (2021) "CPS, Defunctionalization, Accumulations, and Associativity" —
# the hidden precondition is associativity of the operation being accumulated.
#
# Continuations are FTCQueue-based: each trampoline step calls qApp to
# process the continuation queue, yielding the next computation node
# (Pure or Impure).
#
# Critical implementation detail: genericClosure only forces the `key` field
# (for deduplication). Handler state and continuation values would accumulate
# as thunk chains of depth N, blowing the stack when the final result is
# accessed. We break this chain by making `key` depend on `builtins.deepSeq`
# of the new state — since genericClosure forces `key`, this eagerly evaluates
# the state at each step. Validated: 1,000,000 operations in ~3 seconds.
{ lib, fx, api, ... }:

let
  queue = fx.queue;
  inherit (api) mk;

  # Pure constructor needed for abort path (avoids circular import)
  mkPure = value: { _tag = "Pure"; inherit value; };

  run = mk {
    doc = ''
      Run a computation through the genericClosure trampoline.

      comp: Computation a — the freer monad computation to interpret
      handlers: { effectName = { param, state } -> { resume | abort, state }; ... }
      initialState: starting state passed to handlers

      Returns: { value: a, state: finalState }

      Handlers must return one of:
        { resume = value; state = newState; }  — invoke continuation with value
        { abort  = value; state = newState; }  — discard continuation, halt

      This is the defunctionalized encoding of Plotkin & Pretnar (2009):
      resume ≡ invoke continuation k(v), abort ≡ discard k.

      Stack depth: O(1) — constant regardless of computation length.
      Time: O(n) where n = number of effects in the computation.
    '';
    value = comp: handlers: initialState:
      assert (builtins.isAttrs comp && comp ? _tag)
        || builtins.throw "nix-effects: run expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      let
        steps = builtins.genericClosure {
          startSet = [{
            key = 0;
            _comp = comp;
            _state = initialState;
          }];
          operator = step:
            if step._comp._tag == "Pure"
            then []
            else
              let
                eff = step._comp.effect;
                handler = handlers.${eff.name} or
                  (builtins.throw "nix-effects: unhandled effect '${eff.name}'");
                result = handler {
                  param = eff.param;
                  state = step._state;
                };
                newState = if result ? state then result.state
                  else builtins.throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
              in
                if result ? abort then
                  # Non-resumption: discard continuation, return abort value
                  [{
                    key = builtins.deepSeq newState (step.key + 1);
                    _comp = mkPure result.abort;
                    _state = newState;
                  }]
                else if result ? resume then
                  # Resumption: feed value to continuation queue
                  let nextComp = queue.qApp step._comp.queue result.resume;
                  in [{
                    # deepSeq newState in key: genericClosure forces key for dedup,
                    # which forces newState, breaking the thunk chain.
                    key = builtins.deepSeq newState (step.key + 1);
                    _comp = nextComp;
                    _state = newState;
                  }]
                else
                  builtins.throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }";
        };
        final = lib.last steps;
      in {
        value = final._comp.value;
        state = final._state;
      };
  };

  # -- Handler combinator --

  handle = mk {
    doc = ''
      Trampolined handler combinator with return clause.

      Follows Kiselyov & Ishii's handle_relay pattern but trampolined
      via genericClosure for O(1) stack depth.

      Arguments (attrset):
        return: value -> state -> { value, state }
          How to transform the final Pure value. Default: identity.
        handlers: { effectName = { param, state } -> { resume | abort, state }; }
          Effect handlers. Each must return { resume; state; } or { abort; state; }.
        state: initial handler state. Default: null.

      Returns: comp -> { value, state }
    '';
    value = {
      return ? (value: state: { inherit value state; }),
      handlers,
      state ? null,
    }: comp:
      assert (builtins.isAttrs comp && comp ? _tag)
        || builtins.throw "nix-effects: handle expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      let
        steps = builtins.genericClosure {
          startSet = [{
            key = 0;
            _comp = comp;
            _state = state;
          }];
          operator = step:
            if step._comp._tag == "Pure"
            then []
            else
              let
                eff = step._comp.effect;
                handler = handlers.${eff.name} or
                  (builtins.throw "nix-effects: unhandled effect '${eff.name}'");
                result = handler {
                  param = eff.param;
                  state = step._state;
                };
                newState = if result ? state then result.state
                  else builtins.throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
              in
                if result ? abort then
                  [{
                    key = builtins.deepSeq newState (step.key + 1);
                    _comp = mkPure result.abort;
                    _state = newState;
                  }]
                else if result ? resume then
                  let nextComp = queue.qApp step._comp.queue result.resume;
                  in [{
                    key = builtins.deepSeq newState (step.key + 1);
                    _comp = nextComp;
                    _state = newState;
                  }]
                else
                  builtins.throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }";
        };
        final = lib.last steps;
      in return final._comp.value final._state;
    tests = {
      "handle-with-default-return" = {
        expr =
          let
            send' = name: param: {
              _tag = "Impure";
              effect = { inherit name param; };
              queue = queue.singleton (value: { _tag = "Pure"; inherit value; });
            };
            comp = send' "double" 21;
            result = handle.value {
              handlers.double = { param, state }: { resume = param * 2; inherit state; };
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-with-custom-return" = {
        expr =
          let
            comp = { _tag = "Pure"; value = 21; };
            result = handle.value {
              return = v: s: { value = v * 2; state = s; };
              handlers = {};
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-abort-discards-continuation" = {
        expr =
          let
            send' = name: param: {
              _tag = "Impure";
              effect = { inherit name param; };
              queue = queue.singleton (value: { _tag = "Pure"; inherit value; });
            };
            kernelBind = comp: f:
              if comp._tag == "Pure" then f comp.value
              else { _tag = "Impure"; inherit (comp) effect; queue = queue.snoc comp.queue f; };
            comp = kernelBind (send' "fail" "boom") (_: send' "get" null);
            result = handle.value {
              handlers = {
                fail = { param, state }: { abort = { error = param; }; inherit state; };
                get = { param, state }: { resume = state; inherit state; };
              };
            } comp;
          in result.value;
        expected = { error = "boom"; };
      };
    };
  };

in mk {
  doc = "Trampolined interpreter using builtins.genericClosure for O(1) stack depth.";
  value = {
    inherit run handle;
  };
}
