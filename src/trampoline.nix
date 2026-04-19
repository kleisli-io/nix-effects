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
# After handling an effect, the continuation queue is processed inline via
# recursive applyQueue, keeping 1 genericClosure step per effect. For deep
# pure chains (>500 continuations), applyQueue falls back to a
# genericClosure-based qAppSlow for stack safety.
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
  inherit (fx.comp) pure impure isPure isComp;
  inherit (api) mk;

  # -- Queue application --
  #
  # Applies continuations left-to-right until hitting Impure or exhausting
  # the queue. Recursive with a depth limit of 500: beyond that, falls back
  # to genericClosure-based qAppSlow for stack safety. Processing the queue
  # inside the trampoline operator keeps 1 genericClosure step per effect.

  applyQueue = q: val: depth:
    let
      vl = queue.viewl q;
      result = vl.head val;
    in
      if vl.tail == null then result
      else if !(isPure result) then
        impure result.effect (queue.append result.queue vl.tail)
      else if depth >= 500 then
        # Deep pure chain: switch to genericClosure for stack safety.
        qAppSlow vl.tail result.value
      else
        applyQueue vl.tail (builtins.seq result.value result.value) (depth + 1);

  # genericClosure-based queue application for deep pure chains (>500
  # continuations). Iterates via genericClosure for stack safety.
  qAppSlow = q: val:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _queue = q; _val = val; }];
        operator = state:
          let
            vl = queue.viewl state._queue;
            result = vl.head state._val;
          in
            if vl.tail != null && isPure result
            then [{ key = builtins.seq result.value (state.key + 1);
                    _queue = vl.tail; _val = result.value; }]
            else [];
      };
      last = lib.last steps;
      vl = queue.viewl last._queue;
      result = vl.head last._val;
    in
      if vl.tail == null then result
      else impure result.effect (queue.append result.queue vl.tail);

  # -- Interpreter --

  resumeWithQueue = q: value:
    if q._variant == "Identity" then pure value
    else applyQueue q value 0;

  # Resume with a value or computation. If the resume is a computation,
  # splice its effects before the continuation queue. This enables
  # effectful handlers: handlers that return computations to be handled
  # before the continuation runs.
  resumeCompOrValue = q: r:
    if isComp r then
      if isPure r then
        resumeWithQueue q r.value
      else
        # Impure: append original continuation queue to computation's queue.
        # The computation's effects run first; when it reaches Pure,
        # the original continuation picks up the result.
        impure r.effect (queue.append r.queue q)
    else
      resumeWithQueue q r;

  interpret = { comp, handlers, initialState }:
    let
      steps = builtins.genericClosure {
        startSet = [{
          key = 0;
          _comp = comp;
          _state = initialState;
        }];
        operator = step:
          if isPure step._comp then []
          else
            let
              eff = step._comp.effect;
              handler = localHandler handlers eff;
              result = 
                if handler == null 
                then 
                  if eff.name == "has-handler"
                  then { resume = false; state = step._state; }
                  else throw "nix-effects: unhandled effect '${eff.name}'"
                else handler {
                  param = eff.param;
                  state = step._state;
                };
              newState = if result ? state then result.state
                else throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
              # deepSeq newState in key: genericClosure forces key for dedup,
              # which forces newState, breaking the thunk chain.
              k = builtins.deepSeq newState (step.key + 1);
            in
              if result ? abort then
                [{ key = k; _comp = pure result.abort; _state = newState; }]
              else if result ? resume then
                [{ key = k;
                   _comp = resumeCompOrValue step._comp.queue result.resume;
                   _state = newState; }]
              else
                throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }";
      };
      final = lib.last steps;
    in { value = final._comp.value; state = final._state; };

  # -- Selective interpreter (handler rotation) --

  localHandler = handlers: eff:
    if eff.name == "has-handler" then
      if handlers ? ${eff.param}
      then { param, state }: { inherit state; resume = true; }
      else null # causes has-handler to rotate up
    else
      handlers.${eff.name} or null;

  effectRotateSlow = { comp, handlers, state, done }:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _comp = comp; _state = state; }];
        operator = step:
          if isPure step._comp then []
          else
            let
              eff = step._comp.effect;
              handler = localHandler handlers eff;
            in if handler != null then
              let
                result = handler {
                  param = eff.param;
                  state = step._state;
                };
                newState = if result ? state then result.state
                  else throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
                k = builtins.deepSeq newState (step.key + 1);
              in
                if result ? abort then
                  [{ key = k; _comp = pure (done result.abort newState); _state = newState; }]
                else if result ? resume then
                  [{ key = k;
                     _comp = resumeCompOrValue step._comp.queue result.resume;
                     _state = newState; }]
                else
                  throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }"
            else [];
      };
      last = lib.last steps;
    in
      if isPure last._comp then pure (done last._comp.value last._state)
      else
        impure last._comp.effect (queue.singleton (value:
          effectRotate {
            comp = resumeWithQueue last._comp.queue value;
            handlers = handlers;
            state = last._state;
            inherit done;
          } 0));

  effectRotate = { comp, handlers, state, done }: depth:
    if isPure comp then pure (done comp.value state)
    else
      let
        eff = comp.effect;
        handler = localHandler handlers eff;
      in if handler != null then
        let
          result = handler {
            param = eff.param;
            inherit state;
          };
          newState = if result ? state then result.state
            else throw "nix-effects: handler for '${eff.name}' must include 'state' in return value";
        in
          if result ? abort then
            pure (done result.abort newState)
          else if result ? resume then
            if depth >= 500 then
              effectRotateSlow {
                comp = resumeCompOrValue comp.queue result.resume;
                inherit handlers done;
                state = newState;
              }
            else
              effectRotate {
                comp = resumeCompOrValue comp.queue result.resume;
                inherit handlers done;
                state = newState;
              } (depth + 1)
          else
            throw "nix-effects: handler for '${eff.name}' must return { resume; state; } or { abort; state; }"
      else
        impure eff (queue.singleton (value:
          effectRotate {
            comp = resumeWithQueue comp.queue value;
            inherit handlers state done;
          } 0));

  run = mk {
    doc = ''
      Run a computation through the genericClosure trampoline.

      ```
      run : Computation a -> Handlers -> State -> { value : a, state : State }
      ```

      **Arguments:**
      - `comp` — the freer monad computation to interpret
      - `handlers` — `{ effectName = { param, state }: { resume | abort, state }; ... }`
      - `initialState` — starting state passed to handlers

      Handlers must return one of:

      ```
      { resume = value; state = newState; }  -- invoke continuation with value
      { abort  = value; state = newState; }  -- discard continuation, halt
      ```

      This is the defunctionalized encoding of Plotkin & Pretnar (2009):
      `resume` ≡ invoke continuation k(v), `abort` ≡ discard k.

      Stack depth: O(1) — constant regardless of computation length.
      Time: O(n) where n = number of effects in the computation.
    '';
    value = comp: handlers: initialState:
      assert (isComp comp)
        || throw "nix-effects: run expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      interpret { inherit comp handlers initialState; };
  };

  # -- Handler combinator --

  handle = mk {
    doc = ''
      Trampolined handler combinator with return clause.

      ```
      handle : { return?, handlers, state? } -> Computation a -> { value, state }
      ```

      Follows Kiselyov & Ishii's `handle_relay` pattern but trampolined
      via genericClosure for O(1) stack depth.

      **Arguments** (attrset):
      - `return` — `value -> state -> { value, state }`. How to transform the final Pure value. Default: identity.
      - `handlers` — `{ effectName = { param, state }: { resume | abort, state }; }`. Each must return `{ resume; state; }` or `{ abort; state; }`.
      - `state` — initial handler state. Default: null.
    '';
    value = {
      return ? (value: state: { inherit value state; }),
      handlers,
      state ? null,
    }: comp:
      assert (isComp comp)
        || throw "nix-effects: handle expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      let r = interpret { inherit comp handlers; initialState = state; };
      in return r.value r.state;
    tests = {
      "handle-with-default-return" = {
        expr =
          let
            send' = name: param:
              fx.comp.impure { inherit name param; } (fx.queue.singleton pure);
            comp = send' "double" 21;
            result = handle {
              handlers.double = { param, state }: { resume = param * 2; inherit state; };
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-with-custom-return" = {
        expr =
          let
            comp = pure 21;
            result = handle {
              return = v: s: { value = v * 2; state = s; };
              handlers = {};
            } comp;
          in result.value;
        expected = 42;
      };
      "handle-abort-discards-continuation" = {
        expr =
          let
            send' = name: param:
              fx.comp.impure { inherit name param; } (fx.queue.singleton pure);
            kernelBind = comp: f:
              if isPure comp then f comp.value
              else fx.comp.impure comp.effect (fx.queue.snoc comp.queue f);
            comp = kernelBind (send' "fail" "boom") (_: send' "get" null);
            result = handle {
              handlers = {
                fail = { param, state }: { abort = { error = param; }; inherit state; };
                get = { param, state }: { resume = state; inherit state; };
              };
            } comp;
          in result.value;
        expected = { error = "boom"; };
      };
      "effectful-resume-runs-sub-computation" = {
        expr =
          let
            send' = fx.kernel.send;
            bind' = fx.kernel.bind;
            comp = send' "outer" null;
            result = handle {
              handlers = {
                "outer" = { param, state }: {
                  resume = bind' (send' "inner" 10) (x: pure (x * 2));
                  inherit state;
                };
                "inner" = { param, state }: {
                  resume = param + 1;
                  inherit state;
                };
              };
            } comp;
          in result.value;
        expected = 22;
      };
      "effectful-resume-threads-state" = {
        expr =
          let
            send' = fx.kernel.send;
            bind' = fx.kernel.bind;
            comp = send' "resolve" null;
            result = handle {
              handlers = {
                "resolve" = { param, state }: {
                  resume = bind' (send' "count" null) (_: send' "count" null);
                  state = state // { resolved = true; };
                };
                "count" = { param, state }: {
                  resume = null;
                  state = state // { n = (state.n or 0) + 1; };
                };
              };
              state = {};
            } comp;
          in { n = result.state.n; resolved = result.state.resolved; };
        expected = { n = 2; resolved = true; };
      };
      "effectful-resume-with-continuation" = {
        expr =
          let
            send' = fx.kernel.send;
            bind' = fx.kernel.bind;
            comp = bind' (send' "fetch" null) (x: pure (x + 100));
            result = handle {
              handlers = {
                "fetch" = { param, state }: {
                  resume = bind' (send' "db" null) (row: pure row.value);
                  inherit state;
                };
                "db" = { param, state }: {
                  resume = { value = 42; };
                  inherit state;
                };
              };
            } comp;
          in result.value;
        expected = 142;
      };
      "plain-resume-unchanged" = {
        expr =
          let
            comp = fx.kernel.send "x" 5;
            result = handle {
              handlers.x = { param, state }: { resume = param + 1; inherit state; };
            } comp;
          in result.value;
        expected = 6;
      };
    };
  };

  rotate = mk {
    doc = ''
      Selectively handle known effects and rotate unknown effects outward.

      ```
      rotate : { return?, handlers, state? } -> Computation a -> Computation b
      ```

      If the current effect has a matching handler, the handler is applied.
      If it does not match, the effect is re-suspended and its continuation
      is wrapped so handling resumes after that effect is interpreted by an
      outer handler.

      This corresponds to the Kyo-style handler rotation law
      from https://gist.github.com/vic/3a7f52974a28675dbaf40b34bec74787:

      ```
      handle(tag1, suspend(tag2, i, k), f) = suspend(tag2, i, x => handle(tag1, k(x), f))` for `tag1 != tag2
      ```
    '';
    value = {
      return ? (value: state: { inherit value state; }),
      handlers,
      state ? null,
    }: comp:
      assert (isComp comp)
        || throw "nix-effects: rotate expects a computation (Pure or Impure), got ${builtins.typeOf comp}";
      effectRotate {
        inherit comp handlers state;
        done = return;
      } 0;
    tests = {
      "rotate-matches-handled-effect" = {
        expr =
          let
            comp = fx.kernel.send "inc" 1;
            rotated = rotate {
              handlers = {
                inc = { param, state }: { resume = null; state = state + param; };
              };
              state = 0;
            } comp;
            result = handle { handlers = {}; } rotated;
          in result.value.state;
        expected = 1;
      };
      "rotate-preserves-unhandled-effect" = {
        expr =
          let
            comp = fx.kernel.send "outer" 7;
            rotated = rotate {
              handlers = {
                inc = { param, state }: { resume = null; state = state + param; };
              };
              state = 0;
            } comp;
          in rotated.effect.name;
        expected = "outer";
      };
      "rotate-handles-after-outer-resume" = {
        expr =
          let
            comp = fx.kernel.bind (fx.kernel.send "outer" 7) (_:
              fx.kernel.send "inc" 1);
            rotated = rotate {
              handlers = {
                inc = { param, state }: { resume = null; state = state + param; };
              };
              state = 0;
            } comp;
            result = handle {
              handlers = {
                outer = { param, state }: { resume = param * 2; inherit state; };
              };
            } rotated;
          in result.value.state;
        expected = 1;
      };
      "effectful-resume-in-rotate" = {
        expr =
          let
            send' = fx.kernel.send;
            bind' = fx.kernel.bind;
            comp = send' "a" null;
            rotated = rotate {
              handlers = {
                "a" = { param, state }: {
                  resume = bind' (send' "b" 5) (x: pure (x + 1));
                  inherit state;
                };
                "b" = { param, state }: {
                  resume = param * 2;
                  inherit state;
                };
              };
            } comp;
            result = handle { handlers = {}; } rotated;
          in result.value.value;
        expected = 11;
      };
    };
  };

in mk {
  doc = "Trampolined interpreter using builtins.genericClosure for O(1) stack depth.";
  value = {
    inherit run handle rotate;
  };
}
