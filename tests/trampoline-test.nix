# nix-effects trampoline integration tests
#
# Validates:
# 1. Basic operation (pure, single effect, chained effects)
# 2. O(1) stack depth with 10,000+ operations
# 3. Multiple effect types composing correctly
# 4. Effect return values flowing through continuations
# 5. handle combinator with ret clause
# 6. adapt for handler state composition
# 7. FTCQueue-based bind correctness
{ lib, fx }:

let
  inherit (fx) pure bind send run handle adapt adaptHandlers;

  # Helper: build a chain of n identical effect operations
  buildChain = name: param: n:
    if n <= 0 then pure null
    else bind (send name param) (_: buildChain name param (n - 1));

  # -- Test 1: Pure computation, no effects --
  pureComputation =
    let result = run (pure 42) {} {};
    in result.value == 42;

  # -- Test 2: Single effect --
  singleEffect =
    let
      result = run (send "double" 21) {
        double = { param, state }: { resume = param * 2; inherit state; };
      } null;
    in result.value == 42;

  # -- Test 3: Simple counter — 10 increments --
  simpleCounter =
    let
      result = run (buildChain "inc" 1 10) {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 10;

  # -- Test 4: 10,000 operations — validates O(1) stack depth --
  tenThousandOps =
    let
      result = run (buildChain "inc" 1 10000) {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 10000;

  # -- Test 5: 100,000 operations — stress test --
  hundredThousandOps =
    let
      result = run (buildChain "inc" 1 100000) {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 100000;

  # -- Test 6: Multiple effect types compose --
  multipleEffects =
    let
      comp =
        bind (send "get" null) (counter:
        bind (send "log" "step ${toString counter}") (_:
        bind (send "inc" 1) (_:
        bind (send "get" null) (newCounter:
        pure { oldCounter = counter; newCounter = newCounter; }))));

      result = run comp {
        get = { param, state }: { resume = state.counter; inherit state; };
        inc = { param, state }: {
          resume = null;
          state = state // { counter = state.counter + param; };
        };
        log = { param, state }: {
          resume = null;
          state = state // { logs = state.logs ++ [ param ]; };
        };
      } { counter = 0; logs = []; };
    in result.value.oldCounter == 0
       && result.value.newCounter == 1
       && result.state.logs == [ "step 0" ];

  # -- Test 7: Effect return values flow through continuations --
  returnValueFlow =
    let
      comp =
        bind (send "add" { a = 10; b = 20; }) (sum:
        bind (send "double" sum) (doubled:
        bind (send "negate" doubled) (negated:
        pure { inherit sum doubled negated; })));

      result = run comp {
        add = { param, state }: { resume = param.a + param.b; inherit state; };
        double = { param, state }: { resume = param * 2; inherit state; };
        negate = { param, state }: { resume = 0 - param; inherit state; };
      } null;
    in result.value.sum == 30
       && result.value.doubled == 60
       && result.value.negated == (0 - 60);

  # -- Test 8: Stateful accumulation across many effects --
  statefulAccumulation =
    let
      # Compute sum 1 + 2 + ... + 100 via effects
      sumChain = n:
        if n <= 0 then pure null
        else bind (send "add" n) (_: sumChain (n - 1));

      result = run (sumChain 100) {
        add = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 5050;  # Gauss's formula: 100*101/2

  # -- Test 9: Early termination via pure in middle of chain --
  earlyPure =
    let
      comp =
        bind (send "inc" 1) (_:
        bind (pure 99) (x:
        pure x));

      result = run comp {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.value == 99 && result.state == 1;

  # -- Test 10: Bind with pure (no effects at all) --
  pureBindChain =
    let
      comp =
        bind (pure 1) (a:
        bind (pure 2) (b:
        bind (pure 3) (c:
        pure (a + b + c))));

      result = run comp {} null;
    in result.value == 6;

  # -- Test 11: handle combinator with custom return clause --
  handleWithReturn =
    let
      comp = bind (send "inc" 5) (_: send "inc" 3);
      result = handle {
        return = v: s: { value = "done:${toString s}"; state = s; };
        handlers = {
          inc = { param, state }: { resume = null; state = state + param; };
        };
        state = 0;
      } comp;
    in result.value == "done:8";

  # -- Test 12: adapt transforms handler state --
  adaptState =
    let
      # Inner handler works with integer state
      incHandler = { param, state }: { resume = null; state = state + param; };

      # Adapt to work with { counter, logs } parent state
      adapted = adapt {
        get = s: s.counter;
        set = s: c: s // { counter = c; };
      } incHandler;

      comp = buildChain "inc" 1 5;
      result = run comp { inc = adapted; } { counter = 0; logs = []; };
    in result.state.counter == 5 && result.state.logs == [];

  # -- Test 13: adaptHandlers adapts entire handler set --
  adaptHandlersTest =
    let
      innerHandlers = {
        inc = { param, state }: { resume = null; state = state + param; };
        get = { param, state }: { resume = state; inherit state; };
      };

      adapted = adaptHandlers {
        get = s: s.n;
        set = s: n: s // { inherit n; };
      } innerHandlers;

      comp =
        bind (send "inc" 10) (_:
        bind (send "get" null) (val:
        pure val));

      result = run comp adapted { n = 5; extra = true; };
    in result.value == 15 && result.state.extra == true;

  # -- Test 14: FTCQueue correctness — left-nested bind --
  leftNestedBind =
    let
      # Build a left-nested chain: bind (bind (bind (send ...) f1) f2) f3
      leftChain = n: acc:
        if n <= 0 then acc
        else leftChain (n - 1) (bind acc (_: send "inc" 1));

      comp = leftChain 100 (send "inc" 1);
      result = run comp {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 101;  # 100 + 1 initial

  # -- Test: qApp consecutive Pure chain (stress test) --
  # One effect followed by 5000 pure binds: qApp chains all Pure returns
  # within a single trampoline step, exercising the recursive Pure path
  qAppPureChain =
    let
      comp = builtins.foldl'
        (acc: _: bind acc (x: pure (x + 1)))
        (send "start" 0)
        (lib.range 1 5000);
      result = run comp {
        start = { param, state }: { resume = param; inherit state; };
      } null;
    in result.value == 5000;

  # -- Test 16: viewlGo deep left-nested bind (stress test) --
  # 1000-deep left-nested bind chain
  viewlGoLeftNested =
    let
      leftChain = n: acc:
        if n <= 0 then acc
        else leftChain (n - 1) (bind acc (_: send "inc" 1));
      comp = leftChain 1000 (send "inc" 1);
      result = run comp {
        inc = { param, state }: { resume = null; state = state + param; };
      } 0;
    in result.state == 1001;

in {
  inherit pureComputation singleEffect simpleCounter
          tenThousandOps hundredThousandOps
          multipleEffects returnValueFlow
          statefulAccumulation earlyPure pureBindChain
          handleWithReturn adaptState adaptHandlersTest
          leftNestedBind
          qAppPureChain viewlGoLeftNested;

  allPass = pureComputation && singleEffect && simpleCounter
            && tenThousandOps && hundredThousandOps
            && multipleEffects && returnValueFlow
            && statefulAccumulation && earlyPure && pureBindChain
            && handleWithReturn && adaptState && adaptHandlersTest
            && leftNestedBind
            && qAppPureChain && viewlGoLeftNested;
}
