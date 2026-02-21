# nix-effects error path and abort behavior tests
#
# Validates that the trampoline rejects invalid handler protocols,
# throws on unhandled effects, and that abort correctly discards
# continuations while preserving prior state mutations.
{ lib, fx }:

let
  inherit (fx) pure bind send run handle seq;
  inherit (fx.effects) state error conditions;

  # Returns true if evaluating expr throws
  throws = expr:
    let result = builtins.tryEval (builtins.deepSeq expr expr);
    in !result.success;

  stateHandlers = {
    get = { param, state }: { resume = state; inherit state; };
    put = { param, state }: { resume = null; state = param; };
  };

  incHandler = { param, state }: { resume = null; state = state + param; };

  # =========================================================================
  # UNHANDLED EFFECT ERRORS
  # =========================================================================

  # Both run and handle must throw on effects with no matching handler
  unhandledEffectRunThrows =
    throws (run (send "nonexistent" null) {} null);

  unhandledEffectHandleThrows =
    throws (handle { handlers = {}; } (send "nonexistent" null));

  # Handler exists for first effect but not the second
  partialHandlerThrows =
    throws (run (bind (send "get" null) (_: send "missing" null)) stateHandlers 0);

  # Parametric: multiple different missing effect names all throw
  unhandledEffectNames = builtins.all (name:
    throws (run (send name null) {} null)
  ) [ "foo" "bar" "get" "put" "error" "condition" ];

  # =========================================================================
  # BAD HANDLER PROTOCOL
  # =========================================================================

  # Handler returns {value, state} (pre-resume/abort protocol) — must throw
  badProtocolValueThrows =
    throws (run (send "x" null) {
      x = { param, state }: { value = 42; inherit state; };
    } null);

  # Handler returns empty attrset — must throw
  badProtocolEmptyThrows =
    throws (run (send "x" null) {
      x = { param, state }: {};
    } null);

  # Handler returns state but no resume or abort — must throw
  badProtocolStateOnlyThrows =
    throws (run (send "x" null) {
      x = { param, state }: { state = 0; };
    } null);

  # Parametric: all malformed handler return shapes throw
  allBadProtocolsThrow = builtins.all (handler:
    throws (run (send "x" null) { x = handler; } null)
  ) [
    ({ param, state }: { value = 1; inherit state; })
    ({ param, state }: {})
    ({ param, state }: { state = 0; })
  ];

  # When handler returns both resume and abort, abort wins (first branch taken)
  bothResumeAndAbortTakesAbort = {
    expr =
      let
        result = run (send "x" null) {
          x = { param, state }: { resume = 1; abort = 2; state = 0; };
        } null;
      in result.value;
    expected = 2;
  };

  # =========================================================================
  # ERROR EFFECT: STRICT HANDLER
  # =========================================================================

  # error.strict throws on raise with various messages
  errorStrictThrowsParametric = builtins.all (msg:
    throws (handle { handlers = error.strict; state = null; } (error.raise msg))
  ) [ "boom" "" "unexpected token" "field required" ];

  # error.strict throws on raiseWith (context variant)
  errorStrictWithContextThrows = builtins.all (ctx:
    throws (handle { handlers = error.strict; state = null; }
      (error.raiseWith ctx "message"))
  ) [ "parser" "validator" "runtime" "" ];

  # error.strict mid-chain: first error stops evaluation
  errorStrictMidChainThrows =
    throws (handle { handlers = error.strict // stateHandlers; state = 0; }
      (bind (send "put" 5) (_:
        bind (error.raise "fail") (_:
          send "put" 999))));

  # =========================================================================
  # CONDITIONS: FAIL HANDLER
  # =========================================================================

  # conditions.fail throws on signal with various condition names
  conditionsFailThrowsParametric = builtins.all (name:
    throws (handle { handlers = conditions.fail; state = null; }
      (conditions.signal name {} []))
  ) [ "division-by-zero" "file-not-found" "type-error" "unknown" ];

  # =========================================================================
  # ERROR.RESULT: ABORT-BASED HANDLER
  # =========================================================================

  # error.result aborts with Error tag, discarding continuation
  errorResultAbortsTest = {
    expr =
      let
        comp = bind (error.raise "boom") (_: pure "unreachable");
        result = handle { handlers = error.result; state = null; } comp;
      in result.value;
    expected = { _tag = "Error"; message = "boom"; context = ""; };
  };

  # error.result with context carries context through
  errorResultWithContextTest = {
    expr =
      let
        result = handle { handlers = error.result; state = null; }
          (error.raiseWith "validator" "field required");
      in { tag = result.value._tag; ctx = result.value.context; msg = result.value.message; };
    expected = { tag = "Error"; ctx = "validator"; msg = "field required"; };
  };

  # Parametric: error.result aborts for all messages
  errorResultParametric = builtins.all (msg:
    let result = handle { handlers = error.result; state = null; } (error.raise msg);
    in result.value._tag == "Error" && result.value.message == msg
  ) [ "a" "boom" "" "null pointer" ];

  # Pure computation passes through error.result unaffected
  errorResultPurePassesTest = {
    expr = (handle { handlers = error.result; state = null; } (pure 42)).value;
    expected = 42;
  };

  # Parametric: various pure values pass through
  errorResultPureParametric = builtins.all (v:
    (handle { handlers = error.result; state = null; } (pure v)).value == v
  ) [ 0 42 "hello" null true [ 1 2 3 ] ];

  # error.result abort discards continuation, state unchanged
  errorResultDiscardsContTest = {
    expr =
      let
        comp = bind (error.raiseWith "step1" "fail") (_: send "put" 999);
        result = handle { handlers = error.result // stateHandlers; state = 0; } comp;
      in result.state;
    expected = 0;
  };

  # =========================================================================
  # ABORT SEMANTICS
  # =========================================================================

  stopHandler = { param, state }: { abort = param; inherit state; };

  # Abort at start: no continuations run, state untouched
  abortAtStartTest = {
    expr =
      let
        comp = bind (send "stop" "done") (_:
          bind (send "inc" 1) (_: send "inc" 1));
        result = run comp { stop = stopHandler; inc = incHandler; } 0;
      in { value = result.value; state = result.state; };
    expected = { value = "done"; state = 0; };
  };

  # Abort mid-chain: state reflects ops before abort, not after
  abortMidChainTest = {
    expr =
      let
        comp = bind (send "inc" 5) (_:
          bind (send "inc" 3) (_:
            bind (send "stop" "halted") (_:
              send "inc" 100)));
        result = run comp { inc = incHandler; stop = stopHandler; } 0;
      in { value = result.value; state = result.state; };
    expected = { value = "halted"; state = 8; };
  };

  # Parametric: abort at various chain positions
  abortAtPositionN = builtins.all (n:
    let
      # Build chain: n increments, then abort, then more increments
      before = builtins.genList (_: send "inc" 1) n;
      after = builtins.genList (_: send "inc" 1) 5;
      allOps = before ++ [ (send "stop" "halt") ] ++ after;
      comp = builtins.foldl' (acc: op: bind acc (_: op)) (pure null) allOps;
      result = run comp { inc = incHandler; stop = stopHandler; } 0;
    in result.state == n && result.value == "halt"
  ) [ 0 1 3 5 10 ];

  # Abort value can be any type
  abortValueTypes = builtins.all (val:
    let
      result = run (send "stop" val)
        { stop = { param, state }: { abort = param; inherit state; }; } null;
    in result.value == val
  ) [ null 42 "string" true { x = 1; } [ 1 2 ] ];

  # =========================================================================
  # KERNEL.SEQ
  # =========================================================================

  seqEffectsTest = {
    expr =
      let
        comp = seq [ (send "inc" 1) (send "inc" 2) (send "inc" 3) ];
        result = run comp { inc = incHandler; } 0;
      in result.state;
    expected = 6;
  };

  seqEmptyTest = {
    expr = (run (seq []) {} null).value;
    expected = null;
  };

  seqReturnsLastTest = {
    expr =
      let
        valHandler = { param, state }: { resume = param; inherit state; };
        comp = seq [ (send "val" 10) (send "val" 20) (send "val" 30) ];
      in (run comp { val = valHandler; } null).value;
    expected = 30;
  };

  # Parametric: seq accumulates state correctly for various lengths
  seqParametricLengths = builtins.all (n:
    let
      comp = seq (builtins.genList (_: send "inc" 1) n);
      result = run comp { inc = incHandler; } 0;
    in result.state == n
  ) [ 0 1 5 10 50 ];

  # =========================================================================
  # HANDLER COMPOSITION
  # =========================================================================

  handlerMergeRightBiasTest = {
    expr =
      let
        h1 = { eff = { param, state }: { resume = "left"; inherit state; }; };
        h2 = { eff = { param, state }: { resume = "right"; inherit state; }; };
      in (run (send "eff" null) (h1 // h2) null).value;
    expected = "right";
  };

  # =========================================================================
  # MALFORMED INPUT VALIDATION
  # =========================================================================

  # run with non-computation inputs throws with clear message
  runNullThrows = throws (run null {} null);
  runIntThrows = throws (run 42 {} null);
  runStringThrows = throws (run "bad" {} null);
  runAttrsetNoTagThrows = throws (run { x = 1; } {} null);

  # handle with non-computation inputs throws
  handleNullThrows = throws (handle { handlers = {}; } null);
  handleIntThrows = throws (handle { handlers = {}; } 42);

  # =========================================================================
  # EFFECT NAME COLLISION
  # =========================================================================

  # Effect name collision: attrset merge means last handler wins
  effectNameCollision = {
    expr =
      let
        h1 = { eff = { param, state }: { resume = "first"; inherit state; }; };
        h2 = { eff = { param, state }: { resume = "second"; inherit state; }; };
        result = run (send "eff" null) (h1 // h2) null;
      in result.value;
    expected = "second";
  };

  # Same-name effects from different "modules" collide silently
  effectCollisionSilent =
    let
      stateGet = { get = { param, state }: { resume = state; inherit state; }; };
      userGet  = { get = { param, state }: { resume = "user"; inherit state; }; };
    in (run (send "get" null) (stateGet // userGet) 42).value == "user";

  # =========================================================================
  # COLLECT RESULTS
  # =========================================================================

  boolTests = {
    inherit unhandledEffectRunThrows unhandledEffectHandleThrows
            partialHandlerThrows unhandledEffectNames
            badProtocolValueThrows badProtocolEmptyThrows
            badProtocolStateOnlyThrows allBadProtocolsThrow
            errorStrictThrowsParametric errorStrictWithContextThrows
            errorStrictMidChainThrows
            conditionsFailThrowsParametric
            errorResultParametric errorResultPureParametric
            abortAtPositionN abortValueTypes
            seqParametricLengths
            runNullThrows runIntThrows runStringThrows runAttrsetNoTagThrows
            handleNullThrows handleIntThrows
            effectCollisionSilent;
  };

  exprTests = {
    inherit errorResultAbortsTest errorResultWithContextTest
            errorResultPurePassesTest errorResultDiscardsContTest
            abortAtStartTest abortMidChainTest
            bothResumeAndAbortTakesAbort
            seqEffectsTest seqEmptyTest seqReturnsLastTest
            handlerMergeRightBiasTest
            effectNameCollision;
  };

  exprResults = builtins.mapAttrs (_: test:
    let actual = test.expr; in
    { inherit actual; expected = test.expected; pass = actual == test.expected; }
  ) exprTests;

  exprFailed = lib.filterAttrs (_: r: !r.pass) exprResults;

  boolAllPass = builtins.all (n: boolTests.${n}) (builtins.attrNames boolTests);
  exprAllPass = (builtins.length (builtins.attrNames exprFailed)) == 0;

in boolTests // exprTests // {
  allPass = boolAllPass && exprAllPass;
}
