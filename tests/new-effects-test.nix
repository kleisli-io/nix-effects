# nix-effects integration tests for reader, writer, acc, choice
{ lib, fx }:

let
  inherit (fx) pure bind handle run;
  inherit (fx.effects) reader writer acc choice;

  # =========================================================================
  # READER EFFECT
  # =========================================================================

  readerAskTest = {
    expr =
      let
        comp = reader.ask;
        result = handle { handlers = reader.handler; state = { host = "localhost"; port = 8080; }; } comp;
      in result.value;
    expected = { host = "localhost"; port = 8080; };
  };

  readerAsksTest = {
    expr =
      let
        comp = reader.asks (env: env.port);
        result = handle { handlers = reader.handler; state = { host = "localhost"; port = 8080; }; } comp;
      in result.value;
    expected = 8080;
  };

  readerLocalTest = {
    expr =
      let
        comp = reader.local (e: e // { port = 9090; }) (reader.asks (e: e.port));
        result = handle { handlers = reader.handler; state = { host = "localhost"; port = 8080; }; } comp;
      in result.value;
    expected = 9090;
  };

  readerChainTest = {
    expr =
      let
        comp = bind (reader.asks (e: e.host)) (host:
          bind (reader.asks (e: e.port)) (port:
            pure "${host}:${toString port}"));
        result = handle { handlers = reader.handler; state = { host = "example.com"; port = 443; }; } comp;
      in result.value;
    expected = "example.com:443";
  };

  # Parametric: asks with various projections
  readerAsksParametric = builtins.all (key:
    let
      env = { a = 1; b = 2; c = 3; };
      result = handle { handlers = reader.handler; state = env; }
        (reader.asks (e: e.${key}));
    in result.value == env.${key}
  ) [ "a" "b" "c" ];

  # =========================================================================
  # WRITER EFFECT
  # =========================================================================

  writerTellTest = {
    expr =
      let
        comp = bind (writer.tell "hello") (_:
          bind (writer.tell "world") (_:
            pure "done"));
        result = handle { handlers = writer.handler; state = []; } comp;
      in { value = result.value; log = result.state; };
    expected = { value = "done"; log = [ "hello" "world" ]; };
  };

  writerTellAllTest = {
    expr =
      let
        comp = bind (writer.tellAll [ 1 2 ]) (_:
          bind (writer.tell 3) (_:
            writer.tellAll [ 4 5 ]));
        result = handle { handlers = writer.handler; state = []; } comp;
      in result.state;
    expected = [ 1 2 3 4 5 ];
  };

  writerEmptyTest = {
    expr =
      let
        result = handle { handlers = writer.handler; state = []; } (pure 42);
      in { value = result.value; log = result.state; };
    expected = { value = 42; log = []; };
  };

  # Parametric: tell n items accumulates n items
  writerParametric = builtins.all (n:
    let
      comp = builtins.foldl' (acc: i: bind acc (_: writer.tell i))
        (pure null) (builtins.genList (i: i) n);
      result = handle { handlers = writer.handler; state = []; } comp;
    in builtins.length result.state == n
  ) [ 0 1 5 10 ];

  # =========================================================================
  # ACCUMULATOR EFFECT
  # =========================================================================

  accEmitTest = {
    expr =
      let
        comp = bind (acc.emit 1) (_:
          bind (acc.emit 2) (_:
            bind (acc.emit 3) (_:
              acc.collect)));
        result = handle { handlers = acc.handler; state = []; } comp;
      in result.value;
    expected = [ 1 2 3 ];
  };

  accEmitAllTest = {
    expr =
      let
        comp = bind (acc.emitAll [ "a" "b" ]) (_:
          bind (acc.emit "c") (_:
            acc.collect));
        result = handle { handlers = acc.handler; state = []; } comp;
      in result.value;
    expected = [ "a" "b" "c" ];
  };

  accEmptyCollectTest = {
    expr =
      let result = handle { handlers = acc.handler; state = []; } acc.collect;
      in result.value;
    expected = [];
  };

  # Parametric: emit n items, collect gives n items
  accParametric = builtins.all (n:
    let
      comp = bind (builtins.foldl' (c: i: bind c (_: acc.emit i))
        (pure null) (builtins.genList (i: i) n)) (_: acc.collect);
      result = handle { handlers = acc.handler; state = []; } comp;
    in builtins.length result.value == n
  ) [ 0 1 5 10 ];

  # =========================================================================
  # CHOICE EFFECT
  # =========================================================================

  # choose resumes with first alternative
  chooseFirstTest = {
    expr =
      let
        comp = choice.choose [ 10 20 30 ];
        result = handle { handlers = choice.listAll; state = choice.initialState; } comp;
      in result.value;
    expected = 10;
  };

  # fail (choose []) aborts
  choiceFailTest = {
    expr =
      let
        comp = choice.fail;
        result = handle { handlers = choice.listAll; state = choice.initialState; } comp;
      in result.value;
    expected = null;
  };

  # guard true continues, guard false fails
  choiceGuardTrueTest = {
    expr =
      let
        comp = bind (choice.guard true) (_: pure 42);
        result = run comp {} null;
      in result.value;
    expected = 42;
  };

  choiceGuardFalseTest = {
    expr =
      let
        comp = bind (choice.guard false) (_: pure 42);
        result = handle { handlers = choice.listAll; state = choice.initialState; } comp;
      in result.value;
    expected = null;
  };

  # choose queues alternatives in pending
  choicePendingTest = {
    expr =
      let
        comp = choice.choose [ 1 2 3 ];
        result = handle { handlers = choice.listAll; state = choice.initialState; } comp;
      in builtins.length result.state.pending;
    expected = 2;
  };

  # =========================================================================
  # COMPOSITION: reader + writer combined
  # =========================================================================

  readerWriterComposedTest = {
    expr =
      let
        adaptedReader = fx.adaptHandlers {
          get = s: s.env;
          set = s: e: s // { env = e; };
        } reader.handler;

        adaptedWriter = fx.adaptHandlers {
          get = s: s.log;
          set = s: l: s // { log = l; };
        } writer.handler;

        comp = bind (reader.asks (e: e.name)) (name:
          bind (writer.tell "Hello, ${name}!") (_:
            pure name));

        result = handle {
          handlers = adaptedReader // adaptedWriter;
          state = { env = { name = "World"; }; log = []; };
        } comp;
      in { value = result.value; log = result.state.log; };
    expected = { value = "World"; log = [ "Hello, World!" ]; };
  };

  # =========================================================================
  # COLLECT RESULTS
  # =========================================================================

  boolTests = {
    inherit readerAsksParametric writerParametric accParametric;
  };

  exprTests = {
    inherit readerAskTest readerAsksTest readerLocalTest readerChainTest
            writerTellTest writerTellAllTest writerEmptyTest
            accEmitTest accEmitAllTest accEmptyCollectTest
            chooseFirstTest choiceFailTest
            choiceGuardTrueTest choiceGuardFalseTest choicePendingTest
            readerWriterComposedTest;
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
