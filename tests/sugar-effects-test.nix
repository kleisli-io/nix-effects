{ lib, fx }:

let
  inherit (fx) pure bind run handle kleisli;
  inherit (fx.effects) state error reader;
  inherit (fx.sugar) do steps letM;

  statePatternDesugared = {
    expr =
      let
        comp = bind state.get (n:
          bind (state.put (n + 1)) (_:
            bind state.get (n2:
              pure n2)));
        result = handle { handlers = state.handler; state = 0; } comp;
      in
      result.value;
    expected = 1;
  };

  # statePatternDo tests the composable `do` (Kleisli arrow). Apply it
  # to `null` to obtain the Computation, then hand it to `handle`.
  statePatternDo = {
    expr =
      let
        pipeline = do [
          (_: state.get)
          (n: state.put (n + 1))
          (_: state.get)
        ];
        comp = pipeline null;
        result = handle { handlers = state.handler; state = 0; } comp;
      in
      result.value;
    expected = 1;
  };

  statePatternDiv = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        comp = state.get
          / (n: state.put (n + 1))
          / (_: state.get);
        result = handle { handlers = state.handler; state = 0; } comp;
      in
      result.value;
    expected = 1;
  };

  statePatternEquivState = {
    expr =
      let
        d = handle { handlers = state.handler; state = 10; }
          (bind state.get (n:
            bind (state.put (n + 1)) (_:
              bind state.get (n2: pure n2))));
        s = handle { handlers = state.handler; state = 10; }
          ((do [ (_: state.get) (n: state.put (n + 1)) (_: state.get) ]) null);
      in
      { ds = d.state; ss = s.state; dv = d.value; sv = s.value; };
    expected = { ds = 11; ss = 11; dv = 11; sv = 11; };
  };

  errorPatternDesugared = {
    expr =
      let
        comp = bind (error.raiseWith "parser" "unexpected token") (_:
          bind (error.raiseWith "parser" "missing semicolon") (_:
            pure "ok"));
        result = handle { handlers = error.collecting; state = [ ]; } comp;
      in
      builtins.length result.state;
    expected = 2;
  };

  errorPatternDo = {
    expr =
      let
        pipeline = do [
          (_: error.raiseWith "parser" "unexpected token")
          (_: error.raiseWith "parser" "missing semicolon")
          (_: pure "ok")
        ];
        comp = pipeline null;
        result = handle { handlers = error.collecting; state = [ ]; } comp;
      in
      builtins.length result.state;
    expected = 2;
  };

  readerPatternDesugared = {
    expr =
      let
        comp = bind (reader.asks (e: e.host)) (host:
          bind (reader.asks (e: e.port)) (port:
            pure "${host}:${toString port}"));
        result = handle
          {
            handlers = reader.handler;
            state = { host = "example.com"; port = 443; };
          }
          comp;
      in
      result.value;
    expected = "example.com:443";
  };

  readerPatternLetM = {
    expr =
      let
        comp = letM
          {
            host = reader.asks (e: e.host);
            port = reader.asks (e: e.port);
          }
          (b: pure "${b.host}:${toString b.port}");
        result = handle
          {
            handlers = reader.handler;
            state = { host = "example.com"; port = 443; };
          }
          comp;
      in
      result.value;
    expected = "example.com:443";
  };

  # do [] is the identity Kleisli arrow (x: pure x).
  doEmpty = {
    expr = (run (do [ ] 42) { } null).value;
    expected = 42;
  };

  doSingleton = {
    expr = (run (do [ (x: pure (x + 1)) ] 41) { } null).value;
    expected = 42;
  };

  # Plain functions are auto-lifted to Kleisli arrows via `pure`.
  doAutoLift = {
    expr = (run (do [ (x: x + 1) (x: x * 2) ] 20) { } null).value;
    expected = 42;
  };

  # Plain and monadic steps compose uniformly.
  doMixed = {
    expr = (run (do [ (x: x + 1) (x: pure (x * 2)) ] 20) { } null).value;
    expected = 42;
  };

  # Kleisli composition of two `do` pipelines equals one merged pipeline.
  doComposable = {
    expr =
      let
        p1 = do [ (x: x + 1) ];
        p2 = do [ (x: x * 2) ];
        composed = kleisli p1 p2 20;
        merged = do [ (x: x + 1) (x: x * 2) ] 20;
      in
      (run composed { } null).value == (run merged { } null).value;
    expected = true;
  };

  # Data-last argument order enables point-free `map`.
  doPointFree = {
    expr =
      let
        inc = do [ (x: x + 1) ];
        results = map inc [ 1 2 3 ];
        resultValues = map (r: (run r { } null).value) results;
      in
      resultValues;
    expected = [ 2 3 4 ];
  };

  # `steps` preserves the original `do` semantics: sequence effects,
  # discard intermediate values.
  stepsSequences = {
    expr =
      let
        comp = steps [
          (_: state.get)
          (n: state.put (n + 10))
          (_: state.get)
        ];
        result = handle { handlers = state.handler; state = 5; } comp;
      in
      result.value;
    expected = 15;
  };

  divAssociativityTest = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        sugared = state.get / (n: pure (n + 1)) / (n: pure (n * 2));
        desugared = bind state.get (n: bind (pure (n + 1)) (n: pure (n * 2)));
        r1 = handle { handlers = state.handler; state = 10; } sugared;
        r2 = handle { handlers = state.handler; state = 10; } desugared;
      in
      r1.value == r2.value;
    expected = true;
  };

  divNotTopLevel = {
    expr = fx.sugar ? __div;
    expected = false;
  };

  divUnderOperators = {
    expr = fx.sugar.operators ? __div;
    expected = true;
  };

  reexportsPresent = {
    expr = builtins.all (k: fx.sugar ? ${k})
      [ "pure" "bind" "run" "handle" "map" "seq" "pipe" "kleisli" "do" "steps" "letM" ];
    expected = true;
  };

  withSugarTest = {
    expr =
      let s = fx.sugar; in with s;
      (run (do [ (_: pure 1) (x: pure (x + 1)) (x: pure (x * 10)) ] null) { } null).value;
    expected = 20;
  };

  fullSugarWith = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        comp = with fx.sugar;
          state.get / (s: state.put (s * 2)) / (_: state.get);
        result = handle { handlers = state.handler; state = 5; } comp;
      in
      result.value;
    expected = 10;
  };

  withOperatorsDoesNotActivateDiv = {
    expr = with fx.sugar.operators; (6 / 2);
    expected = 3;
  };

  operatorOnly = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        comp = state.get / (s: state.put (s + 7)) / (_: state.get);
        result = handle { handlers = state.handler; state = 3; } comp;
      in
      result.value;
    expected = 10;
  };

  # combinatorsOnly exercises both the composable `do` and the
  # sequencing `steps`.
  combinatorsOnly = {
    expr =
      let
        inherit (fx.sugar) do steps letM;
        compDo = (do [
          (_: state.get)
          (n: state.put (n * 3))
          (_: state.get)
        ]) null;
        resultDo = handle { handlers = state.handler; state = 4; } compDo;

        compSteps = steps [
          (_: state.get)
          (n: state.put (n * 3))
          (_: state.get)
        ];
        resultSteps = handle { handlers = state.handler; state = 4; } compSteps;
      in
      { doResult = resultDo.value; stepsResult = resultSteps.value; };
    expected = { doResult = 12; stepsResult = 12; };
  };

  typesOnly = {
    expr =
      let
        inherit (fx.sugar.types) Int String;
        Port = Int (x: x >= 0) (x: x <= 65535);
      in
      {
        acceptsPort = Port.check 8080;
        rejectsNeg = Port.check (-1);
        rejectsOverflow = Port.check 70000;
        stringAcceptsString = String.check "hi";
        stringRejectsInt = String.check 5;
        portName = builtins.toString Port;
      };
    expected = {
      acceptsPort = true;
      rejectsNeg = false;
      rejectsOverflow = false;
      stringAcceptsString = true;
      stringRejectsInt = false;
      portName = "Int??";
    };
  };

  namespaceShape = {
    expr =
      let s = fx.sugar;
      in {
        topLevelEffects = builtins.all (k: s ? ${k})
          [ "do" "letM" "pure" "bind" "run" "handle" "map" "seq" "pipe" "kleisli" ];
        opsNested = s ? operators && s.operators ? __div;
        typesNested = s ? types
          && builtins.all (k: s.types ? ${k})
          [ "wrap" "Int" "String" "Bool" "Float" "Path" "Null" "Unit" "Any" ];
        divNotAtTopLevel = !(s ? __div);
      };
    expected = {
      topLevelEffects = true;
      opsNested = true;
      typesNested = true;
      divNotAtTopLevel = true;
    };
  };

  allTests = {
    inherit statePatternDesugared statePatternDo statePatternDiv
      statePatternEquivState
      errorPatternDesugared errorPatternDo
      readerPatternDesugared readerPatternLetM
      doEmpty doSingleton doAutoLift doMixed doComposable doPointFree
      stepsSequences
      divAssociativityTest
      divNotTopLevel divUnderOperators
      reexportsPresent
      withSugarTest
      fullSugarWith operatorOnly combinatorsOnly
      typesOnly
      withOperatorsDoesNotActivateDiv
      namespaceShape;
  };

in
allTests
