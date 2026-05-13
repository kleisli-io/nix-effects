{ lib, fx }:

let
  inherit (fx) pure bind run handle;
  inherit (fx.effects) state error reader;
  inherit (fx.sugar) do steps letM;
  inherit (fx.kernel) kleisli;

  statePatternDesugared = {
    expr =
      let
        comp = bind state.get (n:
          bind (state.put (n + 1)) (_:
            bind state.get (n2:
              pure n2)));
        result = handle { handlers = state.handler; state = 0; } comp;
      in result.value;
    expected = 1;
  };

  # statePatternDo now tests the NEW composable `do` (Kleisli arrow).
  # The old sequencing behavior moved to `steps`.
  statePatternDo = {
    expr =
      let
        # NEW `do` returns a Kleisli arrow (a -> M b), not a Computation.
        # Apply it to `null` to get the Computation, then handle it.
        pipeline = do [
          (x: x)                    # identity Kleisli, auto-lifted to pure
          (_: state.get)            # read state
          (n: state.put (n + 1))    # update state
          (_: state.get)            # read state again
        ];
        comp = pipeline null;
        result = handle { handlers = state.handler; state = 0; } comp;
      in result.value;
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
      in result.value;
    expected = 1;
  };

  statePatternEquivState = {
    expr =
      let
        d = handle { handlers = state.handler; state = 10; }
              (bind state.get (n:
                bind (state.put (n + 1)) (_:
                  bind state.get (n2: pure n2))));
        # NEW `do` is composable Kleisli arrow.
        s = handle { handlers = state.handler; state = 10; }
              ((do [ (_: state.get) (n: state.put (n + 1)) (_: state.get) ]) null);
      in { ds = d.state; ss = s.state; dv = d.value; sv = s.value; };
    expected = { ds = 11; ss = 11; dv = 11; sv = 11; };
  };

  errorPatternDesugared = {
    expr =
      let
        comp = bind (error.raiseWith "parser" "unexpected token") (_:
          bind (error.raiseWith "parser" "missing semicolon") (_:
            pure "ok"));
        result = handle { handlers = error.collecting; state = []; } comp;
      in builtins.length result.state;
    expected = 2;
  };

  errorPatternDo = {
    expr =
      let
        # NEW `do` with error effects. Apply to null to get Computation.
        pipeline = do [
          (_: error.raiseWith "parser" "unexpected token")
          (_: error.raiseWith "parser" "missing semicolon")
          (_: pure "ok")
        ];
        comp = pipeline null;
        result = handle { handlers = error.collecting; state = []; } comp;
      in builtins.length result.state;
    expected = 2;
  };

  readerPatternDesugared = {
    expr =
      let
        comp = bind (reader.asks (e: e.host)) (host:
          bind (reader.asks (e: e.port)) (port:
            pure "${host}:${toString port}"));
        result = handle {
          handlers = reader.handler;
          state = { host = "example.com"; port = 443; };
        } comp;
      in result.value;
    expected = "example.com:443";
  };

  readerPatternLetM = {
    expr =
      let
        comp = letM {
          host = reader.asks (e: e.host);
          port = reader.asks (e: e.port);
        } (b: pure "${b.host}:${toString b.port}");
        result = handle {
          handlers = reader.handler;
          state = { host = "example.com"; port = 443; };
        } comp;
      in result.value;
    expected = "example.com:443";
  };

  doEmpty = {
    expr = (run (do [] 42) {} null).value;
    expected = 42;
  };

  doSingleton = {
    expr = (run (do [ (x: pure (x + 1)) ] 41) {} null).value;
    expected = 42;
  };

  # doAutoLift: plain functions are auto-lifted to Kleisli arrows
  doAutoLift = {
    expr = (run (do [ (x: x + 1) (x: x * 2) ] 20) {} null).value;
    expected = 42;  # (20 + 1) * 2 = 42
  };

  # doMixed: plain and monadic functions compose uniformly
  doMixed = {
    expr = (run (do [ (x: x + 1) (x: pure (x * 2)) ] 20) {} null).value;
    expected = 42;
  };

  # doComposable: kleisli composition of two `do` pipelines equals one merged pipeline
  doComposable = {
    expr =
      let
        p1 = do [ (x: x + 1) ];
        p2 = do [ (x: x * 2) ];
        # Two pipelines composed via kleisli should equal one merged pipeline:
        composed = kleisli p1 p2 20;
        merged = do [ (x: x + 1) (x: x * 2) ] 20;
      in (run composed {} null).value == (run merged {} null).value;
    expected = true;
  };

  # doPointFree: `do` enables point-free style (data-last)
  doPointFree = {
    expr =
      let
        inc = do [ (x: x + 1) ];
        double = do [ (x: x * 2) ];
        # Map over a list without lambda
        results = map inc [ 1 2 3 ];
        result_values = map (r: (run r {} null).value) results;
      in result_values;
    expected = [ 2 3 4 ];
  };

  # stepsSequences: `steps` (old `do`) sequences effects, discards values
  stepsSequences = {
    expr =
      let
        comp = steps [
          (_: state.get)
          (n: state.put (n + 10))
          (_: state.get)
        ];
        result = handle { handlers = state.handler; state = 5; } comp;
      in result.value;
    expected = 15;
  };

  divAssociativityTest = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        sugared  = state.get / (n: pure (n + 1)) / (n: pure (n * 2));
        desugared = bind state.get (n: bind (pure (n + 1)) (n: pure (n * 2)));
        r1 = handle { handlers = state.handler; state = 10; } sugared;
        r2 = handle { handlers = state.handler; state = 10; } desugared;
      in r1.value == r2.value;
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
        (run (do [ (_: pure 1) (x: pure (x + 1)) (x: pure (x * 10)) ] null) {} null).value;
    expected = 20;  # (1 + 1) * 10 = 20
  };

  fullSugarWith = {
    expr =
      let
        inherit (fx.sugar.operators) __div;
        comp = with fx.sugar;
          state.get / (s: state.put (s * 2)) / (_: state.get);
        result = handle { handlers = state.handler; state = 5; } comp;
      in result.value;
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
      in result.value;
    expected = 10;
  };

  # combinatorsOnly now tests the NEW `do` (composable Kleisli)
  # and `steps` (old sequencing behavior)
  combinatorsOnly = {
    expr =
      let
        inherit (fx.sugar) do steps letM;
        # NEW `do`: composable Kleisli pipeline
        comp_do = (do [
          (_: state.get)
          (n: state.put (n * 3))
          (_: state.get)
        ]) null;
        result_do = handle { handlers = state.handler; state = 4; } comp_do;
        
        # OLD `steps`: sequences effects (renamed from `do`)
        comp_steps = steps [
          (_: state.get)
          (n: state.put (n * 3))
          (_: state.get)
        ];
        result_steps = handle { handlers = state.handler; state = 4; } comp_steps;
      in { do_result = result_do.value; steps_result = result_steps.value; };
    expected = { do_result = 12; steps_result = 12; };
  };

  typesOnly = {
    expr =
      let
        inherit (fx.sugar.types) Int String;
        Port = Int (x: x >= 0) (x: x <= 65535);
      in {
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
            doEmpty doSingleton doAutoLift doMixed doComposable doPointFree stepsSequences
            divAssociativityTest
            divNotTopLevel divUnderOperators
            reexportsPresent
            withSugarTest
            fullSugarWith operatorOnly combinatorsOnly
            typesOnly
            withOperatorsDoesNotActivateDiv
            namespaceShape;
  };

  results = builtins.mapAttrs (_: test:
    let actual = test.expr; in
    { inherit actual; expected = test.expected; pass = actual == test.expected; }
  ) allTests;

  failed = lib.filterAttrs (_: r: !r.pass) results;

in allTests // {
  allPass = (builtins.length (builtins.attrNames failed)) == 0;
}
