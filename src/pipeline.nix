# nix-effects pipeline: Typed pipeline framework with composable stages
#
# Stages are composable transformations on pipeline data, executed with:
#   reader  -- immutable environment context (stages access via ask/asks)
#   error   -- collecting validation errors (all stages checked, not just first)
#   acc     -- non-fatal warnings / accumulator
#
# Each stage's transform: Data -> Computation Data
# where Data flows as the value through bind, and effects
# are handled by run.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.kernel) pure bind;

  reader = fx.effects.reader;
  error  = fx.effects.error;
  acc    = fx.effects.acc;

  mkStage = mk {
    doc = ''
      Create a named pipeline stage.

      ```
      mkStage : { name, description?, transform, inputType?, outputType? } -> Stage
      ```

      transform : Data -> Computation Data
        Takes current pipeline data, uses effects (ask, raise, warn),
        returns computation producing updated pipeline data.

      inputType/outputType : optional type schemas for validation
        at stage boundaries (checked when provided).
        Validation uses fx.types.validate which sends typeCheck effects.
    '';
    value = {
      name,
      description ? "",
      transform,
      inputType ? null,
      outputType ? null,
    }: let
      validate = schema: data: fx.kernel.map (_: data) (schema.validate data);
    in {
      inherit name description;
      transform = data:
        let
          data1 = if inputType != null then validate inputType data else pure data;
          transformed = bind data1 transform;
          validated = if outputType != null then bind transformed (validate outputType) else transformed;
        in validated;
      inputType = inputType;
      outputType = outputType;
      __isStage = true;
    };
    tests = {
      "creates-stage" = {
        expr = (mkStage.value {
          name = "test";
          transform = data: pure (data // { touched = true; });
        }).__isStage;
        expected = true;
      };
      "stage-has-name" = {
        expr = (mkStage.value {
          name = "my-stage";
          transform = data: pure data;
        }).name;
        expected = "my-stage";
      };
      "stage-transform-produces-computation" = {
        expr = ((mkStage.value {
          name = "add-x";
          transform = data: pure (data // { x = 1; });
        }).transform {})._tag;
        expected = "Pure";
      };
    };
  };

  compose = mk {
    doc = ''
      Chain stages into a single computation.

      ```
      compose : [Stage] -> Data -> Computation Data
      ```

      Each stage's transform receives the output of the previous stage
      and returns a computation producing the next stage's input.
      Initial data seeds the pipeline.
    '';
    value = stages: data:
      builtins.foldl'
        (comp: stage: bind comp stage.transform)
        (pure data)
        stages;
    tests = {
      "compose-empty-returns-input" = {
        expr =
          let result = fx.trampoline.handle {
            handlers = {};
            state = null;
          } (compose.value [] { x = 42; });
          in result.value;
        expected = { x = 42; };
      };
      "compose-two-stages" = {
        expr =
          let
            s1 = mkStage.value {
              name = "add-x";
              transform = data: pure (data // { x = 1; });
            };
            s2 = mkStage.value {
              name = "add-y";
              transform = data: pure (data // { y = 2; });
            };
            result = fx.trampoline.handle {
              handlers = {};
              state = null;
            } (compose.value [ s1 s2 ] {});
          in result.value;
        expected = { x = 1; y = 2; };
      };
      "compose-stages-sequential" = {
        expr =
          let
            s1 = mkStage.value {
              name = "set-n";
              transform = _: pure { n = 10; };
            };
            s2 = mkStage.value {
              name = "double-n";
              transform = data: pure { n = data.n * 2; };
            };
            result = fx.trampoline.handle {
              handlers = {};
              state = null;
            } (compose.value [ s1 s2 ] {});
          in result.value.n;
        expected = 20;
      };
    };
  };

  run = mk {
    doc = ''
      Execute a pipeline with effect handling.

      ```
      run : args -> [Stage] -> { value, errors, warnings, typeErrors }
      ```

      args : { ... }
        Becomes the reader environment -- stages access via ask/asks.

      stages : [Stage]
        Ordered list of stages to execute.

      Returns:
        value      -- final pipeline data from last stage
        errors     -- list of { message, context } from validation failures
        warnings   -- list of non-fatal warning items
        typeErrors -- list of type validation errors
    '';
    value = args: stages:
      let
        pipeline = compose.value stages {};

        # Reader env is wrapped in a function closure so that the trampoline's
        # builtins.deepSeq on handler state doesn't force the entire depot tree.
        # deepSeq on a function is a no-op (functions are already values in Nix).
        adaptedReader = fx.adapt.adaptHandlers {
          get = s: s.envFn null;
          set = s: env: s // { envFn = _: env; };
        } reader.handler;

        adaptedError = fx.adapt.adaptHandlers {
          get = s: s.errors;
          set = s: errors: s // { inherit errors; };
        } error.collecting;

        adaptedAcc = fx.adapt.adaptHandlers {
          get = s: s.warnings;
          set = s: warnings: s // { inherit warnings; };
        } acc.handler;

        adaptedTypecheck = fx.adapt.adaptHandlers {
          get = s: s.typeErrors;
          set = s: typeErrors: s // { inherit typeErrors; };
        } fx.effects.typecheck.collecting;

        result = fx.trampoline.handle {
          handlers = adaptedReader // adaptedError // adaptedAcc // adaptedTypecheck;
          state = { envFn = _: args; errors = []; warnings = []; typeErrors = []; };
        } pipeline;
      in {
        inherit (result) value;
        errors = result.state.errors;
        warnings = result.state.warnings;
        typeErrors = result.state.typeErrors;
      };
    tests = {
      "run-empty-pipeline" = {
        expr =
          let result = run.value {} [];
          in result.value;
        expected = {};
      };
      "run-single-stage" = {
        expr =
          let
            s = mkStage.value {
              name = "init";
              transform = _: pure { initialized = true; };
            };
            result = run.value {} [ s ];
          in result.value;
        expected = { initialized = true; };
      };
      "run-two-stages-compose" = {
        expr =
          let
            s1 = mkStage.value {
              name = "set-a";
              transform = data: pure (data // { a = 1; });
            };
            s2 = mkStage.value {
              name = "set-b";
              transform = data: pure (data // { b = data.a + 1; });
            };
            result = run.value {} [ s1 s2 ];
          in result.value;
        expected = { a = 1; b = 2; };
      };
      "run-collects-errors" = {
        expr =
          let
            s = mkStage.value {
              name = "fail";
              transform = data:
                bind (error.raiseWith "stage" "something broke") (_:
                  pure data);
            };
            result = run.value {} [ s ];
          in builtins.length result.errors;
        expected = 1;
      };
      "run-collects-warnings" = {
        expr =
          let
            s = mkStage.value {
              name = "warn";
              transform = data:
                bind (acc.emit "heads up") (_:
                  pure data);
            };
            result = run.value {} [ s ];
          in result.warnings;
        expected = [ "heads up" ];
      };
      "run-reader-asks" = {
        expr =
          let
            s = mkStage.value {
              name = "read-env";
              transform = _:
                bind (reader.asks (env: env.greeting)) (msg:
                  pure { message = msg; });
            };
            result = run.value { greeting = "hello"; } [ s ];
          in result.value.message;
        expected = "hello";
      };
      "run-multiple-errors-collected" = {
        expr =
          let
            s1 = mkStage.value {
              name = "err1";
              transform = data:
                bind (error.raiseWith "s1" "first") (_: pure data);
            };
            s2 = mkStage.value {
              name = "err2";
              transform = data:
                bind (error.raiseWith "s2" "second") (_: pure data);
            };
            result = run.value {} [ s1 s2 ];
          in builtins.length result.errors;
        expected = 2;
      };
      "run-warnings-accumulate-across-stages" = {
        expr =
          let
            s1 = mkStage.value {
              name = "w1";
              transform = data:
                bind (acc.emit "warn-1") (_: pure data);
            };
            s2 = mkStage.value {
              name = "w2";
              transform = data:
                bind (acc.emit "warn-2") (_: pure data);
            };
            result = run.value {} [ s1 s2 ];
          in result.warnings;
        expected = [ "warn-1" "warn-2" ];
      };
    };
  };

  # Convenience re-exports for stage implementations.
  # Stages import these rather than reaching into fx.effects directly.
  ask       = reader.ask;       # Computation returning full env
  asks      = reader.asks;      # (env -> a) -> Computation a
  raise     = error.raise;      # message -> Computation _
  raiseWith = error.raiseWith;  # context -> message -> Computation _
  warn      = acc.emit;         # item -> Computation null

in mk {
  doc = ''
    Typed pipeline framework with composable stages.

    Stages are composable transformations executed with reader (immutable
    environment), error (collecting validation errors), and acc (non-fatal
    warnings) effects. The run function wires up all handlers and returns
    { value, errors, warnings, typeErrors }.

    ```nix
    let
      stage1 = pipeline.mkStage {
        name = "discover";
        transform = data:
          bind (pipeline.asks (env: env.config)) (cfg:
            pure (data // { config = cfg; }));
      };
      result = pipeline.run { config = "prod"; } [ stage1 ];
    in result.value  # => { config = "prod"; }
    ```
  '';
  value = {
    inherit mkStage compose run;
    inherit pure bind;
    map = fx.kernel.map;
    inherit ask asks raise raiseWith warn;
  };
}
