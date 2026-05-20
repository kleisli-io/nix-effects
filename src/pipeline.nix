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
{ fx, ... }:

let
  inherit (fx.kernel) pure bind;

  reader = fx.effects.reader;
  error  = fx.effects.error;
  acc    = fx.effects.acc;

  mkStage = {
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

  compose = stages: data:
    builtins.foldl'
      (comp: stage: bind comp stage.transform)
      (pure data)
      stages;

  run = args: stages:
    let
      pipeline = compose stages {};

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

  # Convenience re-exports for stage implementations.
  # Stages import these rather than reaching into fx.effects directly.
  ask       = reader.ask;       # Computation returning full env
  asks      = reader.asks;      # (env -> a) -> Computation a
  raise     = error.raise;      # message -> Computation _
  raiseWith = error.raiseWith;  # context -> message -> Computation _
  warn      = acc.emit;         # item -> Computation null

in {
  inherit mkStage compose run;
  inherit pure bind;
  map = fx.kernel.map;
  inherit ask asks raise raiseWith warn;

  __docs = {
    _self = {
      description = "Typed pipeline framework: `mkStage`/`compose`/`run` build composable stages over reader/error/acc/typecheck handlers with collected errors, warnings, and type errors.";
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
        in result  # => { config = "prod"; }
        ```
      '';
    };

    mkStage = {
      description = "mkStage: build a named pipeline stage carrying a `transform`, optional `inputType`/`outputType` schemas, and a `description`; stages chain through `compose`.";
      signature = "mkStage : { name, description ? \"\", transform, inputType ? null, outputType ? null } -> Stage";
      doc = ''
        Create a named pipeline stage.

        `transform : Data -> Computation Data`
          Takes current pipeline data, uses effects (ask, raise, warn),
          returns computation producing updated pipeline data.

        inputType/outputType : optional type schemas for validation
          at stage boundaries (checked when provided).
          Validation uses fx.types.validate which sends typeCheck effects.
      '';
      tests = {
        "creates-stage" = {
          expr = (mkStage {
            name = "test";
            transform = data: pure (data // { touched = true; });
          }).__isStage;
          expected = true;
        };
        "stage-has-name" = {
          expr = (mkStage {
            name = "my-stage";
            transform = data: pure data;
          }).name;
          expected = "my-stage";
        };
        "stage-transform-produces-computation" = {
          expr = fx.comp.isPure ((mkStage {
            name = "add-x";
            transform = data: pure (data // { x = 1; });
          }).transform {});
          expected = true;
        };
      };
    };

    compose = {
      description = "compose: chain a list of stages into a single computation; each stage's transform receives the previous output and returns the next stage's input wrapped in a computation.";
      signature = "compose : [Stage] -> Data -> Computation Data";
      doc = ''
        Chain stages into a single computation.

        Each stage's transform receives the output of the previous stage
        and returns a computation producing the next stage's input.
        Initial data seeds the pipeline.
      '';
      tests = {
        "compose-empty-returns-input" = {
          expr =
            let result = fx.trampoline.handle {
              handlers = {};
              state = null;
            } (compose [] { x = 42; });
            in result.value;
          expected = { x = 42; };
        };
        "compose-two-stages" = {
          expr =
            let
              s1 = mkStage {
                name = "add-x";
                transform = data: pure (data // { x = 1; });
              };
              s2 = mkStage {
                name = "add-y";
                transform = data: pure (data // { y = 2; });
              };
              result = fx.trampoline.handle {
                handlers = {};
                state = null;
              } (compose [ s1 s2 ] {});
            in result.value;
          expected = { x = 1; y = 2; };
        };
        "compose-stages-sequential" = {
          expr =
            let
              s1 = mkStage {
                name = "set-n";
                transform = _: pure { n = 10; };
              };
              s2 = mkStage {
                name = "double-n";
                transform = data: pure { n = data.n * 2; };
              };
              result = fx.trampoline.handle {
                handlers = {};
                state = null;
              } (compose [ s1 s2 ] {});
            in result.value.n;
          expected = 20;
        };
      };
    };

    run = {
      description = "run: execute a pipeline with reader/error/acc/typecheck handlers wired up; returns `{ value, errors, warnings, typeErrors }` from the final state.";
      signature = "run : Args -> [Stage] -> { value : Data, errors : [Err], warnings : [Warn], typeErrors : [Err] }";
      doc = ''
        Execute a pipeline with effect handling.

        `args : { ... }`
          Becomes the reader environment -- stages access via ask/asks.

        stages : [Stage]
          Ordered list of stages to execute.

        Returns:
          value      -- final pipeline data from last stage
          errors     -- list of { message, context } from validation failures
          warnings   -- list of non-fatal warning items
          typeErrors -- list of type validation errors
      '';
      tests = {
        "run-empty-pipeline" = {
          expr =
            let result = run {} [];
            in result.value;
          expected = {};
        };
        "run-single-stage" = {
          expr =
            let
              s = mkStage {
                name = "init";
                transform = _: pure { initialized = true; };
              };
              result = run {} [ s ];
            in result.value;
          expected = { initialized = true; };
        };
        "run-two-stages-compose" = {
          expr =
            let
              s1 = mkStage {
                name = "set-a";
                transform = data: pure (data // { a = 1; });
              };
              s2 = mkStage {
                name = "set-b";
                transform = data: pure (data // { b = data.a + 1; });
              };
              result = run {} [ s1 s2 ];
            in result.value;
          expected = { a = 1; b = 2; };
        };
        "run-collects-errors" = {
          expr =
            let
              s = mkStage {
                name = "fail";
                transform = data:
                  bind (error.raiseWith "stage" "something broke") (_:
                    pure data);
              };
              result = run {} [ s ];
            in builtins.length result.errors;
          expected = 1;
        };
        "run-collects-warnings" = {
          expr =
            let
              s = mkStage {
                name = "warn";
                transform = data:
                  bind (acc.emit "heads up") (_:
                    pure data);
              };
              result = run {} [ s ];
            in result.warnings;
          expected = [ "heads up" ];
        };
        "run-reader-asks" = {
          expr =
            let
              s = mkStage {
                name = "read-env";
                transform = _:
                  bind (reader.asks (env: env.greeting)) (msg:
                    pure { message = msg; });
              };
              result = run { greeting = "hello"; } [ s ];
            in result.value.message;
          expected = "hello";
        };
        "run-multiple-errors-collected" = {
          expr =
            let
              s1 = mkStage {
                name = "err1";
                transform = data:
                  bind (error.raiseWith "s1" "first") (_: pure data);
              };
              s2 = mkStage {
                name = "err2";
                transform = data:
                  bind (error.raiseWith "s2" "second") (_: pure data);
              };
              result = run {} [ s1 s2 ];
            in builtins.length result.errors;
          expected = 2;
        };
        "run-warnings-accumulate-across-stages" = {
          expr =
            let
              s1 = mkStage {
                name = "w1";
                transform = data:
                  bind (acc.emit "warn-1") (_: pure data);
              };
              s2 = mkStage {
                name = "w2";
                transform = data:
                  bind (acc.emit "warn-2") (_: pure data);
              };
              result = run {} [ s1 s2 ];
            in result.warnings;
          expected = [ "warn-1" "warn-2" ];
        };
      };
    };
  };
}
