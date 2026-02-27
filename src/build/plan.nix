# Eval-time build pipeline: validate steps, filter conditions, collect errors.
#
# Uses fx.pipeline.run internally with reader (context), error (collecting),
# and acc (warnings) effects. Produces a validated BuildPlan without throwing.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.pipeline) mkStage run pure bind asks raiseWith warn;
  BuildStep = fx.build.types.BuildStep;

  plan = mk {
    doc = ''
      Validate and process build steps into a BuildPlan.

      Runs an eval-time pipeline that validates each step against
      BuildStep, filters steps by `when` predicates using reader context,
      and collects all errors without throwing.

      ```
      plan : { name, steps, sources?, context? } -> { plan, errors, warnings, typeErrors }
      ```
    '';
    value = { name, steps, sources ? {}, context ? {} }:
      let
        validate = mkStage {
          name = "validate-steps";
          transform = _:
            let
              n = builtins.length steps;
              check = i:
                let step = builtins.elemAt steps i;
                in { inherit step i; valid = BuildStep.check step; };
              checked = builtins.genList check n;
              valid = map (x: x.step) (builtins.filter (x: x.valid) checked);
              invalid = builtins.filter (x: !x.valid) checked;
              raiseAll = builtins.foldl'
                (comp: x: bind comp (_:
                  raiseWith "validate-steps"
                    "step ${toString x.i}: invalid (requires name: non-empty string, run: string)"))
                (pure null)
                invalid;
            in bind raiseAll (_: pure { steps = valid; });
        };

        filterConditions = mkStage {
          name = "evaluate-conditions";
          transform = data:
            bind (asks (env: env)) (ctx:
              let
                keeps = s: !(s ? when) || s.when ctx;
                kept = builtins.filter keeps data.steps;
                skipped = builtins.filter (s: !keeps s) data.steps;
                warnAll = builtins.foldl'
                  (comp: s: bind comp (_:
                    warn "step '${s.name}' skipped: condition not met"))
                  (pure null)
                  skipped;
              in bind warnAll (_: pure { steps = kept; }));
        };

        result = run context [ validate filterConditions ];
      in {
        plan = { inherit name sources; steps = result.value.steps or []; };
        inherit (result) errors warnings typeErrors;
      };

    tests = {
      "all-valid-steps" = {
        expr =
          let r = plan.value {
            name = "test";
            steps = [
              { name = "a"; run = "echo a"; }
              { name = "b"; run = "echo b"; }
            ];
          };
          in { stepCount = builtins.length r.plan.steps; errors = r.errors; };
        expected = { stepCount = 2; errors = []; };
      };
      "collects-error-for-invalid-step" = {
        expr =
          let r = plan.value {
            name = "test";
            steps = [
              { name = "good"; run = "echo ok"; }
              { bad = true; }
            ];
          };
          in { validCount = builtins.length r.plan.steps; errorCount = builtins.length r.errors; };
        expected = { validCount = 1; errorCount = 1; };
      };
      "filters-conditional-step" = {
        expr =
          let r = plan.value {
            name = "test";
            context = { mode = "dev"; };
            steps = [
              { name = "always"; run = "echo always"; }
              { name = "prod-only"; run = "echo prod"; when = ctx: ctx.mode == "production"; }
            ];
          };
          in {
            stepCount = builtins.length r.plan.steps;
            warningCount = builtins.length r.warnings;
            stepName = (builtins.elemAt r.plan.steps 0).name;
          };
        expected = { stepCount = 1; warningCount = 1; stepName = "always"; };
      };
      "keeps-step-when-condition-met" = {
        expr =
          let r = plan.value {
            name = "test";
            context = { mode = "production"; };
            steps = [
              { name = "always"; run = "echo always"; }
              { name = "prod-only"; run = "echo prod"; when = ctx: ctx.mode == "production"; }
            ];
          };
          in builtins.length r.plan.steps;
        expected = 2;
      };
      "preserves-name-and-sources" = {
        expr =
          let r = plan.value {
            name = "my-css";
            sources = { src = /tmp; };
            steps = [{ name = "s"; run = "e"; }];
          };
          in { name = r.plan.name; hasSources = r.plan ? sources; };
        expected = { name = "my-css"; hasSources = true; };
      };
      "empty-steps" = {
        expr =
          let r = plan.value { name = "empty"; steps = []; };
          in { stepCount = builtins.length r.plan.steps; errors = r.errors; };
        expected = { stepCount = 0; errors = []; };
      };
    };
  };

in plan
