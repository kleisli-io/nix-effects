# nix-effects build types: BuildStep and BuildPlan
#
# Core data types for effects-powered builders. BuildStep describes a
# single shell step. BuildPlan describes a complete pipeline with named
# steps, source inputs, and reader context.
#
# Both use Record with open semantics — required fields are validated,
# optional fields (tools, env, when, etc.) are permitted and validated
# when consumed by the eval-time pipeline.
{ fx, api, ... }:
let
  inherit (fx.types.foundation) check;
  inherit (fx.types.constructors) RecordOpen ListOf;
  inherit (fx.types.primitives) String;
  inherit (fx.types.refinement) refined nonEmpty;

  NonEmptyString = refined "NonEmptyString" String nonEmpty;

  BuildStep = RecordOpen {
    name = NonEmptyString;
    run = String;
  };

  BuildPlan = RecordOpen {
    name = NonEmptyString;
    steps = ListOf BuildStep;
  };

in
{
  scope = {
    types = api.namespace {
      description = "Build types: `BuildStep`/`BuildPlan` open-record schemas that validate build pipelines at eval time before materialisation into derivations.";
      doc = ''
        Build types for effects-powered builders.

        `BuildStep` and `BuildPlan` describe build pipelines at the type level,
        enabling validation before materialization into derivations.
      '';
      value = {
        BuildStep = api.leaf {
          value = BuildStep;
          description = "BuildStep: open-record type for a single shell step in a build pipeline; requires non-empty `name` and `run`, permits `tools`/`env`/`when`/etc.";
          doc = ''
            Build step: a single step in a build pipeline.

            Required: `name` (non-empty), `run` (shell fragment).
            Optional (open record): `description`, `tools`, `env`, `inputType`,
            `outputType`, `when`.
          '';
          tests = {
            "accepts-minimal-step" = {
              expr = check BuildStep { name = "test"; run = "echo hello"; };
              expected = true;
            };
            "accepts-full-step" = {
              expr = check BuildStep {
                name = "compile";
                description = "Compile CSS";
                tools = [ ];
                env = { FOO = "bar"; };
                run = "echo compile";
                when = _ctx: true;
              };
              expected = true;
            };
            "allows-extra-fields" = {
              expr = check BuildStep { name = "test"; run = "echo"; custom = 42; };
              expected = true;
            };
            "rejects-missing-name" = {
              expr = check BuildStep { run = "echo hello"; };
              expected = false;
            };
            "rejects-missing-run" = {
              expr = check BuildStep { name = "test"; };
              expected = false;
            };
            "rejects-non-string-name" = {
              expr = check BuildStep { name = 42; run = "echo hello"; };
              expected = false;
            };
            "rejects-empty-name" = {
              expr = check BuildStep { name = ""; run = "echo hello"; };
              expected = false;
            };
            "rejects-non-attrs" = {
              expr = check BuildStep "not-an-attrset";
              expected = false;
            };
          };
        };

        BuildPlan = api.leaf {
          value = BuildPlan;
          description = "BuildPlan: open-record type for a complete build pipeline; requires non-empty `name` and a `[BuildStep]` list, permits `sources` and `context`.";
          doc = ''
            Build plan: a complete build pipeline.

            Required: `name` (non-empty), `steps` (list of `BuildStep`).
            Optional (open record): `sources`, `context`.
          '';
          tests = {
            "accepts-minimal-plan" = {
              expr = check BuildPlan {
                name = "my-build";
                steps = [{ name = "step1"; run = "echo hello"; }];
              };
              expected = true;
            };
            "accepts-full-plan" = {
              expr = check BuildPlan {
                name = "css-pipeline";
                steps = [
                  { name = "filter"; run = "grep -v docstring"; }
                  { name = "compile"; run = "tailwindcss -o $out/styles.css"; tools = [ ]; }
                ];
                sources = { src = /tmp; };
                context = { mode = "production"; };
              };
              expected = true;
            };
            "accepts-empty-steps" = {
              expr = check BuildPlan { name = "empty"; steps = [ ]; };
              expected = true;
            };
            "rejects-missing-name" = {
              expr = check BuildPlan { steps = [{ name = "s"; run = "echo"; }]; };
              expected = false;
            };
            "rejects-missing-steps" = {
              expr = check BuildPlan { name = "build"; };
              expected = false;
            };
            "rejects-invalid-step-in-plan" = {
              expr = check BuildPlan {
                name = "build";
                steps = [{ name = "s"; }];
              };
              expected = false;
            };
            "rejects-non-list-steps" = {
              expr = check BuildPlan { name = "build"; steps = "not-a-list"; };
              expected = false;
            };
            "rejects-non-attrs" = {
              expr = check BuildPlan 42;
              expected = false;
            };
          };
        };

      };
    };
  };
}
