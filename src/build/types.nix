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
  inherit (api) mk;
  inherit (fx.types.foundation) check;
  inherit (fx.types.constructors) Record ListOf;
  inherit (fx.types.primitives) String;
  inherit (fx.types.refinement) refined nonEmpty;

  NonEmptyString = refined "NonEmptyString" String nonEmpty;

  BuildStep = mk {
    doc = ''
      Build step: a single step in a build pipeline.

      Required: name (non-empty), run (shell fragment).
      Optional (open record): description, tools, env, inputType, outputType, when.
    '';
    value = Record {
      name = NonEmptyString;
      run = String;
    };
    tests = {
      "accepts-minimal-step" = {
        expr = check BuildStep.value { name = "test"; run = "echo hello"; };
        expected = true;
      };
      "accepts-full-step" = {
        expr = check BuildStep.value {
          name = "compile";
          description = "Compile CSS";
          tools = [];
          env = { FOO = "bar"; };
          run = "echo compile";
          when = _ctx: true;
        };
        expected = true;
      };
      "allows-extra-fields" = {
        expr = check BuildStep.value { name = "test"; run = "echo"; custom = 42; };
        expected = true;
      };
      "rejects-missing-name" = {
        expr = check BuildStep.value { run = "echo hello"; };
        expected = false;
      };
      "rejects-missing-run" = {
        expr = check BuildStep.value { name = "test"; };
        expected = false;
      };
      "rejects-non-string-name" = {
        expr = check BuildStep.value { name = 42; run = "echo hello"; };
        expected = false;
      };
      "rejects-empty-name" = {
        expr = check BuildStep.value { name = ""; run = "echo hello"; };
        expected = false;
      };
      "rejects-non-attrs" = {
        expr = check BuildStep.value "not-an-attrset";
        expected = false;
      };
    };
  };

  BuildPlan = mk {
    doc = ''
      Build plan: a complete build pipeline.

      Required: name (non-empty), steps (list of BuildStep).
      Optional (open record): sources, context.
    '';
    value = Record {
      name = NonEmptyString;
      steps = ListOf BuildStep.value;
    };
    tests = {
      "accepts-minimal-plan" = {
        expr = check BuildPlan.value {
          name = "my-build";
          steps = [{ name = "step1"; run = "echo hello"; }];
        };
        expected = true;
      };
      "accepts-full-plan" = {
        expr = check BuildPlan.value {
          name = "css-pipeline";
          steps = [
            { name = "filter"; run = "grep -v docstring"; }
            { name = "compile"; run = "tailwindcss -o $out/styles.css"; tools = []; }
          ];
          sources = { src = /tmp; };
          context = { mode = "production"; };
        };
        expected = true;
      };
      "accepts-empty-steps" = {
        expr = check BuildPlan.value { name = "empty"; steps = []; };
        expected = true;
      };
      "rejects-missing-name" = {
        expr = check BuildPlan.value { steps = [{ name = "s"; run = "echo"; }]; };
        expected = false;
      };
      "rejects-missing-steps" = {
        expr = check BuildPlan.value { name = "build"; };
        expected = false;
      };
      "rejects-invalid-step-in-plan" = {
        expr = check BuildPlan.value {
          name = "build";
          steps = [{ name = "s"; }];
        };
        expected = false;
      };
      "rejects-non-list-steps" = {
        expr = check BuildPlan.value { name = "build"; steps = "not-a-list"; };
        expected = false;
      };
      "rejects-non-attrs" = {
        expr = check BuildPlan.value 42;
        expected = false;
      };
    };
  };

in mk {
  doc = ''
    Build types for effects-powered builders.

    BuildStep and BuildPlan describe build pipelines at the type level,
    enabling validation before materialization into derivations.
  '';
  value = {
    inherit BuildStep BuildPlan;
  };
}
