# Materialize a validated BuildPlan into a derivation.
#
# Takes a plan (from fx.build.plan) and pkgs, produces a pkgs.runCommand
# derivation that copies sources, sets up per-step environments, and
# executes steps sequentially.
#
# Shell generation is pure and tested inline. The derivation itself
# is validated by consumers that actually build it.
{ api, lib, ... }:

let
  inherit (api) mk;

  # -- Shell generation helpers (pure, testable without pkgs) --

  # Generate shell for a single build step
  mkStepScript = step:
    let
      envSetup = lib.concatStringsSep "\n"
        (lib.mapAttrsToList (k: v: "export ${k}=${lib.escapeShellArg v}")
          (step.env or {}));
    in ''
      echo "=== Step: ${step.name} ==="
      ${envSetup}
      ${step.run}
    '';

  # Generate shell to copy sources into $work
  mkSourceSetup = sources:
    lib.concatStringsSep "\n"
      (lib.mapAttrsToList (dest: src:
        let
          destDir = dirOf dest;
          mkdirCmd = if destDir != "." && destDir != ""
                     then "mkdir -p \"$work/${destDir}\""
                     else "";
        in ''
          ${mkdirCmd}
          cp -r ${src} "$work/${dest}"
          chmod -R u+w "$work/${dest}"
        ''
      ) sources);

  # Assemble the complete build script from steps and sources
  mkBuildScript = { steps, sources ? {}, native ? [] }:
    let
      ldPath = lib.makeLibraryPath native;
      allStepScripts = lib.concatMapStringsSep "\n" mkStepScript steps;
      sourceScript = mkSourceSetup sources;
    in ''
      set -euo pipefail
      ${lib.optionalString (native != []) "export LD_LIBRARY_PATH=${ldPath}:\${LD_LIBRARY_PATH:-}"}

      mkdir -p $out
      work=$(mktemp -d)

      ${sourceScript}

      cd $work

      ${allStepScripts}

      if [ -z "$(ls -A $out 2>/dev/null)" ]; then
        touch $out/.empty
      fi
    '';

in mk {
  doc = ''
    Materialize a validated BuildPlan into a derivation.

    Converts the eval-time plan (validated by fx.build.plan) into a
    pkgs.runCommand derivation. Sources are copied into a working
    directory, per-step environment variables are scoped, and steps
    execute sequentially under set -euo pipefail.

    ```
    materialize : { pkgs, plan, native? } -> derivation
    ```

    The plan argument is the `.plan` field from fx.build.plan output.
    Shell generation helpers (mkStepScript, mkSourceSetup, mkBuildScript)
    are pure functions tested inline.
  '';
  value = { pkgs, plan, native ? [] }:
    let
      steps = plan.steps or [];
      sources = plan.sources or {};
    in pkgs.runCommand "${plan.name}-build" {
      nativeBuildInputs = lib.concatMap (s: s.tools or []) steps;
      buildInputs = native;
    } (mkBuildScript {
      inherit steps sources native;
    });

  tests = {
    "step-script-includes-name" = {
      expr = builtins.match ".*Step: compile.*" (mkStepScript { name = "compile"; run = "gcc -o out main.c"; }) != null;
      expected = true;
    };
    "step-script-includes-run" = {
      expr = builtins.match ".*echo hello.*" (mkStepScript { name = "test"; run = "echo hello"; }) != null;
      expected = true;
    };
    "step-script-includes-env" = {
      expr = builtins.match ".*export FOO=bar.*" (mkStepScript { name = "test"; run = "echo"; env = { FOO = "bar"; }; }) != null;
      expected = true;
    };
    "step-script-no-env-when-absent" = {
      expr = builtins.match ".*export.*" (mkStepScript { name = "test"; run = "echo"; }) != null;
      expected = false;
    };
    "source-setup-generates-cp" = {
      expr = builtins.match ".*cp -r .*/nix/store[^ ]* .*" (mkSourceSetup { src = ./.; }) != null;
      expected = true;
    };
    "source-setup-empty" = {
      expr = mkSourceSetup {};
      expected = "";
    };
    "build-script-has-pipefail" = {
      expr = builtins.match ".*set -euo pipefail.*" (mkBuildScript { steps = []; }) != null;
      expected = true;
    };
    "build-script-has-steps" = {
      expr = builtins.match ".*Step: a.*Step: b.*" (mkBuildScript {
        steps = [
          { name = "a"; run = "echo a"; }
          { name = "b"; run = "echo b"; }
        ];
      }) != null;
      expected = true;
    };
  };
}
