{ self, api, ... }:

api.mk {
  description = "fx.build: eval-time build pipeline — `plan` validates BuildStep records via fx.pipeline, `materialize` lowers a plan to a runCommand derivation.";
  doc = ''
    `plan` validates a sequence of `BuildStep` records via
    `fx.pipeline.run` (reader/error/acc effects). `materialize` lowers
    a validated plan to a `pkgs.runCommand` derivation; shell
    generation is pure and tested inline.
  '';
  value = {
    inherit (self) materialize plan types;
  };
}
