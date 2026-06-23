# Handler-swap validation: one computation, three handlers, three behaviors.
#
#   nix eval --raw -f examples/handler-swap-validation.nix collecting
#   nix eval --raw -f examples/handler-swap-validation.nix logging
#   nix eval --raw -f examples/handler-swap-validation.nix strict
{ fx, ... }:

let
  inherit (fx.types) String Int Record ListOf refined;

  Pos = refined "Pos" Int (x: x > 0);
  Network = Record {
    hostName = String;
    port = Pos;
    interfaces = ListOf (Record { name = String; mtu = Pos; });
  };

  badConfig = {
    hostName = "kleisli.io";
    port = (-1);
    interfaces = [
      { name = "eth0"; mtu = (-50); }
      { name = 42; mtu = 1500; }
      { name = "eth2"; mtu = "big"; }
    ];
  };

  comp = Network.validate badConfig;
  runWith = handlers: state: fx.handle { inherit handlers state; } comp;

  renderPath = e:
    if e.path == [ ] then e.context
    else builtins.concatStringsSep "" (map (p: p.segment) e.path);

  collecting =
    let
      r = runWith fx.effects.typecheck.collecting [ ];
      line = e: "  ${renderPath e} :: expected ${e.typeName}, got ${e.actual}";
    in
    "${toString (builtins.length r.state)} error(s):\n"
    + builtins.concatStringsSep "\n" (map line r.state);

  logging =
    let
      r = runWith fx.effects.typecheck.logging [ ];
      line = e: "  ${if e.passed then "pass" else "fail"}  ${renderPath e} : ${e.typeName}";
    in
    builtins.concatStringsSep "\n" (map line r.state);

  # strict throws on the first violation — nix eval surfaces it directly.
  strict = (runWith fx.effects.typecheck.strict null).value;
in
rec {
  inherit strict collecting logging;

  collectingReportsFourErrors =
    builtins.substring 0 11 collecting == "4 error(s):";

  loggingIncludesFailures =
    let text = builtins.replaceStrings [ "\n" ] [ " " ] logging;
    in
    builtins.match ".*fail.*" text != null
    && builtins.match ".*interfaces.*" text != null;

  __example = {
    title = "Handler-Swap Validation";
    description = "Run one validation computation with collecting, logging, and strict handlers.";
    introduction = ''
      The computation is built once from a typed record validator. Only the
      handler changes. That makes the effect boundary visible: collecting
      accumulates every validation error, logging records each check, and
      strict aborts at the first failure.
    '';
    sections = [
      {
        title = "Define a typed boundary";
        prose = ''
          The type describes a network configuration with positive numeric
          fields. `badConfig` intentionally violates multiple checks.
        '';
        code = ''
          Pos = refined "Pos" Int (x: x > 0);
          Network = Record {
            hostName = String;
            port = Pos;
            interfaces = ListOf (Record { name = String; mtu = Pos; });
          };

          badConfig = {
            hostName = "kleisli.io";
            port = (-1);
            interfaces = [
              { name = "eth0"; mtu = (-50); }
              { name = 42; mtu = 1500; }
              { name = "eth2"; mtu = "big"; }
            ];
          };
        '';
        tests = [ ];
      }
      {
        title = "Swap the handler";
        prose = ''
          `Network.validate badConfig` returns an effectful computation. The
          same computation can be interpreted by collecting, logging, or strict
          handlers without rebuilding the validator.
        '';
        code = ''
          comp = Network.validate badConfig;
          runWith = handlers: state: fx.handle { inherit handlers state; } comp;

          collecting =
            let
              r = runWith fx.effects.typecheck.collecting [ ];
              line = e: "  ''${renderPath e} :: expected ''${e.typeName}, got ''${e.actual}";
            in
            "''${toString (builtins.length r.state)} error(s):\n"
            + builtins.concatStringsSep "\n" (map line r.state);

          logging =
            let
              r = runWith fx.effects.typecheck.logging [ ];
              line = e: "  ''${if e.passed then "pass" else "fail"}  ''${renderPath e} : ''${e.typeName}";
            in
            builtins.concatStringsSep "\n" (map line r.state);
        '';
        tests = [
          "collectingReportsFourErrors"
          "loggingIncludesFailures"
        ];
      }
    ];
  };
}
