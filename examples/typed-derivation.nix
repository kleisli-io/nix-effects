# Typed Derivations: eval-time type checking of Nix build configs
#
# The cipher suite type DEPENDS on the fipsMode flag:
#   fipsMode = true  → cipherSuites : ListOf FIPSCipher  (approved ciphers only)
#   fipsMode = false → cipherSuites : ListOf String       (anything goes)
#
# This is Σ(fipsMode:Bool).B(fipsMode) — a dependent contract in pure Nix.
# Invalid configs throw at eval time. The collecting handler reports
# exactly which cipher at which index failed.
#
#   nix build .#cryptoService    — builds: valid FIPS config
#   nix build .#buggyService     — fails at eval time: 3DES slipped in
{ fx, pkgs ? null, ... }:

let
  inherit (fx.types) refined Bool String ListOf DepRecord;

  FIPSCipher = refined "FIPSCipher" String
    (x: builtins.elem x [ "AES-256-GCM" "AES-192-GCM" "AES-128-GCM" "AES-256-CBC" "AES-128-CBC" ]);

  ServiceConfig = DepRecord [
    { name = "fipsMode"; type = Bool; }
    { name = "cipherSuites"; type = self:
        if self.fipsMode then ListOf FIPSCipher else ListOf String; }
  ];

  # Collect all type errors with blame context, value, and expected type
  collectErrors = config:
    let
      packed = ServiceConfig.pack config;
      showValue = v:
        let s = builtins.toJSON v;
        in if builtins.stringLength s > 40
           then builtins.substring 0 37 s + "..."
           else s;
      result = fx.run (ServiceConfig.validate packed) {
        typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [
            "${param.context}: ${showValue param.value} is not a valid ${param.type.name}"
          ]; };
      } [];
    in result.state;

  # Gate: throw with per-element blame if config is invalid
  validateOrThrow = config:
    let errors = collectErrors config;
    in if errors == [] then config
       else builtins.throw ("Type errors in ServiceConfig:\n"
         + builtins.concatStringsSep "\n" (map (e: "  - ${e}") errors));

  valid   = { fipsMode = true;  cipherSuites = [ "AES-256-GCM" "AES-128-GCM" ]; };
  invalid = { fipsMode = true;  cipherSuites = [ "AES-256-GCM" "RC4" "DES" ]; };

  # Tests
  gateRejectsInvalid = !(builtins.tryEval (validateOrThrow invalid)).success;
  gatePassesValid    = (builtins.tryEval (validateOrThrow valid)).success;

  # The point: per-element blame through DepRecord → Sigma → ListOf.
  # Not "list failed" or "snd failed" — RC4 at index 1, DES at index 2.
  deepBlame =
    let errors = collectErrors invalid;
    in builtins.length errors == 2
       && builtins.elemAt errors 0 == "List[FIPSCipher][1]: \"RC4\" is not a valid FIPSCipher"
       && builtins.elemAt errors 1 == "List[FIPSCipher][2]: \"DES\" is not a valid FIPSCipher";

in {
  inherit gateRejectsInvalid gatePassesValid deepBlame;
  allPass = gateRejectsInvalid && gatePassesValid && deepBlame;
} // (if pkgs == null then {} else {
  cryptoService =
    let checked = validateOrThrow valid;
    in pkgs.stdenv.mkDerivation {
      name = "crypto-service";
      dontUnpack = true;
      installPhase = ''
        mkdir -p $out
        echo '${builtins.toJSON checked}' > $out/config.json
      '';
    };

  # A senior engineer copy-pasted from the prod cipher list and added
  # TLS 1.3 suites. Looks fine. But 3DES slipped through from the
  # legacy compatibility section — it's been deprecated since 2019.
  # Without the type system this ships to production.
  buggyService =
    let checked = validateOrThrow {
      fipsMode = true;
      cipherSuites = [
        "AES-256-GCM"
        "AES-128-GCM"
        "AES-192-GCM"
        "3DES"                  # <-- the bug
        "AES-256-CBC"
      ];
    };
    in pkgs.stdenv.mkDerivation {
      name = "crypto-service";
      dontUnpack = true;
      installPhase = ''
        mkdir -p $out
        echo '${builtins.toJSON checked}' > $out/config.json
      '';
    };
})
