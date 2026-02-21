# nix-effects documentation example tests
#
# Evaluates the code blocks from book/src/getting-started.md to catch
# broken examples before users hit them.
{ lib, fx }:

let
  # -- Test 1: "Your first type" (Port example) --
  portExample =
    let
      inherit (fx.types) Int refined;
      Port = refined "Port" Int (x: x >= 1 && x <= 65535);
      ok = Port.check 8080;
      bad = Port.check 99999;
      result = fx.run (Port.validate 99999)
        fx.effects.typecheck.collecting [];
    in
      ok == true
      && bad == false
      && builtins.isList result.state
      && builtins.length result.state > 0;

  # -- Test 2: "Your first dependent contract" (DepRecord + FIPSCipher) --
  depContractExample =
    let
      inherit (fx.types) Bool Int String ListOf DepRecord refined;
      FIPSCipher = refined "FIPSCipher" String
        (x: builtins.elem x [ "AES-256-GCM" "AES-192-GCM" "AES-128-GCM" "AES-256-CBC" "AES-128-CBC" ]);
      ServiceConfig = DepRecord [
        { name = "fipsMode"; type = Bool; }
        { name = "cipherSuites"; type = self:
            if self.fipsMode then ListOf FIPSCipher else ListOf String; }
      ];
      ok  = ServiceConfig.checkFlat { fipsMode = true;  cipherSuites = [ "AES-256-GCM" ]; };
      bad = ServiceConfig.checkFlat { fipsMode = true;  cipherSuites = [ "3DES" ]; };
    in
      ok == true && bad == false;

  # -- Test 3: "Your first effect" (state doubling) --
  stateEffectExample =
    let
      inherit (fx) pure bind run;
      inherit (fx.effects) get put;
      doubleState = bind get (s: bind (put (s * 2)) (_: pure s));
      result = run doubleState fx.effects.state.handler 21;
    in
      result.value == 21 && result.state == 42;

  # -- Test 4: API surface sanity ("What's in the box") --
  apiSurfaceSanity =
    fx ? pure && fx ? bind && fx ? send && fx ? map && fx ? seq
    && fx ? run && fx ? handle
    && fx ? adapt && fx ? adaptHandlers
    && fx ? types && fx ? effects && fx ? stream;

in {
  inherit portExample depContractExample stateEffectExample apiSurfaceSanity;

  allPass = portExample && depContractExample && stateEffectExample && apiSurfaceSanity;
}
