# Getting Started

## Installation

Add nix-effects as a flake input:

```nix
{
  inputs.nix-effects.url = "github:kleisli-io/nix-effects";

  outputs = { nix-effects, nixpkgs, ... }:
    let
      fx = nix-effects.lib;
    in {
      # fx.types, fx.run, fx.send, fx.bind, fx.effects, fx.stream ...
    };
}
```

Or import directly without flakes:

```nix
let fx = import ./path/to/nix-effects { lib = nixpkgs.lib; };
in ...
```

## Your first type

Define a type with `fx.types.refined`:

```nix
let
  inherit (fx.types) Int refined;

  Port = refined "Port" Int (x: x >= 1 && x <= 65535);
in {
  # Pure guard — fast boolean check
  ok  = Port.check 8080;   # true
  bad = Port.check 99999;  # false

  # Effectful validate — runs through the trampoline, produces blame context
  result = fx.run (Port.validate 99999)
    fx.effects.typecheck.collecting [];
  # result.state = [ { context = "Port"; message = "Expected Port, got int"; ... } ]
}
```

## Your first dependent contract

One field's type depends on another field's value:

```nix
let
  inherit (fx.types) Bool Int String ListOf DepRecord refined;

  FIPSCipher = refined "FIPSCipher" String
    (x: builtins.elem x [ "AES-256-GCM" "AES-192-GCM" "AES-128-GCM" "AES-256-CBC" "AES-128-CBC" ]);

  ServiceConfig = DepRecord [
    { name = "fipsMode"; type = Bool; }
    { name = "cipherSuites"; type = self:
        if self.fipsMode then ListOf FIPSCipher else ListOf String; }
  ];
in {
  ok  = ServiceConfig.checkFlat { fipsMode = true;  cipherSuites = [ "AES-256-GCM" ]; };  # true
  bad = ServiceConfig.checkFlat { fipsMode = true;  cipherSuites = [ "3DES" ]; };         # false
}
```

## Your first effect

Write a computation, then choose the handler:

```nix
let
  inherit (fx) pure bind run;
  inherit (fx.effects) get put;

  # Double the state
  doubleState = bind get (s: bind (put (s * 2)) (_: pure s));

  result = run doubleState fx.effects.state.handler 21;
  # result.value = 21  (old state returned)
  # result.state = 42  (state doubled)
in result
```

## Running the showcase

The repo includes a working end-to-end demo:

```bash
git clone https://github.com/kleisli-io/nix-effects
cd nix-effects

# Valid config — build succeeds
nix build .#cryptoService

# Invalid config (3DES in FIPS mode) — caught at eval time
nix build .#buggyService
# error: Type errors in ServiceConfig:
#   - List[FIPSCipher][3]: "3DES" is not a valid FIPSCipher

# Run all tests
nix flake check
```

## What's in the box

The `fx` attrset is the entire public API:

| Namespace | Contents |
|-----------|---------|
| `fx.pure`, `fx.bind`, `fx.send`, `fx.map`, `fx.seq` | Freer monad kernel |
| `fx.run`, `fx.handle` | Trampoline interpreter |
| `fx.adapt`, `fx.adaptHandlers` | Handler composition |
| `fx.types.*` | Type system (primitives, constructors, dependent, refinement, universe) |
| `fx.effects.*` | Built-in effects (state, error, reader, writer, acc, choice, conditions, typecheck, linear) |
| `fx.stream.*` | Effectful lazy sequences |
