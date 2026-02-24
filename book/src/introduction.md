# nix-effects

A type-checking kernel, algebraic effects, and dependent types in pure Nix.

nix-effects catches configuration errors at `nix eval` time — before
anything builds or ships. Every type is backed by an MLTT proof checker
that verifies values, computes universe levels, and extracts certified Nix
functions from proof terms. You get precise blame when something violates
a type.

```
$ nix build .#buggyService
error: Type errors in ServiceConfig:
  - List[FIPSCipher][3]: "3DES" is not a valid FIPSCipher

```

That error is specific: element 3 of the cipher list is `"3DES"`, which
isn't a valid `FIPSCipher`. Index, type name, rejected value — no chasing
through a stack trace. No evaluator patches, no external tools. Pure Nix.

## The demo

A crypto service requires FIPS-compliant ciphers when `fipsMode = true`.
The cipher list type *depends on* the mode flag — this is a dependent
type (`Σ(fipsMode:Bool).B(fipsMode)`) checked by the MLTT kernel at
eval time:

```nix
let
  FIPSCipher = refined "FIPSCipher" String
    (x: builtins.elem x [ "AES-256-GCM" "AES-192-GCM" "AES-128-GCM" "AES-256-CBC" "AES-128-CBC" ]);

  ServiceConfig = DepRecord [
    { name = "fipsMode"; type = Bool; }
    { name = "cipherSuites"; type = self:
        if self.fipsMode then ListOf FIPSCipher else ListOf String; }
  ];
in ...

```

`nix build .#cryptoService` succeeds. `nix build .#buggyService`
fails at eval time because 3DES slipped in. See
[examples/typed-derivation.nix](https://github.com/kleisli-io/nix-effects/blob/main/examples/typed-derivation.nix)
for the complete example with handler, error formatting, and both derivations.
