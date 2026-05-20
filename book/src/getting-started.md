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
  inherit (fx.types) String refined;

  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);
in {
  # Kernel decision procedure — fast boolean check
  ok  = TargetClass.check "module";   # true
  bad = TargetClass.check "fleet";    # false

  # Effectful validate — runs through the trampoline, produces blame context
  result = fx.run (TargetClass.validate "fleet")
    fx.effects.typecheck.collecting [];
  # result.state = [ { context = "TargetClass"; ... } ]
}

```

## Your first dependent type

One field's type depends on another field's value — this is a genuine
dependent type, checked by the MLTT proof-checking kernel:

```nix
let
  inherit (fx.types) Bool String ListOf DepRecord refined;

  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);

  AspectDecl = DepRecord [
    { name = "generated"; type = Bool; }
    { name = "target"; type = self:
        if self.generated then TargetClass else String; }
    { name = "requires"; type = _: ListOf String; }
  ];
in {
  ok = AspectDecl.checkFlat {
    generated = true;
    target = "module";
    requires = [ "toolchain" ];
  };  # true

  bad = AspectDecl.checkFlat {
    generated = true;
    target = "fleet";
    requires = [ ];
  };  # false
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

## A first generated datatype

Generated datatypes are the next step after validation. They give a DSL
its constructors, its type, and reusable structural metadata:

```nix
let
  H = fx.types.hoas;

  Aspect = H.datatype "Aspect" [
    (H.con "aspect" [
      (H.field "name" H.string)
      (H.field "target" H.string)
      (H.field "requires" (H.listOf H.string))
    ])
  ];
in Aspect
```

The generated `Aspect` shape can be checked, viewed, reviewed,
documented, traversed for dependencies, interpreted by handlers, and
ornamented with derived fields.

## Running checks

The repo includes runnable tests and examples:

```bash
git clone https://github.com/kleisli-io/nix-effects
cd nix-effects

# Run all tests
nix flake check

```

## The kernel behind every type

Every `.check` call runs the MLTT type-checking kernel. When you write
`TargetClass.check "module"`, the kernel elaborates `"module"` into a
term, type-checks it, and returns a boolean. This is not a separate
system — it is what `.check` does.

You can also write verified implementations using HOAS combinators:

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  # Write a function in HOAS, kernel type-checks it, extract as Nix function
  succ = v.verify (H.forall "x" H.nat (_: H.nat))
                   (v.fn "x" H.nat (x: H.succ x));
in
  succ 5    # 6 — a certified Nix function
```

The kernel checks the implementation against its type at `nix eval` time.
If the types don't match, you get an error before anything builds.
See the [Kernel Architecture](/nix-effects/internals/kernel-architecture)
chapter for the full pipeline.

## What's in the box

The `fx` attrset is the entire public API:

| Namespace | Contents |
|-----------|---------|
| `fx.pure`, `fx.bind`, `fx.send`, `fx.map`, `fx.seq` | Freer monad kernel |
| `fx.run`, `fx.handle` | Trampoline interpreter |
| `fx.adapt`, `fx.adaptHandlers` | Handler composition |
| `fx.types.*` | Type system (primitives, constructors, dependent, refinement, universe) |
| `fx.types.hoas` | HOAS surface combinators for the kernel |
| `fx.types.elaborateType`, etc. | Elaboration bridge: fx.types ↔ kernel |
| `fx.types.verified` | Convenience combinators for writing verified implementations |
| `fx.effects.*` | Built-in effects (state, error, reader, writer, acc, choice, conditions, typecheck, linear) |
| `fx.stream.*` | Effectful lazy sequences |
