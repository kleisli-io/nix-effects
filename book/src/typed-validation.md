# Typed Validation

Typed validation is the first user-facing layer built on the effect
model. A type describes the values a boundary accepts. The same type can
answer a fast yes/no question or produce structured diagnostics through
a handler.

The point is not only that validation exists. In nix-effects, validation
is derived from the type description. Users write the shape and any
domain refinements; they do not write a recursive validator for every
record, list, variant, or generated datatype. That derive-style
capability is hosted inside Nix itself, not delegated to an external
schema engine or macro system.

This chapter uses value-level types. Later chapters show how generated
datatypes carry reusable descriptions that the same checker, diagnostic
tools, interpreters, and generic derivations consume.

## Primitive and refined types

Primitive types wrap Nix value predicates with kernel-backed type
information:

```nix
let inherit (fx.types) Int String Bool;
in {
  okInt = Int.check 3;
  okString = String.check "aspect";
  badBool = Bool.check "true";
}
```

Refinement types narrow an existing type with a predicate:

```nix
let
  inherit (fx.types) String refined;
  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);
in {
  ok = TargetClass.check "module";
  bad = TargetClass.check "fleet";
}
```

Use refinements for named boundary conditions: target classes,
non-empty names, supported dialects, allowed protocol versions, and
similar concrete constraints.

## Structured values

Records and lists compose types into larger boundaries:

```nix
let
  inherit (fx.types) Record String ListOf refined;
  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);

  AspectDecl = Record {
    name = String;
    target = TargetClass;
    requires = ListOf String;
  };
in
  AspectDecl.check {
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
  }
```

The check is structural and derived. Each field is checked with its own
type, and the composed type preserves enough context for diagnostics to
point at the field that failed. Adding another field or nesting another
record changes the type description; the validator follows automatically.

## Dependent records

Some fields depend on earlier fields. `DepRecord` evaluates field types
left to right, so later field types can inspect earlier values:

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
  };

  bad = AspectDecl.checkFlat {
    generated = true;
    target = "fleet";
    requires = [ ];
  };
}
```

The dependent field type is never evaluated until the fields it depends
on have passed. That ordering keeps diagnostics local and avoids running
domain logic on malformed input.

## Check vs validate

Use `.check` when you need a boolean:

```nix
AspectDecl.checkFlat value
```

Use `.validate` when the caller needs diagnostics:

```nix
fx.run (AspectDecl.validate value)
  fx.effects.typecheck.collecting []
```

The validation path reports through effects, so choosing a handler
chooses policy. A CLI can collect every field error. CI can abort on the
first fatal error. Tests can inspect the emitted diagnostics as data.

This separates two concerns that are often mixed together in Nix DSLs:
the type describes the accepted shape, while the handler decides whether
a failed check becomes an exception, a list of diagnostics, or a trace.

## Where the kernel fits

Every public type carries a kernel representation. Primitive and
first-order types can use fast decidable checks. Higher-order and proof
oriented boundaries use HOAS terms that the kernel checks directly.

This is one model, not two. Value-level validation is the practical
entry point; generated datatypes and verified functions reuse the same
kernel-backed structure when the boundary needs more evidence than a
predicate can provide.
