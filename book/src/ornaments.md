# Ornaments and Description-Backed Data

Generated datatypes in nix-effects are description-backed. A datatype is
not only a bundle of constructors; it also carries a `Desc` tree and
metadata that generic tools can inspect. That is what makes the same
datatype usable by the checker, value walkers, schema derivation,
dependency extraction, and ornaments.

An ornament refines one generated datatype into another while preserving a
forgetful map back to the base datatype. Use it when one layer needs more
information than another layer, but the enriched value should still be
usable wherever the base value was expected.

## Description-backed datatypes

Start with an ordinary generated datatype:

```nix
let
  fx = import ./nix/nix-effects {};
  H = fx.types.hoas;
  G = fx.types.generic;

  Aspect = H.datatype "Aspect" [
    (H.con "aspect" [
      (H.field "name" H.string)
      (H.field "target" H.string)
      (H.field "requires" (H.listOf H.string))
    ])
  ];
in Aspect
```

`Aspect` exposes:

- `Aspect.D`: the description used by the kernel.
- `Aspect.T`: the generated type.
- `Aspect.aspect`: the constructor.
- `_dtypeMeta`: constructor and field metadata used by generic tools.

The generic layer is the usual interface for description-backed
programming:

```nix
let
  info = G.datatype.datatypeInfo Aspect.T;
  value = G.value.review Aspect.T {
    _con = "aspect";
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
  };
in {
  constructors = map (c: c.name) info.constructors;
  roundtrip = G.value.view Aspect.T value;
}
```

`review` turns a constructor record into a HOAS value. `view` turns the
HOAS value back into a named constructor record. Derivation helpers such
as `G.derive.deriveDescriptor`, `G.derive.deriveSchema`, and
`G.derive.deriveDeps` consume the same metadata.

## Plain ornaments

A plain ornament adds fields while retaining enough structure to forget
back to the base datatype:

```nix
let
  ResolvedAspect = G.ornaments.ornament Aspect {
    name = "ResolvedAspect";
    constructors.aspect.fields = [
      { keep = "name"; }
      { keep = "target"; }
      { keep = "requires"; }
      { insert = "resolvedPath"; type = H.string; }
    ];
  };

  resolved = G.value.review ResolvedAspect.T {
    _con = "aspect";
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
    resolvedPath = "modules/workspace-shell.nix";
  };
in G.value.view Aspect.T (G.ornaments.forget ResolvedAspect resolved)
```

The result is:

```nix
{
  _con = "aspect";
  name = "workspace-shell";
  target = "module";
  requires = [ "toolchain" ];
}
```

The important property is one-way. Many resolved aspects may forget to the
same aspect. The ornament says how to drop the inserted structure without
changing the base shape.

Plain ornaments are useful when the enriched value already exists. They
give you checked forgetful maps, composition, and pullback transport:

```nix
G.ornaments.forget ResolvedAspect resolved
G.ornaments.compose Outer Inner
G.ornaments.pullback ResolvedAspect baseFunction resolved
```

## Functional ornaments

A functional ornament adds the forward direction: a section of the
forgetful map.

```nix
section : base -> ornamented
forget (section x) = x
```

In the generic API, build a functional ornament from a base datatype, an
ornament spec, and explicit synthesis functions for inserted fields:

```nix
let
  ResolvedAspect = G.ornaments.functional {
    base = Aspect;
    spec = {
      name = "ResolvedAspect";
      constructors.aspect.fields = [
        { keep = "name"; }
        { keep = "target"; }
        { keep = "requires"; }
        { insert = "resolvedPath"; type = H.string; }
      ];
    };
    synth.constructors.aspect.fields.resolvedPath =
      ctx: "modules/${ctx.baseRecord.name}.nix";
  };

  aspect = G.value.review Aspect.T {
    _con = "aspect";
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
  };

  resolved = G.ornaments.build ResolvedAspect aspect;
in {
  enriched = G.value.view ResolvedAspect.meta.ornamented.T resolved;
  forgotten = G.value.view Aspect.T (G.ornaments.forget ResolvedAspect resolved);
}
```

The enriched record contains the synthesized resolvedPath:

```nix
{
  _con = "aspect";
  name = "workspace-shell";
  target = "module";
  requires = [ "toolchain" ];
  resolvedPath = "modules/workspace-shell.nix";
}
```

The forgotten record is the original aspect. This gives a practical
workflow: construct the small base value first, then let the functional
ornament add canonical metadata.

## Composing enrichments

Functional ornaments compose when the outer ornament starts from the
inner ornament's generated datatype:

```nix
let
  MaterializedAspect = G.ornaments.functional {
    base = ResolvedAspect.meta.ornamented;
    spec = {
      name = "MaterializedAspect";
      constructors.aspect.fields = [
        { keep = "name"; }
        { keep = "target"; }
        { keep = "requires"; }
        { keep = "resolvedPath"; }
        { insert = "order"; type = H.nat; }
      ];
    };
    synth.constructors.aspect.fields.order = _ctx: 1;
  };

  Materialized = G.ornaments.composeFunctional MaterializedAspect ResolvedAspect;
in G.ornaments.build Materialized aspect
```

The composed section builds the final enriched value directly from the
base aspect. Forgetting the result through the composed ornament returns
the base aspect.

## Lifting producers and transforms

Producer lifting runs a base producer, then enriches its output through
the functional section:

```nix
let
  makeAspect =
    H.ann
      (H.lam "aspect" Aspect.T (_:
        G.value.review Aspect.T {
          _con = "aspect";
          name = "workspace-shell";
          target = "module";
          requires = [ "toolchain" ];
        }))
      (H.forall "_" Aspect.T (_: Aspect.T));

  lifted = G.ornaments.liftProducer Materialized makeAspect aspect;
in G.value.view MaterializedAspect.meta.ornamented.T lifted
```

The base function still only knows about `Aspect`. The lifted producer
returns the canonical materialized aspect. Forgetting the lifted result gives
the base producer's result.

Transform lifting is similar, but starts from an ornamented input:

```nix
G.ornaments.liftTransform {
  input = ResolvedAspect;
  output = MaterializedAspect;
  fn = baseTransform;
} resolved
```

The input is forgotten to the base, `fn` runs on the base value, and the
output section rebuilds the canonical enriched result.

## Obligations and diagnostics

Inserted fields must have a builder, a declared measure, or an explicit
proof builder. Validation is total and returns structured diagnostics:

```nix
G.ornaments.validateFunctional {
  base = Aspect;
  spec = {
    name = "BrokenResolvedAspect";
    constructors.aspect.fields = [
      { keep = "name"; }
      { keep = "target"; }
      { keep = "requires"; }
      { insert = "resolvedPath"; type = H.string; }
    ];
  };
  synth = {};
}
```

The diagnostic identifies the missing field builder:

```nix
{
  ok = false;
  diagnostics = [{
    code = "functional.missing-builder";
    path = [ "functional" "constructors" "aspect" "fields" "resolvedPath" ];
    message = "inserted field needs builder";
    severity = "error";
  }];
}
```

Proof-marked inserted fields use `proof = true` or `role = "proof"` and
report `functional.unresolved-proof` until a proof builder is supplied.
Measure-derived inserted fields use `measure = "<name>"` and require a
matching entry under `measures`.

## Algebraic ornaments

Algebraic ornaments are the case where inserted indices or fields are
computed from a fold over the base value. The canonical example is
ornamenting a list into a vector by inserting its length.

The public helper is `G.ornaments.algOrn`. It validates the supported
description/algebra fragment before constructing the ornament. The
current supported fragment covers `ret`, `arg`, `rec`, keep-only `pi`,
and `plus`. Unsupported function-domain aggregation remains explicit:
validation reports a shape diagnostic instead of guessing an algebra.

Use algebraic ornaments when the extra information is determined by the
base structure itself. Use functional ornaments when the extra
information comes from a user-provided synthesis function, proof builder,
or declared measure.

## API summary

HOAS layer:

```nix
H.ornament base spec
H.ornDesc ornament
H.ornForget ornament
H.ornCompose outer inner
H.ornPullback ornament resultTy baseFn
H.ornLiftFold ornament resultTy baseFold

H.functionalOrnament { ornament; chooseIndex; section; ... }
H.ornBuild functional index baseValue
H.ornLiftProducer functional baseFn index baseInput
H.ornLiftTransform { input; output; fn; } outputIndex inputIndex ornamentedInput
```

Generic layer:

```nix
G.ornaments.ornament base spec
G.ornaments.forget ornamented value
G.ornaments.compose outer inner
G.ornaments.pullback ornamented baseFn value

G.ornaments.functional { base; spec; synth; ... }
G.ornaments.validateFunctional { base; spec; synth; ... }
G.ornaments.build functional baseValue
G.ornaments.composeFunctional outer inner
G.ornaments.liftProducer functional baseFn baseInput
G.ornaments.liftTransform { input; output; fn; } ornamentedInput
```

The generic layer is the best default for application code. Drop to HOAS
when you need direct indexed terms, explicit proof terms, or kernel-level
transport.
