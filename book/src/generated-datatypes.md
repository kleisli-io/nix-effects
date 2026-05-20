# Generated Datatypes

Generated datatypes make structure explicit. A datatype is not only a
constructor API; it also carries the description and metadata that the
kernel, generic walkers, diagnostics, schemas, dependency extraction,
and ornaments reuse.

Use generated datatypes when a domain value should be more than an
untyped attrset. The generated value has constructors for building data,
a type for checking data, and public structural evidence for tools.

## A first datatype

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

The generated `Aspect` object exposes:

- `Aspect.D` — the description used by the kernel.
- `Aspect.T` — the generated type.
- `Aspect.aspect` — the constructor.
- `_dtypeMeta` — constructor and field metadata.

The description is the important part. It is the common shape that lets
multiple consumers agree on what an aspect declaration is.

## View and review

Application code usually works with named constructor records:

```nix
let
  G = fx.types.generic;

  aspect = G.value.review Aspect.T {
    _con = "aspect";
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
  };
in
  G.value.view Aspect.T aspect
```

`review` turns a constructor record into the generated value. `view`
turns the generated value back into a constructor record. This is the
bridge between ergonomic Nix data and the description-backed
representation the kernel can inspect.

## Generated families

The datatype layer supports several shapes:

- `datatype` for ordinary generated datatypes.
- `datatypeP` when constructors are parameterized.
- `datatypeI` when the family is indexed.
- `datatypePI` when both parameters and indices are needed.

The more indexed the family, the more precisely the type can state what
the value means. The public model is still the same: a description, a
generated type, constructors, and metadata.

## Stack-safe elaboration

Generated constructor trees can be large. nix-effects elaborates them
through the same stack-safe machinery used by the effect interpreter and
kernel normalizer. Deep values should remain ordinary data, not a reason
to avoid the generated layer.

That is why generated datatypes are suitable for infrastructure DSLs:
they give the checker real structure without moving the user out of
pure Nix evaluation.

## What comes next

The next chapter shows what the metadata buys. Once a datatype carries a
description, generic tools can derive schemas, dependency graphs,
diagnostics, and ornaments without each tool inventing its own walker.
