# Generic Programming

Generic programming is the payoff for description-backed data. Once a
datatype exposes its constructors, fields, and description, tools can
consume that structure directly instead of maintaining hand-written
walkers for every domain shape.

The same generated datatype can feed a checker, a documentation surface,
a dependency extractor, a schema generator, and an ornament. Those tools
agree because they read the same metadata.

This is the consequence of hosting the typed description language inside
Nix. There is no separate schema file to keep synchronized with the DSL,
and no per-datatype validator to write. A new user datatype participates
because the generic programs consume the levitated description, not a
closed set of special cases known in advance.

## Inspecting metadata

```nix
let
  G = fx.types.generic;
  info = G.datatype.datatypeInfo Aspect.T;
in {
  name = info.name;
  constructors = map (c: c.name) info.constructors;
}
```

`datatypeInfo` is the stable entry point for generated datatype
metadata. It returns the public structure: datatype name, constructors,
field names, field types, and description data needed by derivations.

## Deriving descriptors

`deriveDescriptor` turns datatype metadata into a neutral structural
description suitable for tools that do not want to depend on the HOAS
representation directly:

```nix
let
  G = fx.types.generic;
in
  G.derive.deriveDescriptor Aspect.T
```

A descriptor is not a second source of truth. It is a view of the
datatype's existing structure.

## Deriving schemas

Schema derivation uses the same fields and constructor tags:

```nix
G.derive.deriveSchema Aspect.T
```

Use this for external validation surfaces, generated documentation, or
tooling that needs to explain the shape to systems outside the kernel.
The schema follows the datatype; changing the datatype changes the
derived schema.

## Deriving dependencies

Dependency extraction is another consumer of the same shape:

```nix
G.derive.deriveDeps Aspect.T aspect
```

This is useful when a domain value references other values by name or
path. For an aspect declaration, the `requires` field can become the
dependency edge list for a topological interpreter. The generic walker
handles traversal; domain-specific metadata decides which fields count
as references.

## Diagnostics from shape

Structured diagnostics become easier when every field has a stable path.
The validator can report:

```nix
[ "constructors" "aspect" "fields" "requires" 0 ]
```

instead of a string-only error. That path is reusable in CLI output,
HTML documentation, editor integrations, and test assertions.

The path is not guessed by a custom recursive function. It is produced
by the same generic descent that reads constructor and field metadata.

## Avoid ad hoc walkers

The design rule is direct: if a tool needs to traverse a generated
datatype, start from `datatypeInfo`, `view`, `review`, and the derive
helpers. Do not duplicate the datatype's shape in a separate hand-written
walker. The description is already the shared structure.

The ornaments chapter builds on this. An ornament refines one generated
shape into another while preserving a forgetful map, and functional
ornaments add a canonical way to rebuild the enriched value.
