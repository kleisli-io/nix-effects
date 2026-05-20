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

## Ornament composition

Plain, functional, and algebraic ornaments all refine a single base
datatype at the whole-type level. Three additional constructions
refine ornaments themselves, so the refinement *at one field position*
can be an ornament rather than the identity:

- **Leaf functional ornaments** lift a Nix-meta function `f : B → A`
  into an ornament of a primitive HOAS type former. They are the
  base case for refinements on non-μ types (`H.string`, `H.derivation`,
  `H.thunk`, …) where there is no constructor structure to walk.
- **Functorial container lifts** carry an ornament `O : Ornament A A'`
  through a strictly-positive container functor (`List`, `Attrs`,
  `Maybe`, or a single record field) to produce an ornament between the
  lifted containers, with forget defined by the standard functorial
  action.
- **Sub-ornament composition at `keep`** is the spec verb
  `{ keep = "x"; sub = O; }` inside a `G.ornaments.ornament` call. It
  declares that the kept field carries the *refined* type at the
  source and forgets through `O.forget` at that field on the way to
  the base.

These compose: a `keep + sub` may use a `lift.list` of a
`thunkOrnament`, and so on.

### Leaf functional ornaments

A leaf functional ornament refines a primitive HOAS type former by
attaching a Nix-meta function pair `(forget, section)`. Construction
requires the primitive to satisfy `_htag ≠ "mu"`; μ-encoded bases use
`H.ornament` or `H.functionalOrnament` instead.

```nix
let
  fx = import ./nix/nix-effects {};
  H = fx.types.hoas;

  IdString = H.leafOrnament {
    primitive = H.string;
    forget = x: x;
    section = x: x;
  };
in IdString.forget "hello"
```

The identity is the trivial case; the construction earns its keep when
`forget` is a non-trivial Nix function such as `forceThunk`. The
literature anchor is Dagand and McBride, *Transporting Functions
across Ornaments* (JFP 2014), which gives the general construction of
a functional ornament over `A` induced by a function `f : B → A`. The
leaf case specialises that construction to primitive type formers.

The derived constructor `H.thunkOrnament` packages the lift of
`forceThunk : Thunk a → a` and its section `mkThunk : a → Thunk a`:

```nix
H.thunkOrnament inner
≡ H.leafOrnament {
    primitive = H.thunk inner;
    forget = fx.state.thunk.forceThunk;
    section = fx.state.thunk.mkThunk;
    meta = { name = "Thunk"; baseHtag = "thunk"; inner = inner; };
  }
```

The `Thunk` carrier is the kernel's deepSeq-safe wrapper for transport
of cyclic or otherwise force-unsafe values through handler state; see
`src/state/thunk.nix` for the carrier shape and discipline. `H.thunk`
is the leaf functional ornament whose forget is `forceThunk` — the
ornament algebra is the principled home for the `Thunk → a` story
that the runtime already follows.

### Functorial container lifts

Given an ornament `O : Ornament A A'`, each strictly-positive
container functor `F` extends `O` to an ornament `F(O) : Ornament
F(A) F(A')` whose forget is `F`'s functorial action on `O.forget`.
The kernel exposes four lifts under `G.ornaments.lift`:

```nix
G.ornaments.lift.list  : Ornament A A' -> Ornament (List A) (List A')
G.ornaments.lift.attrs : Ornament A A' -> Ornament (Attrs A) (Attrs A')
G.ornaments.lift.maybe : Ornament A A' -> Ornament (Maybe A) (Maybe A')
G.ornaments.lift.field : String -> Ornament A A' -> Ornament Record Record'
```

Forget is `map o.forget`, `mapAttrs (_: o.forget)`, the null-passthrough
of `o.forget`, and the single-field rewrite `r // { ${name} = o.forget
r.${name}; }` respectively. Section mirrors forget on the dual side.

```nix
let
  fx = import ./nix/nix-effects {};
  H = fx.types.hoas;
  G = fx.types.generic;

  drvA = { type = "derivation"; name = "a"; outPath = "/nix/store/a"; };
  drvB = { type = "derivation"; name = "b"; outPath = "/nix/store/b"; };

  thunked = H.thunkOrnament H.derivation;
  paths   = G.ornaments.lift.list thunked;
in paths.forget [ (thunked.section drvA) (thunked.section drvB) ]
# ≡ [ drvA drvB ]
```

The literature anchor is Dagand, *A Cosmology of Datatypes* (PhD
thesis, Strathclyde 2013), chapter 6 "Functoriality of refinements." The
four lifts are siblings, not derived from one another at the kernel
boundary: each is the functorial action of an ornament along the
corresponding container functor. `lift.field` is the elementary
product-component move; the other three are the analogous moves for
`List`, `Attrs`, and `Maybe`. The container lifts decompose through
`lift.field` via the μ-encoding of containers, but the kernel ships
them all directly so consumers do not pay μ-unfolding cost at every
use site.

### Sub-ornament composition at `keep`

The spec language of `G.ornaments.ornament` recognises
`{ keep = "fieldName"; sub = O; }` as a directive that the named
field carries `O`'s *refined* type on the ornamented side and
forgets through `O.forget` at that field. The plain `{ keep =
"fieldName"; }` form remains the categorical identity at the kept
position; the `sub` verb adds the refinement.

```nix
let
  fx = import ./nix/nix-effects {};
  H = fx.types.hoas;
  G = fx.types.generic;

  drv = { type = "derivation"; name = "x"; outPath = "/nix/store/x"; };

  Box = H.datatype "Box" [
    (H.con "box" [ (H.field "value" H.derivation) ])
  ];

  TaggedThunkBox = G.ornaments.ornament Box {
    name = "TaggedThunkBox";
    constructors.box.fields = [
      { keep = "value"; sub = H.thunkOrnament H.derivation; }
      { insert = "tag"; type = H.bool; }
    ];
  };

  state = {
    _con = "box";
    value = (H.thunkOrnament H.derivation).section drv;
    tag = true;
  };
in G.ornaments.forget TaggedThunkBox state
# ≡ { _con = "box"; value = drv; }
```

The forget walker copies plain `keep` fields, drops `insert` fields,
and dispatches `keep + sub` fields through the sub-ornament's forget.
Constructor `_con` is preserved because the kernel reuses the base
constructor's name for the refined branch.

Sub-type agreement is checked at spec time. A `sub` whose forward
type disagrees with the kept field's type produces an
`ornament.sub-type-mismatch` diagnostic; a `sub` that is not a
recognised ornament produces `ornament.sub-not-ornament`.

### A single forget, two evaluations

`G.ornaments.forget : Ornamented → Value → Value` is one morphism. The
HOAS-term path and the Nix-meta path are two evaluations of the same
morphism; the commutation `eval (forgetHoas t) ≡ forgetMeta (eval t)`
is a theorem of the framework. Dispatch is structural on the
well-formed sum `_htag` (HOAS term) ⊕ `_con` (Nix-meta μ-value):

```nix
G.ornaments.forget ornamented value
# value._htag  -> HOAS-term path (returns HOAS-applied forget)
# value._con   -> Nix-meta path  (returns Nix attrset)
# both / neither / non-attrset -> throws
```

Both internal paths are reachable as
`G.ornaments._internal.{forgetHoas, forgetMeta}` for tests that need
to pin the evaluator, but application code calls `G.ornaments.forget`
and lets the dispatcher pick.

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

H.leafOrnament { primitive; forget; section; sectionProof?; meta?; }
H.thunkOrnament inner
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

G.ornaments.lift.list  o
G.ornaments.lift.attrs o
G.ornaments.lift.maybe o
G.ornaments.lift.field name o
```

The generic layer is the best default for application code. Drop to HOAS
when you need direct indexed terms, explicit proof terms, or kernel-level
transport.
