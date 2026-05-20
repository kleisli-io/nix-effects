# Introduction

Nix libraries often grow into small languages. A user declares entities,
reusable aspects, target classes, dependencies, and policies; a pipeline
turns that declarative graph into concrete Nix modules, files, packages,
or checks. Without a shared structure, every layer writes its own walker:
one for validation, one for documentation, one for dependency ordering,
one for rendering, one for diagnostics.

nix-effects is a typed, description-backed programming substrate for
pure Nix. Effects are the execution model; generated descriptions are
the shared structure; the kernel checks boundaries; generic tools,
diagnostics, proofs, and ornaments reuse the same shape. Everything runs
at `nix eval` time, before anything builds or ships.

The unusual part is that the kernel is hosted inside Nix evaluation
itself. Nix normally gives libraries functions, attrsets, assertions,
and module option types. nix-effects adds typed descriptions that generic
programs can inspect. Validation is therefore not a hand-written walker:
it is one interpretation of a type description, next to schemas,
documentation, dependency extraction, and DSL interpretation.

The type layer is backed by a Martin-Löf dependent type checker in
`src/tc/` with Pi, Sigma, identity types with J, explicit universe
levels, HOAS elaboration, generated datatypes, and verified extraction
of plain Nix functions from proof terms. Descriptions provide reusable
datatype shapes, so domain DSLs can be validated, interpreted,
documented, transformed, or extracted by generic tools instead of
one-off traversals.
The bidirectional checker sends `typeCheck` effects carrying a
field-path context, so type errors in deeply nested terms come back
localized to the field that broke.

## What it looks like

A target class is one of a small set of strings. In nix-effects, that is
a refinement type:

```nix
let
  inherit (fx.types) String refined;

  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);
in {
  ok  = TargetClass.check "module";   # true
  bad = TargetClass.check "fleet";    # false
}
```

Behind the scenes, `.check` runs the MLTT kernel's decision procedure
for the base type, then evaluates the refinement predicate. For a
refinement type like `TargetClass`, this is fast: the kernel confirms a
string, the guard confirms membership in the known target classes. You
write normal Nix and the kernel runs behind the scenes.

But checking individual values is only the starting point. The same
kernel-backed structure supports derived validation for compound shapes
and can also verify entire functions, then extract them as ordinary Nix
functions.

## Verified functions over real data

Write an implementation in HOAS (Higher-Order Abstract Syntax), the
kernel type-checks it, and `v.verify` extracts a callable Nix function.

Here is a small aspect declaration predicate. The kernel verifies a
function that takes a record with `name`, `target`, and `requires`
fields, then checks that the target is one of the classes this pipeline
knows how to render. The check uses string comparison inside the kernel
— `strEq` is a kernel primitive, not a Nix-level hack.

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  AspectDecl = H.record [
    { name = "name";     type = H.string; }
    { name = "target";   type = H.string; }
    { name = "requires"; type = H.listOf H.string; }
  ];

  targets =
    H.cons H.string (v.str "module")
      (H.cons H.string (v.str "file")
        (H.cons H.string (v.str "package")
          (H.cons H.string (v.str "check") (H.nil H.string))));

  validateAspect = v.verify (H.forall "a" AspectDecl (_: H.bool))
    (v.fn "a" AspectDecl (a:
      v.strElem (v.field AspectDecl "target" a) targets));
in {
  ok = validateAspect {
    name = "workspace-shell";
    target = "module";
    requires = [ "toolchain" ];
  };   # true

  bad = validateAspect {
    name = "workspace-aspect";
    target = "fleet";
    requires = [ ];
  };   # false
}
```

`validateAspect` is a plain Nix function. You call it with a plain Nix
attrset. But the implementation was verified by the MLTT kernel before
extraction — the kernel confirmed that the function matches its type
(`AspectDecl → Bool`), that field projections are well-typed, and that
the string membership check composes correctly. If you made a type error
in the implementation — say, compared a `Bool` where a `String` was
expected — the kernel would reject it at `nix eval` time.

The record type (`H.record`) elaborates to nested Sigma in the kernel.
`v.field` desugars to the right chain of first/second projections.
`v.strEq` is a kernel primitive that reduces `strEq "foo" "foo"` to
`true` during normalization. `v.strElem` folds over a list with `strEq`.
None of this is Nix-level string comparison — it's computation inside
the proof checker.

## Proofs as programs

The same kernel that verifies functions also checks mathematical
proofs. Both are the same judgment — `Γ ⊢ t : T` — applied
differently. A verified function proves that an implementation inhabits
its type. An equality proof proves that two expressions reduce to the
same normal form.

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  # Verified addition: Nat → Nat → Nat by structural recursion
  add = v.verify (H.forall "m" H.nat (_: H.forall "n" H.nat (_: H.nat)))
    (v.fn "m" H.nat (m: v.fn "n" H.nat (n:
      v.match H.nat m {
        zero = n;
        succ = _k: ih: H.succ ih;
      })));

in {
  five = add 2 3;     # 5

  # Prove 3 + 5 = 8: the kernel normalizes both sides, Refl witnesses equality
  proof = (H.checkHoas (H.eq H.nat (add (H.natLit 3) (H.natLit 5)) (H.natLit 8))
                       H.refl).tag == "refl";    # true
}
```

The `add` function is extracted exactly like `validateAspect` — write in
HOAS, kernel checks, extract a Nix function. The equality proof goes
one step further: the kernel normalizes `add(3, 5)` by running the
structural recursion, arrives at `8`, and confirms `Refl` witnesses
`8 = 8`. This is computational proof — the kernel computes the answer
and verifies that computation agrees with the claim.

## The effect system

The "effects" in nix-effects are algebraic effects implemented via a
freer monad (Kiselyov & Ishii 2015). A computation is a tree of
effects with continuations. A handler walks the tree, interpreting
each effect:

```nix
let
  inherit (fx) pure bind run;
  inherit (fx.effects) get put;

  # Read state, double it, write it back
  doubleState = bind get (s: bind (put (s * 2)) (_: pure s));

  result = run doubleState fx.effects.state.handler 21;
  # result.value = 21, result.state = 42
in result
```

This matters for type checking because it separates *what* to check
from *how* to report. When `DepRecord.validate` finds a type error,
it sends a `typeCheck` effect. The handler decides the policy:

- **Strict** — abort on the first error
- **Collecting** — gather all errors, keep checking
- **Logging** — record every check, pass or fail

Same validation logic, different handler. The checker reports through
the same effect substrate, so validation policy composes with the rest
of the effect system.

## The verification spectrum

Not everything needs proofs. nix-effects supports four levels of
assurance, and you pick the one that fits:

**Level 1 — Contract.** Write normal Nix. Types check values via
`.check`. The kernel runs behind the scenes. Zero cost to adopt.

```nix
TargetClass = refined "TargetClass" String
  (x: builtins.elem x [ "module" "file" "package" "check" ]);
TargetClass.check "module"    # true
```

**Level 2 — Boundary.** Data is checked by the kernel at module
interfaces. Every type has a `kernelType` and `.check` is derived from
the kernel's `decide` procedure. This is what all built-in types do by
default — `(ListOf String).check ["a" "b"]` elaborates the list into a
kernel term and type-checks it.

**Level 3 — Property.** Write proof terms in HOAS that the kernel
verifies. Prove that `3 + 5 = 8`, or that double negation on booleans
is the identity, or that `append([1,2], [3]) = [1,2,3]`.

**Level 4 — Full.** The implementation IS the proof term. Write in
HOAS, the kernel verifies, `extract` produces a Nix function correct by
construction. The `validateAspect` example above is Level 4 — the kernel
verified the validator before extracting it as a callable function.

Most users will stay at levels 1 and 2. The kernel is there when you
need it. With record types and string comparison now in the kernel,
Level 4 handles real-world validation — not just arithmetic on natural
numbers.

## How this document is organized

The rest of the guide builds up from here:

- **[Getting Started](getting-started.md)** sets up the library and
  shows the first type, effect, and generated datatype.
- **[Effects and Handlers](effects-and-handlers.md)** explains the
  execution model: computations send operations, handlers choose policy.
- **[Typed Validation](typed-validation.md)** covers primitive,
  refined, structured, and dependent validation boundaries.
- **[Generated Datatypes](generated-datatypes.md)** introduces
  description-backed data as the shared structure.
- **[Generic Programming](generic-programming.md)** shows how schemas,
  dependency graphs, diagnostics, and views derive from that structure.
- **[Ornaments and Description-Backed Data](ornaments.md)** refines
  generated shapes while preserving forgetful maps.
- **[Proof Guide](proof-guide.md)** builds proofs and verified
  implementations from kernel-checked HOAS terms.
- **[Theory](theory.md)** explains the ideas behind the model.
- The internals chapters document the trampoline, architecture, kernel
  implementation, and formal specification for contributors.

## References

1. Martin-Lof, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.

2. Kiselyov, O., & Ishii, H. (2015). *Freer Monads, More Extensible
   Effects*. Haskell Symposium 2015.
   [[pdf](https://okmij.org/ftp/Haskell/extensible/more.pdf)]

3. Plotkin, G., & Pretnar, M. (2009). *Handlers of Algebraic Effects*.
   ESOP 2009.
   [[doi](https://doi.org/10.1007/978-3-642-00590-9_7)]

4. Findler, R., & Felleisen, M. (2002). *Contracts for Higher-Order
   Functions*. ICFP 2002.
   [[doi](https://doi.org/10.1145/581478.581484)]
