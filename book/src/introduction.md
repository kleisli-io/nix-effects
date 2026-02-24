# Introduction

Nix configurations fail late. A misspelled option name, a string where an
integer belongs, a firewall rule that references a port no service
listens on — these surface at build time, at deploy time, or when
a user files a ticket. The NixOS module system catches some of this
with `mkOption` and `types.str`, but the checking is shallow: it
validates individual fields, not relationships between them. "The build
system must appear in the declared platforms list" is a constraint no
existing Nix tool can express as a type.

nix-effects is a type-checking kernel, an algebraic effect system, and
a dependent type library, implemented entirely in pure Nix. It catches
configuration errors at `nix eval` time — before anything builds or
ships. The kernel can verify that a validator function is correct,
then extract it as an ordinary Nix function you call on plain attrsets.

## What it looks like

A port number is an integer between 1 and 65535. In nix-effects, that's
a refinement type:

```nix
let
  inherit (fx.types) Int refined;

  Port = refined "Port" Int (x: x >= 1 && x <= 65535);
in {
  ok  = Port.check 8080;   # true
  bad = Port.check 99999;  # false
}
```

Behind the scenes, `.check` runs the MLTT kernel's decision procedure —
the value is elaborated into a kernel term, type-checked, and the
predicate is evaluated. For a refinement type like `Port`, this is fast:
the kernel confirms the base type (`Int`), the guard confirms the range.
You write normal Nix and the kernel runs behind the scenes.

But checking individual values is only the starting point. The kernel
can also verify entire functions — confirm that a validator you wrote
is type-correct, then extract it as an ordinary Nix function.

## Verified functions over real data

Write an implementation in HOAS (Higher-Order Abstract Syntax), the
kernel type-checks it, and `v.verify` extracts a callable Nix function.

Here's a derivation spec validator. The kernel verifies a function that
takes a record with `license`, `platforms`, and `system` fields, then
checks three constraints: the build system appears in the platforms
list, the system is one of the supported architectures, and the license
is approved. All three checks use string comparison inside the kernel
— `strEq` is a kernel primitive, not a Nix-level hack.

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  Spec = H.record [
    { name = "license";   type = H.string; }
    { name = "platforms"; type = H.listOf H.string; }
    { name = "system";    type = H.string; }
  ];

  licenses = mkStrList [ "MIT" "Apache-2.0" "BSD-3-Clause" ];
  systems  = mkStrList [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" ];

  # Kernel-verified: system ∈ platforms AND system ∈ supported AND license ∈ approved
  validateSpec = v.verify (H.forall "s" Spec (_: H.bool))
    (v.fn "s" Spec (s:
      v.if_ H.bool (v.strElem (v.field Spec "system" s)
                               (v.field Spec "platforms" s)) {
        then_ = v.if_ H.bool (v.strElem (v.field Spec "system" s) systems) {
          then_ = v.strElem (v.field Spec "license" s) licenses;
          else_ = v.false_;
        };
        else_ = v.false_;
      }));
in {
  ok   = validateSpec {
    system = "x86_64-linux"; license = "MIT";
    platforms = [ "x86_64-linux" "aarch64-linux" ];
  };   # true

  bad  = validateSpec {
    system = "arm64"; license = "MIT";
    platforms = [ "x86_64-linux" ];
  };   # false — arm64 not in supported systems

  mismatch = validateSpec {
    system = "x86_64-linux"; license = "MIT";
    platforms = [ "aarch64-linux" ];
  };   # false — system not in its own platforms list
}
```

`validateSpec` is a plain Nix function. You call it with a plain Nix
attrset. But the implementation was verified by the MLTT kernel before
extraction — the kernel confirmed that the function matches its type
(`Spec → Bool`), that field projections are well-typed, and that the
string membership checks compose correctly. If you made a type error in
the implementation — say, compared a `Bool` where a `String` was
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

The `add` function is extracted exactly like `validateSpec` — write in
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

Same validation logic, different handler. The type-checking kernel
itself runs as an effectful computation on this same infrastructure —
the kernel is just another program running on the effects substrate.

## The verification spectrum

Not everything needs proofs. nix-effects supports four levels of
assurance, and you pick the one that fits:

**Level 1 — Contract.** Write normal Nix. Types check values via
`.check`. The kernel runs behind the scenes. Zero cost to adopt.

```nix
Port = refined "Port" Int (x: x >= 1 && x <= 65535);
Port.check 8080    # true
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
construction. The `validateSpec` example above is Level 4 — the kernel
verified the validator before extracting it as a callable function.

Most users will stay at levels 1 and 2. The kernel is there when you
need it. With record types and string comparison now in the kernel,
Level 4 handles real-world validation — not just arithmetic on natural
numbers.

## How this document is organized

The rest of the guide builds up from here:

- **[Getting Started](getting-started.md)** walks through installation,
  your first type, your first effect, and the end-to-end derivation demo.
- **[Proof Guide](proof-guide.md)** builds proofs incrementally — from
  computational equality through the J eliminator to proof-gated
  derivations that reject invalid configurations at eval time.
- **[Theory](theory.md)** covers the nine papers that shaped the
  design — algebraic effects, freer monads, dependent types, refinement
  types, the Fire Triangle, and why they fit together in pure Nix.
- **[Trampoline](trampoline.md)** explains how `builtins.genericClosure`
  becomes a trampoline for stack-safe evaluation at scale.
- **[Systems Architecture](systems-architecture.md)** describes the
  kernel-first design: one notion of type, one checking mechanism, no
  adequacy bridge.
- **[Kernel Architecture](kernel-architecture.md)** details the MLTT
  kernel internals — NbE, bidirectional checking, HOAS elaboration,
  extraction, and the trust model.
- **[Kernel Specification](kernel-spec.md)** gives the formal typing
  rules.

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
