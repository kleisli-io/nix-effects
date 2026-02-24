# Kernel Architecture

This chapter describes the type-checking kernel: its pipeline, its
primitives, and how to write verified implementations that the kernel
checks and extracts back to usable Nix functions.

## The "one system" architecture

nix-effects has one notion of type and one checking mechanism. Every
type is defined by its kernel representation. `.check` is derived
mechanically from the kernel's `decide` procedure. There is no
separate contract system, no adequacy bridge, and no possibility of
disagreement between the check predicate and the kernel.

```
Type system API
  Record, ListOf, DepRecord, refined, Pi, Sigma, ...
       |
       | elaboration
       v
Type-checking kernel (MLTT)
       |
       | checker runs as effectful computation
       v
Effects kernel (freer monad, FTCQueue, trampoline, handlers)
       |
       v
Pure Nix
```

Types are kernel types. `Record`, `ListOf`, `DepRecord`, `refined` —
all of them compile down to kernel constructions via elaboration.
Checking a value against a type is a kernel judgment. Proving a
universal property about a type is also a kernel judgment. Same
kernel, same judgment form `Γ ⊢ t : T`, two modes of interaction:
automated (decidable checking) and explicit (proof terms).

## The kernel pipeline

The kernel implements normalization by evaluation (NbE) with
bidirectional type checking. Six modules, each with a single
responsibility:

```
term.nix ──→ eval.nix ──→ value.nix
                              │
                          quote.nix ──→ term.nix
                              │
                          conv.nix
                              │
                          check.nix
```

| Module | Function | Signature |
|--------|----------|-----------|
| `term.nix` | Term constructors | `mkVar`, `mkPi`, `mkLam`, `mkApp`, ... |
| `eval.nix` | Evaluation | `Env × Tm → Val` |
| `value.nix` | Value constructors | `VLam`, `VPi`, `VPair`, `VZero`, ... |
| `quote.nix` | Quotation | `ℕ × Val → Tm` |
| `conv.nix` | Conversion checking | `ℕ × Val × Val → Bool` |
| `check.nix` | Type checking | `Ctx × Tm × Val → Tm` / `Ctx × Tm → Tm × Val` |

**Terms** (`Tm`) are the syntax — de Bruijn indexed expressions with
explicit binding structure. **Values** (`Val`) are the semantics —
fully normalized forms where lambdas are Nix closures (this is the NbE
trick). **Evaluation** converts terms to values. **Quotation** reads
values back to terms. **Conversion** checks whether two values are
definitionally equal by comparing their quoted forms.

The type checker is bidirectional:

- `check(Γ, t, T)` — check that term `t` has type `T` (type-directed)
- `infer(Γ, t)` — infer the type of term `t` (term-directed)
- `checkTypeLevel(Γ, T)` — compute the universe level of a type

### Trust model

The kernel has three layers with decreasing trust requirements:

**Layer 0 — Trusted Computing Base.** `eval`, `quote`, `conv`. Pure
functions. No side effects. No imports from the effect system. Bugs
here compromise soundness.

**Layer 1 — Semi-trusted.** `check`, `infer`, `checkTypeLevel`. Uses
the TCB and sends effects for error reporting. Bugs may produce wrong
error messages or reject valid terms, but cannot cause unsoundness.

**Layer 2 — Untrusted.** The elaborator (`hoas.nix`, `elaborate.nix`).
Translates surface syntax to core terms. Can have arbitrary bugs
without compromising safety — the kernel verifies the output.

## Axiomatized primitives

The kernel understands seven Nix primitive types as axioms. Each has a
type former, a literal constructor, and a typing rule. None have
eliminators — the kernel says "String is a type at level 0" and "a
string literal inhabits String" but cannot structurally decompose
these values.

| Nix type | Kernel type | Literal | Level |
|----------|-------------|---------|-------|
| `string` | `String` | `StringLit(s)` | 0 |
| `int` | `Int` | `IntLit(n)` | 0 |
| `float` | `Float` | `FloatLit(f)` | 0 |
| `set` | `Attrs` | `AttrsLit` | 0 |
| `path` | `Path` | `PathLit` | 0 |
| `lambda` | `Function` | `FnLit` | 0 |
| (any) | `Any` | `AnyLit` | 0 |

The structural types — `Nat`, `Bool`, `Unit`, `Void`, `List`, `Sum`,
`Sigma`, `Pi`, `Eq` — have full introduction and elimination rules.
This means the kernel can compute with natural numbers, booleans,
lists, pairs, and functions, but treats strings, integers, and other
Nix-native types as opaque tokens.

Axiomatized primitives are critical for real-world use. Without them,
verified modules can only work over `Nat`/`Bool`/`List`/`Sigma`/`Sum`.
With them, modules can handle ports (`Int`), service names (`String`),
configuration records (nested `Sigma`/`Attrs`), and so on.

## HOAS: the surface API

Writing de Bruijn indexed terms by hand is error-prone. The HOAS
(Higher-Order Abstract Syntax) layer lets you use Nix lambdas for
variable binding. The public API is `fx.types.hoas`.

### Type combinators

```nix
H = fx.types.hoas;

H.nat                         # Nat
H.bool                        # Bool
H.string                      # String
H.int_                        # Int
H.float_                      # Float
H.unit                        # Unit (nullary product)
H.void                        # Void (empty type)
H.listOf H.nat                # List Nat
H.sum H.nat H.bool            # Nat + Bool
H.forall "x" H.nat (_: H.bool)  # Π(x : Nat). Bool
H.sigma "x" H.nat (_: H.bool)   # Σ(x : Nat). Bool
H.u 0                         # U₀ (universe of small types)
```

### Term combinators

```nix
# Lambda: λ(x : Nat). x
H.lam "x" H.nat (x: x)

# Application
H.app f arg

# Natural number literals
H.zero                        # 0
H.succ H.zero                 # 1
H.natLit 42                   # 42 (sugar for 42 succs)

# Boolean literals
H.true_
H.false_

# Pairs
H.pair fst snd sigmaType

# Projections
H.fst_ p
H.snd_ p

# Sum injections
H.inl leftTy rightTy term
H.inr leftTy rightTy term

# String / Int / Float literals
H.stringLit "hello"
H.intLit 42
H.floatLit 3.14

# Type annotation
H.ann term type
```

### Eliminators

```nix
# Natural number induction
H.ind motive base step scrut

# Boolean elimination
H.boolElim motive onTrue onFalse scrut

# List elimination
H.listElim elemType motive onNil onCons scrut

# Sum elimination
H.sumElim leftTy rightTy motive onLeft onRight scrut

# Equality elimination (J)
H.j type lhs motive base rhs eq
```

### How HOAS compiles

Binding combinators produce HOAS markers — lightweight attrsets that
stand for bound variables at a specific depth. The `elaborate`
function (in `hoas.nix`) converts these to de Bruijn indexed `Tm`
terms:

```
H.lam "x" H.nat (x: H.succ x)
  │
  │ HOAS: x is a marker { _hoas = true; level = 0; }
  │
  ▼ elaborate (depth=0)
  │
  │ marker at level 0 → T.mkVar(0 - 0 - 1) = T.mkVar(0)
  │
  ▼
Lam("x", Nat, Succ(Var(0)))   ← de Bruijn term
```

The elaboration of nested binding forms is trampolined via
`builtins.genericClosure` for stack safety on deeply nested terms.

## The elaboration bridge

The elaboration bridge (`elaborate.nix`) connects the user-facing type
system to the kernel. It has six operations:

| Operation | Signature | Direction |
|-----------|-----------|-----------|
| `elaborateType` | `FxType → HoasTree` | type system → kernel |
| `elaborateValue` | `HoasTree × NixVal → HoasTree` | Nix value → kernel term |
| `extract` | `HoasTree × Val → NixValue` | kernel value → Nix value |
| `decide` | `HoasTree × NixVal → Bool` | decision procedure |
| `decideType` | `FxType × NixVal → Bool` | elaborate type, then decide |
| `verifyAndExtract` | `HoasTree × HoasTree → NixValue` | full pipeline |

### elaborateType

Converts an `fx.types` type into a HOAS tree. Dispatches on three
things, in order:

1. The `_kernel` field (types built via `mkType` with `kernelType`)
2. Structural fields (Pi: `domain`/`codomain`, Sigma: `fstType`/`sndFamily`)
3. Name convention (`"Bool"` → `H.bool`, `"String"` → `H.string`, etc.)

### elaborateValue

Converts a Nix value into a HOAS term, guided by a HOAS type. For
example, given `H.nat` and the Nix integer `3`, produces
`H.succ (H.succ (H.succ H.zero))`. Given `H.string` and `"hello"`,
produces `H.stringLit "hello"`.

### extract — the reverse direction

`extract` converts kernel values back to Nix values. It is the reverse
of `elaborateValue`. This is where the verification story becomes
interesting: you write an implementation as a HOAS term, the kernel
verifies it, `eval` produces a kernel value, and `extract` converts
the result to a usable Nix value.

```nix
# extract : HoasTree → Val → NixValue
extract H.nat (VSucc (VSucc VZero))   # → 2
extract H.bool VTrue                   # → true
extract H.string (VStringLit "hi")     # → "hi"
extract (H.listOf H.nat) (VCons ...)   # → [1 2 3]
extract (H.forall "x" ...) (VLam ...)  # → Nix function (!)
```

The Pi case is the most important. Extracting a verified function
produces a Nix function that:

1. Elaborates its argument into a kernel value (Nix → kernel)
2. Applies the kernel-verified closure
3. Extracts the result back (kernel → Nix)

Correct by construction — the kernel verified the term, `eval`
produced the closure, `extract` wraps with value conversion at the
boundaries.

### decide

The decision procedure. Returns `true` iff both elaboration and
kernel type-checking succeed:

```nix
decide = hoasTy: value:
  let
    result = builtins.tryEval (
      let
        hoasVal = elaborateValue hoasTy value;
        checked = H.checkHoas hoasTy hoasVal;
      in !(checked ? error)
    );
  in result.success && result.value;
```

This is the function that `mkType` uses to derive `.check`. Every
type's `.check` is `v: decide(kernelType, v)` — no hand-written
predicates.

### verifyAndExtract — the full pipeline

Type-check a HOAS term against a HOAS type, then extract the result:

```nix
verifyAndExtract = hoasTy: hoasImpl:
  let
    checked = H.checkHoas hoasTy hoasImpl;
  in if checked ? error
    then throw "verifyAndExtract: type check failed"
    else
      let
        tm = H.elab hoasImpl;         # HOAS → de Bruijn
        val = E.eval [] tm;           # evaluate to Val
      in extract hoasTy val;          # Val → Nix value
```

## Convenience combinators

Raw HOAS is verbose. The convenience combinator layer (`fx.types.verified`,
accessed as `v`) provides sugar that produces valid HOAS term trees:

```nix
v = fx.types.verified;
H = fx.types.hoas;
```

### Literals

```nix
v.nat 5          # H.natLit 5
v.str "hello"    # H.stringLit "hello"
v.int_ 42        # H.intLit 42
v.float_ 3.14    # H.floatLit 3.14
v.true_          # H.true_
v.false_         # H.false_
v.null_          # H.tt (unit)
```

### Binding forms

```nix
# Lambda: λ(x : Nat). body
v.fn "x" H.nat (x: body)

# Let: let x : Nat = 5 in body
v.let_ "x" H.nat (v.nat 5) (x: body)
```

### Eliminators with inferred motives

The convenience combinators construct the required motive automatically
from the result type. The motive is always constant (non-dependent):
`λ_. resultTy`.

```nix
# Boolean: if b then 1 else 0
v.if_ H.nat v.true_ { then_ = v.nat 1; else_ = v.nat 0; }

# Natural number: pattern match on n
v.match H.nat n {
  zero = v.nat 42;
  succ = k: ih: H.succ ih;
}

# List: fold over elements
v.matchList H.nat H.nat list {
  nil = v.nat 0;
  cons = h: t: ih: H.succ ih;   # count elements
}

# Sum: case split
v.matchSum H.nat H.bool H.nat scrut {
  left = x: H.succ x;
  right = _: v.nat 0;
}
```

### Derived combinators

```nix
# Map: apply f to each element
v.map H.nat H.nat succFn myList

# Fold: combine elements with accumulator
v.fold H.nat H.nat (v.nat 0) addFn myList

# Filter: keep elements matching predicate
v.filter H.nat isZeroFn myList
```

### Pairs and sums

```nix
v.pair fstTerm sndTerm sigmaType
v.fst p
v.snd p
v.inl leftTy rightTy term
v.inr leftTy rightTy term
v.app f arg
```

### The verify pipeline

`v.verify` wraps `verifyAndExtract` — type-check and extract in one
call:

```nix
v.verify type implementation
# = verifyAndExtract type implementation
```

## Writing verified implementations

The key insight: instead of writing Nix functions and trying to
elaborate them into kernel terms (which fails for closures), write
implementations as HOAS terms and **extract** Nix functions out. This
is the approach taken by Coq (extraction), Idris (compilation), and
F\*.

### Example: verified addition

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  addTy = H.forall "m" H.nat (_: H.forall "n" H.nat (_: H.nat));
  addImpl = v.fn "m" H.nat (m: v.fn "n" H.nat (n:
    v.match H.nat m {
      zero = n;
      succ = _k: ih: H.succ ih;
    }));

  # Kernel verifies: addImpl : Π(m:Nat). Π(n:Nat). Nat
  # Then extracts a 2-argument Nix function
  add = v.verify addTy addImpl;
in
  add 2 3    # → 5
```

What happens step by step:

1. `v.verify` calls `H.checkHoas addTy addImpl` — the kernel
   type-checks the HOAS term against the HOAS type
2. `H.elab addImpl` converts HOAS to de Bruijn indexed `Tm`
3. `E.eval [] tm` evaluates to a `VLam` value (a Nix closure via NbE)
4. `extract addTy val` wraps the `VLam` as a Nix function that
   elaborates arguments at call boundaries

The resulting `add` is an ordinary Nix function. Call it with Nix
integers. At each call, the argument is elaborated into a kernel
value, the verified closure runs, and the result is extracted back.

### Example: verified list operations

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  # Successor function: Nat → Nat
  succFn = v.fn "x" H.nat (x: H.succ x);

  # Map successor over a list
  input = H.cons H.nat (v.nat 0)
    (H.cons H.nat (v.nat 1)
      (H.cons H.nat (v.nat 2) (H.nil H.nat)));

  result = v.verify (H.listOf H.nat) (v.map H.nat H.nat succFn input);
in
  result    # → [1 2 3]
```

### Example: verified filter

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  # isZero : Nat → Bool
  isZero = v.fn "n" H.nat (n:
    v.match H.bool n {
      zero = v.true_;
      succ = _k: _ih: v.false_;
    });

  input = H.cons H.nat (v.nat 0)
    (H.cons H.nat (v.nat 1)
      (H.cons H.nat (v.nat 0)
        (H.cons H.nat (v.nat 2) (H.nil H.nat))));

  result = v.verify (H.listOf H.nat) (v.filter H.nat isZero input);
in
  result    # → [0 0]
```

## The verification spectrum

The architecture supports a spectrum of assurance levels. Each level
offers a different trade-off between verification strength and
implementation cost.

### Level 1: Contract

The baseline. Types check values at introduction via `.check` (which
calls `decide` under the hood). No HOAS, no proof terms — just write
normal Nix code and let the type system validate data at boundaries.

```nix
let
  inherit (fx.types) Int String refined;

  Port = refined "Port" Int (x: x >= 1 && x <= 65535);

  # Refinement with string guard — kernel checks String, guard checks membership
  LogLevel = refined "LogLevel" String
    (x: builtins.elem x [ "debug" "info" "warn" "error" ]);
in {
  ok    = Port.check 8080;       # true — decide says Int, guard says in range
  bad   = Port.check 99999;      # false — guard rejects (> 65535)
  wrong = Port.check "http";     # false — decide rejects (not Int)

  info  = LogLevel.check "info";    # true
  trace = LogLevel.check "trace";   # false — not in the allowed set

  # Effectful validation with blame context
  result = fx.run (Port.validate 99999)
    fx.effects.typecheck.collecting [];
  # result.state = [ { context = "Port"; message = "Expected Port, got int"; ... } ]
}
```

**Cost:** Zero — write normal Nix. The kernel runs behind the scenes.
Refinement types compose: `ListOf Port` checks that every element is
an integer in range. The kernel elaborates the list, the guard runs
per element.

### Level 2: Boundary

Data values are checked by the kernel at module interfaces. Types
carry `kernelType` and `.check` is derived from the kernel's `decide`
procedure. This is what every type does by default.

```nix
let
  inherit (fx.types) Bool Int String ListOf DepRecord refined;

  FIPSCipher = refined "FIPSCipher" String
    (x: builtins.elem x [ "AES-256-GCM" "AES-128-GCM" "AES-256-CBC" ]);

  # Dependent record: when fipsMode is true, cipherSuites must be FIPS-approved.
  # The kernel elaborates the record to a Sigma chain, checks each field's type
  # against its kernelType, and the guard on FIPSCipher validates membership.
  ServiceConfig = DepRecord [
    { name = "fipsMode"; type = Bool; }
    { name = "cipherSuites"; type = self:
        if self.fipsMode then ListOf FIPSCipher else ListOf String; }
  ];
in {
  ok  = ServiceConfig.checkFlat {
    fipsMode = true;
    cipherSuites = [ "AES-256-GCM" ];
  };   # true — kernel verifies each cipher is a valid FIPSCipher

  bad = ServiceConfig.checkFlat {
    fipsMode = true;
    cipherSuites = [ "3DES" ];
  };   # false — "3DES" fails the FIPSCipher guard

  lax = ServiceConfig.checkFlat {
    fipsMode = false;
    cipherSuites = [ "ChaCha20" "RC4" ];
  };   # true — non-FIPS mode accepts any string
}
```

**Cost:** Low — add `kernelType` to custom types (built-in types
already have it). The dependent record pattern shows how boundary
checking scales: the kernel handles structural verification, guards
handle domain predicates, and the dependency between fields is
resolved at check time.

### Level 3: Property

Universal properties verified via proof terms. Write proofs in HOAS
that the kernel checks. The proof term is separate from the
implementation — you write separate Nix code alongside, and the
kernel verifies that the stated property holds.

```nix
let
  H = fx.types.hoas;
  inherit (H) nat bool eq forall refl checkHoas;

  # Define addition by structural recursion on the first argument
  add = m: n:
    H.ind (H.lam "_" nat (_: nat)) n
      (H.lam "k" nat (_: H.lam "ih" nat (ih: H.succ ih))) m;

  not_ = b:
    H.boolElim (H.lam "_" bool (_: bool)) H.false_ H.true_ b;
in {
  # Prove: 3 + 5 = 8
  # The kernel normalizes add(3,5) via NatElim, arrives at 8,
  # and confirms Refl witnesses Eq(Nat, 8, 8).
  arithmetic = (checkHoas
    (eq nat (add (H.natLit 3) (H.natLit 5)) (H.natLit 8))
    refl).tag == "refl";

  # Prove: not(not(true)) = true
  # The kernel evaluates two BoolElim steps and confirms the result.
  doubleNeg = (checkHoas
    (eq bool (not_ (not_ H.true_)) H.true_)
    refl).tag == "refl";

  # Prove: append([1,2], [3]) = [1,2,3]
  # ListElim unfolds the first list, cons-ing each element onto [3].
  listAppend = let
    list12  = H.cons nat (H.natLit 1) (H.cons nat (H.natLit 2) (H.nil nat));
    list3   = H.cons nat (H.natLit 3) (H.nil nat);
    list123 = H.cons nat (H.natLit 1) (H.cons nat (H.natLit 2)
                (H.cons nat (H.natLit 3) (H.nil nat)));
    append = xs: ys:
      H.listElim nat (H.lam "_" (H.listOf nat) (_: H.listOf nat)) ys
        (H.lam "h" nat (h: H.lam "t" (H.listOf nat) (_:
          H.lam "ih" (H.listOf nat) (ih: H.cons nat h ih)))) xs;
  in (checkHoas (eq (H.listOf nat) (append list12 list3) list123) refl).tag == "refl";
}
```

**Cost:** Medium — write proofs in HOAS. The proofs are separate from
production code, so you can add them incrementally to an existing
codebase without rewriting anything.

### Level 4: Full

The implementation IS the proof term. Write the entire implementation
in HOAS, the kernel verifies it, and `extract` produces a Nix
function that is correct by construction. The extracted function is
plain Nix — no kernel overhead at call time.

```nix
let
  H = fx.types.hoas;
  v = fx.types.verified;

  RecTy = H.record [
    { name = "name";   type = H.string; }
    { name = "target"; type = H.string; }
  ];

  # Verified record validator: checks if two string fields match.
  # The kernel type-checks the implementation against its type
  # (Record → Bool), verifies that field projections are well-typed,
  # and confirms strEq composes correctly. Then extracts a Nix function.
  matchFn = v.verify (H.forall "r" RecTy (_: H.bool))
    (v.fn "r" RecTy (r:
      v.strEq (v.field RecTy "name" r) (v.field RecTy "target" r)));

  # Verified addition: structural recursion extracted as Nix function
  add = v.verify (H.forall "m" H.nat (_: H.forall "n" H.nat (_: H.nat)))
    (v.fn "m" H.nat (m: v.fn "n" H.nat (n:
      v.match H.nat m {
        zero = n;
        succ = _k: ih: H.succ ih;
      })));
in {
  sum   = add 2 3;    # → 5, correct by construction
  yes   = matchFn { name = "hello"; target = "hello"; };    # → true
  no    = matchFn { name = "hello"; target = "world"; };    # → false
}
```

**Cost:** High — write the implementation in HOAS. Best reserved for
security-critical code (firewall rules, certificate validation,
cross-field invariants) where the cost is justified by the assurance.
The `typed-derivation.nix` example illustrates the pattern with a
service builder where the kernel rejects invalid configurations via a
machine-checked proof before any derivation is attempted. (The example
itself is contrived — `assert` could do the same job. The interesting
direction is dependent module types where `assert` can't.) See the
[Proof Guide](proof-guide.md) for a progressive tutorial from simple
proofs through verified extraction to proof-gated derivations.

## How mkType derives .check

Every type is built by `mkType` (in `foundation.nix`). The kernel
type IS the type. `.check` is its decision procedure, derived
mechanically:

```
_kernel : HoasType        ← the type IS this
check : Value → Bool       ← derived from decide(kernelType, value)
kernelCheck : Value → Bool ← same as check (legacy alias)
prove : HoasTerm → Bool    ← kernel proof checking
universe : Int             ← computed from checkTypeLevel(kernelType)
```

For refinement types, an optional `guard` adds a runtime predicate
on top of the kernel check: `check = decide(kernelType, v) && guard(v)`.
The guard handles predicates the kernel cannot express — for example,
`x >= 0` for natural numbers, or membership in a finite set for
validated strings.

## Limitations

**Nix closures are opaque.** `decide(H.forall ..., f)` can only
check `builtins.isFunction f`. For full function verification, write
the function in HOAS and use `v.verify` to extract.

**Refinement predicates are opaque.** The kernel cannot represent
`x >= 0` as a type-level assertion. Refinement types always need a
hand-written guard predicate.

**`builtins.tryEval` is limited.** It only catches `throw` and
`assert false`. Cross-type comparison errors, boolean coercion errors,
and missing attribute access crash Nix uncatchably. This affects
`decide` for types whose elaboration might trigger such errors.

**Dependent extraction is limited.** Extracting a dependent Pi or
Sigma requires a sentinel test to detect non-dependence. If the
type family is truly dependent, extraction throws and requires
explicit type annotation.

**Opaque types cannot be extracted.** `Attrs`, `Path`, `Function`,
and `Any` are axiomatized — the kernel knows they exist but discards
their payloads. Extracting a value of these types throws. They work
for type-checking (deciding membership) but not for the full
verify-and-extract pipeline.

**Extraction has boundary cost.** Extracted functions elaborate their
arguments at every call (Nix → kernel value → apply → extract → Nix).
For hot paths, the contract layer's `.check` fast path is more
efficient.
