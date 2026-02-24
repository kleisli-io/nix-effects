# nix-effects

A type-checking kernel, algebraic effects, and dependent types in pure Nix.

nix-effects catches configuration errors at `nix eval` time — before
anything builds or ships. Every type is backed by an MLTT proof checker
that verifies values, computes universe levels, and extracts certified
Nix functions from proof terms. You get precise blame when something
violates a type.

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
The cipher list contract *depends on* the mode flag, making this a
dependent contract (`Σ(fipsMode:Bool).B(fipsMode)` checked at runtime):

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
[examples/typed-derivation.nix](examples/typed-derivation.nix) for the
complete example with handler, error formatting, and both derivations.

**[Documentation](https://docs.kleisli.io/nix-effects)**

## Quick start

Add nix-effects as a flake input:

```nix
{
  inputs.nix-effects.url = "github:kleisli-io/nix-effects";

  outputs = { nix-effects, ... }:
    let fx = nix-effects.lib;
    in {
      # Use fx.types, fx.run, fx.send, fx.bind ...
    };
}
```

Or import directly:

```nix
let fx = import ./path/to/nix-effects { lib = nixpkgs.lib; };
in ...
```

## Type system

Every type is grounded in an MLTT type-checking kernel. The guard (`check`)
is derived from the kernel's `decide` procedure. The verifier (`validate`)
sends `typeCheck` effects through the freer monad for blame tracking. You
choose the error policy by choosing the handler.

### Primitives

```nix
fx.types.String   fx.types.Int    fx.types.Bool
fx.types.Float    fx.types.Attrs  fx.types.Path
fx.types.Function fx.types.Null   fx.types.Unit  fx.types.Any
```

Each wraps a `builtins.is*` check:

```nix
fx.types.String.check "hello"  # true
fx.types.Int.check "hello"     # false
```

### Constructors

Build compound types from simpler ones:

```nix
# Record with typed fields (open — extra fields allowed)
PersonT = Record { name = String; age = Int; };
PersonT.check { name = "Alice"; age = 30; }  # true

# Homogeneous list
(ListOf Int).check [ 1 2 3 ]  # true

# Optional value
(Maybe String).check null     # true
(Maybe String).check "hello"  # true

# Tagged union (two branches)
(Either Int String).check { _tag = "Left"; value = 42; }   # true

# Tagged union (open)
(Variant { circle = Float; rect = Attrs; }).check { _tag = "circle"; value = 5.0; }  # true
```

`ListOf` sends per-element `typeCheck` effects with indexed context
(`List[Int][0]`, `List[Int][1]`, ...) so handlers report exactly which
element failed.

### Value-dependent contracts

Contract specifications whose predicates depend on runtime values,
structured after Martin-Löf's Pi and Sigma types (1984) and enforced
as higher-order contracts (Findler & Felleisen 2002).

```nix
# Sigma (Σ) — dependent pair: the second type depends on the first value
Sigma { fst = Bool; snd = b: if b then Int else String; }
# check { fst = true; snd = 42; }    → true
# check { fst = true; snd = "no"; }  → false

# Pi (Π) — dependent function: the return type depends on the argument
Pi { domain = String; codomain = _: Int; }
# Guards: isFunction. Full contract checked at elimination via .checkAt

# DepRecord — syntactic sugar over nested Sigma
DepRecord [
  { name = "mode"; type = Bool; }
  { name = "data"; type = self: if self.mode then Int else String; }
]

# Vector — length-indexed list (a Pi type: Nat → SizedList)
v3i = (Vector Int).apply 3;
v3i.check [ 1 2 3 ]  # true
v3i.check [ 1 2 ]    # false

# Certified — value paired with witness (predicate passed)
Certified { base = Int; predicate = x: x > 0; name = "Positive"; }
```

`Sigma.validate` decomposes checking recursively — per-element blame flows
through compound types (DepRecord → Sigma → ListOf → each element).

### Refinement types

Narrow any type with a predicate (Freeman & Pfenning 1991; cf. Rondon et al. 2008):

```nix
Nat = refined "Nat" Int (x: x >= 0);
Port = refined "Port" Int (x: x >= 1 && x <= 65535);
NonEmpty = refined "NonEmptyString" String (s: builtins.stringLength s > 0);

# Predicate combinators
refined "Safe" String (allOf [ (s: s != "") (s: !(builtins.elem s blocked)) ])
refined "Either" Int (anyOf [ (x: x < 0) (x: x > 100) ])
```

Built-in refinements: `positive`, `nonNegative`, `inRange`, `nonEmpty`, `matching`.

### Universe hierarchy

Types themselves have types, stratified to prevent accidental paradoxes
(universe levels are enforced by the kernel's `checkTypeLevel`; see [Known limitations](#known-limitations)):

```nix
Type_0  # Type of value types (Int, String, ...)
Type_1  # Type of Type_0
Type_2  # Type of Type_1
# ...up to Type_4

(typeAt 0).check Int   # true — Int lives at universe 0
level Int               # 0
```

## Effects

An effectful computation is a freer monad value: a tree of effects with
continuations. `send` creates an effect. `bind` sequences computations.
`run` interprets the tree through a handler.

```nix
# A computation that reads state, doubles it, writes it back
comp = bind get (s:
  bind (put (s * 2)) (_:
    pure s));

# Run with state handler
result = fx.run comp {
  get  = { param, state }: { resume = state; inherit state; };
  put  = { param, state }: { resume = null; state = param; };
} 21;

# result.value = 21, result.state = 42
```

### Same computation, different handler

Write the validation once. Swap the handler to change error policy.

```nix
packed = ServiceConfig.pack config;
validation = ServiceConfig.validate packed;

# Strict — abort on first error
strict = fx.run validation {
  typeCheck = { param, state }:
    if param.type.check param.value
    then { resume = true; inherit state; }
    else { abort = null; state = state ++ [ param.context ]; };
} [];

# Collecting — gather all errors, continue checking
collecting = fx.run validation {
  typeCheck = { param, state }:
    if param.type.check param.value
    then { resume = true; inherit state; }
    else { resume = false; state = state ++ [ param.context ]; };
} [];
```

The `resume` vs `abort` distinction: `resume` feeds a value back to the
continuation and keeps running. `abort` discards the continuation and
returns immediately. Handlers should return one of
`{ resume = value; state = ...; }` or `{ abort = value; state = ...; }`.
If both are present, `abort` takes priority.

### Built-in effects

| Module | Operations | Purpose |
|--------|-----------|---------|
| `state` | `get`, `put`, `modify`, `gets` | Mutable state |
| `error` | `raise`, `raiseWith` | Error handling |
| `reader` | `ask`, `asks`, `local` | Read-only environment |
| `writer` | `tell`, `tellAll` | Append-only log |
| `acc` | `emit`, `emitAll`, `collect` | Value accumulation |
| `choice` | `choose`, `fail`, `guard` | Nondeterminism |
| `conditions` | `signal`, `warn` | Common Lisp-style restarts |
| `typecheck` | *sent by `type.validate`* | Type validation with blame |
| `linear` | `acquire`, `consume`, `release` | Graded linear resource tracking |

## Streams

Effectful lazy sequences. Each step yields `Done` (finished) or `More`
(element + continuation):

```nix
# Generate, transform, consume
result = fx.run
  (fold (a: b: a + b) 0 (take 5 (map (x: x * x) (range 1 100))))
  {} null;
# result.value = 55 (1² + 2² + 3² + 4² + 5²)
```

Available: `fromList`, `iterate`, `range`, `replicate`, `map`, `filter`,
`scanl`, `take`, `takeWhile`, `drop`, `fold`, `toList`, `length`, `sum`,
`any`, `all`, `concat`, `interleave`, `zip`, `zipWith`.

## API reference

The `fx` attrset is the entire public API:

```
fx.pure         fx.impure       fx.send         fx.bind
fx.map          fx.seq
fx.run          fx.handle       fx.adapt        fx.adaptHandlers

fx.types.mkType     fx.types.check      fx.types.validate
fx.types.make       fx.types.refine

fx.types.String     fx.types.Int        fx.types.Bool       fx.types.Float
fx.types.Attrs      fx.types.Path       fx.types.Function   fx.types.Null
fx.types.Unit       fx.types.Any

fx.types.Record     fx.types.ListOf     fx.types.Maybe
fx.types.Either     fx.types.Variant

fx.types.Pi         fx.types.Sigma      fx.types.Certified
fx.types.Vector     fx.types.DepRecord

fx.types.Linear     fx.types.Affine     fx.types.Graded

fx.types.refined    fx.types.allOf      fx.types.anyOf      fx.types.negate
fx.types.positive   fx.types.nonNegative  fx.types.inRange
fx.types.nonEmpty   fx.types.matching

fx.types.typeAt     fx.types.level
fx.types.Type_0 .. fx.types.Type_4

fx.effects.get      fx.effects.put      fx.effects.modify   fx.effects.gets
fx.effects.state    fx.effects.error    fx.effects.typecheck
fx.effects.conditions  fx.effects.reader  fx.effects.writer
fx.effects.acc      fx.effects.choice
fx.effects.linear

fx.stream.done      fx.stream.more      fx.stream.fromList
fx.stream.iterate   fx.stream.range     fx.stream.replicate
fx.stream.map       fx.stream.filter    fx.stream.scanl
fx.stream.take      fx.stream.takeWhile fx.stream.drop
fx.stream.fold      fx.stream.toList    fx.stream.length
fx.stream.sum       fx.stream.any       fx.stream.all
fx.stream.concat    fx.stream.interleave  fx.stream.zip  fx.stream.zipWith

fx.tc.term          fx.tc.value         fx.tc.eval      fx.tc.quote
fx.tc.conv          fx.tc.check         fx.tc.hoas      fx.tc.elaborate
fx.tc.verified

fx.kernel.pure      fx.kernel.send      fx.kernel.bind
fx.trampoline.handle
```

Types additionally expose:

```
T.check v          -- decide via kernel (elaborate + type-check)
T.prove term       -- verify a HOAS proof term against the kernel type
T._kernel          -- the kernel type (HOAS tree)
```

## How it works

Computations are freer monad values: `Pure value` or `Impure effect continuation`.
`bind` appends to an `FTCQueue` (catenable queue) in O(1).
The interpreter uses `builtins.genericClosure` — Nix's only iterative
primitive — as a trampoline, giving O(1) stack depth for the main
dispatch loop. Each step calls the handler for the current effect,
feeds the result to the continuation queue, and produces the next node.
`deepSeq` on the handler state in the `key` field breaks thunk chains
that would otherwise blow memory. Test suite validates 100,000 operations;
manual runs confirm 1,000,000 operations in ~3 seconds with constant memory.

## Known limitations

**Kernel is the single source of truth.** Every `.check` call runs through
the kernel's `decide` procedure — there is no separate contract system.
The MLTT type-checking kernel (`src/tc/`) provides bidirectional type
checking with normalization by evaluation (NbE), proof terms, and formal
verification for universally quantified properties. The `Certified`
type's witness is a boolean, not an inhabitation proof — kernel proofs
use HOAS combinators from `fx.tc.hoas`. See Findler & Felleisen (2002)
for the contract-theoretic framing and Dunfield & Krishnaswami (2021)
for the bidirectional checking approach.

**Universe levels are partially enforced.** For kernel-backed types,
`checkTypeLevel` computes the correct universe level from the typing derivation.
For non-kernel types, the `universe` field remains a trusted declaration
— nothing prevents a user from declaring `universe = 0` on a type that
operates at a higher level. Computing `sup_{a:A} level(B(a))` for
arbitrary type families requires evaluating on all domain values, which
is undecidable. The hierarchy prevents accidental paradoxes; the kernel
enforces it for types it knows about.

**Effects are string-keyed, not extensible.** Kiselyov & Ishii (2015)
contributes both the freer monad encoding with FTCQueue and extensible effects
via open unions. nix-effects implements the first but not the second. Effect
handlers go into a single flat attrset per `run` call; name collisions are
silently accepted (last handler wins via attrset merge).

**No handler layering.** Each `run` call takes one handler set.
Nested `run` calls are possible but there is no automatic effect
forwarding to outer handlers. The `adapt` combinator addresses state
shape composition, not effect isolation.

**O(1) stack depth caveat.** The trampoline gives O(1) stack for the main
dispatch loop. Both `qApp` (continuation application) and `viewlGo` (queue
rotation) are trampolined via `builtins.genericClosure`, so chains of
10,000+ pure binds and deep left-nested queues are handled iteratively.
The remaining stack risk is in user-supplied handler functions that recurse
deeply within a single trampoline step.

**Handler state must be deepSeq-safe.** The trampoline uses
`builtins.deepSeq` on handler state at each step to break thunk chains.
This means handler state must not contain functions (closures), since
`deepSeq` on a function is a no-op in Nix -- thunks captured inside
closures survive the eager evaluation and can accumulate. All built-in
handlers use scalar or flat-attrset state (safe). Custom handlers with
closure-valued state may lose the thunk-breaking guarantee.

## Testing

```bash
# Run all tests via nix-unit
nix flake check

# Evaluate test results directly
nix eval --impure --expr \
  'let fx = import ./. { lib = (builtins.getFlake "nixpkgs").lib; };
   in fx.tests.allPass'
# => true
```

Tests cover algebraic laws (functor, monad), all type constructors
including dependent and linear types, the trampoline at 100k operations,
error paths, streams, and the typed derivation showcase.

## Formal foundations

Key papers that shaped the design:

- **Martin-Löf (1984)** *Intuitionistic Type Theory*. Pi, Sigma, universe
  hierarchy. nix-effects implements these in an MLTT type-checking kernel
  (`src/tc/`) — all types are grounded in the kernel, which operates at
  `nix eval` time.

- **Findler & Felleisen (2002)** *Contracts for Higher-Order Functions*.
  The guard/verifier decomposition follows their strategy: first-order
  types check immediately, higher-order types (Pi) defer to elimination.

- **Freeman & Pfenning (1991)** *Refinement Types for ML*. The concept of
  narrowing a type with a predicate. nix-effects' `refined` constructor
  and predicate combinators implement runtime refinement checking.
  Rondon, Kawaguchi & Jhala (2008) extended this with SMT-based inference
  (*Liquid Types*); nix-effects uses predicates rather than SMT solvers.

- **Plotkin & Pretnar (2009)** *Handlers of Algebraic Effects*. The
  handler pattern. `resume` invokes the continuation, `abort` discards it.

- **Kiselyov & Ishii (2015)** *Freer Monads, More Extensible Effects*.
  The freer monad encoding and `FTCQueue` (catenable queue)
  that give O(1) bind and make effectful validation practical at scale.
  nix-effects uses the freer encoding and FTCQueue but does not implement
  the paper's extensible effects (open unions, Member constraint).

- **Orchard, Liepelt & Eades (2019)** *Quantitative Program Reasoning with
  Graded Modal Types*. The graded linear type model. nix-effects' `Linear`,
  `Affine`, and `Graded` types implement resource-usage tracking following
  this quantitative framework.

- **Pédrot & Tabareau (2020)** *The Fire Triangle*. Their no-go theorem
  proves that substitution, dependent elimination, and observable effects
  can't coexist in a consistent type theory. Nix eval is pure — no
  observable effects in their sense — so the theorem doesn't directly
  apply. But it validates the design: keeping types as pure values means
  dependent contracts like DepRecord avoid the coherence problems the
  theorem identifies. See the [theory chapter](https://docs.kleisli.io/nix-effects/theory.html)
  for the full argument.

## Acknowledgments

[nfx](https://github.com/vic/nfx) by Victor Borja (Apache-2.0) shaped the
API design of this project. The `adapt` handler combinator, the
`mk { doc, value, tests }` structured module pattern, and the effect module
vocabulary (`state`, `acc`, `conditions`, `choice`, streams) all come from
nfx. nix-effects builds a different core on freer monads with FTCQueue
(Kiselyov & Ishii 2015) and adds a value-dependent contract system that
nfx does not attempt, but the overall API owes a clear debt to that project.

## License

[MIT](LICENSE)
