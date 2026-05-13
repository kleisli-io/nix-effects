# nix-effects

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
[![CI](https://github.com/kleisli-io/nix-effects/actions/workflows/flake-check.yml/badge.svg)](https://github.com/kleisli-io/nix-effects/actions/workflows/flake-check.yml)
[![Release](https://img.shields.io/github/v/release/kleisli-io/nix-effects)](https://github.com/kleisli-io/nix-effects/releases)

A pure Nix toolkit for effectful programs, typed validation, verified
boundaries, and description-backed DSLs.

Programs describe what they need. Handlers decide policy. Types,
datatypes, and proofs describe the structure that generic tools can
validate, interpret, extract, or document.

Everything runs at `nix eval` time.

**[Documentation](https://docs.kleisli.io/nix-effects)**

## Small example

Validation is a `typeCheck` effect. A validator walks a nested record
and sends `typeCheck` at every leaf; the handler decides what happens
on failure:

```nix
# src/effects/typecheck.nix — three handlers for the same effect.

strict = {
  typeCheck = { param, state }:
    if param.type.check param.value
    then { resume = true; inherit state; }
    else builtins.throw
      "Type error in ${param.context}: expected ${param.type.name}, got ${builtins.typeOf param.value}";
};

collecting = {
  typeCheck = { param, state }:
    if param.type.check param.value
    then { resume = true; inherit state; }
    else {
      resume = false;
      state = state ++ [{
        context = param.context;
        typeName = param.type.name;
        actual = builtins.typeOf param.value;
        message = "Expected ${param.type.name}, got ${builtins.typeOf param.value}";
      }];
    };
};

logging = {
  typeCheck = { param, state }:
    let passed = param.type.check param.value;
    in { resume = passed;
         state = state ++ [{
           context = param.context;
           typeName = param.type.name;
           inherit passed;
         }]; };
};
```

The same validator runs under all three without a rewrite. `strict`
throws on the first bad field. `collecting` visits every leaf and
returns the failures with their `context` paths. `logging` records
every check, pass or fail — how you debug a validator that rejects a
value you thought it should accept.

The dependent type checker in `src/tc/` is ordinary pure Nix — no
`fx.*` calls — but `.validate` routes through `typeCheck`, so type
errors in deeply nested terms come back with the field path that
broke.

Recursion in the kernel and the effect interpreter goes through a
trampoline built on `builtins.genericClosure` (Nix's only iterative
primitive). Call stack stays O(1) for the interpreter loop. See
[`book/src/trampoline.md`](book/src/trampoline.md).

## Table of contents

- [Small example](#small-example)
- [What you can build](#what-you-can-build)
- [Core concepts](#core-concepts)
- [Quick start](#quick-start)
- [Effects](#effects)
- [Typed boundaries](#typed-boundaries)
- [Datatypes and descriptions](#datatypes-and-descriptions)
- [Streams and pipelines](#streams-and-pipelines)
- [Syntax sugar](#syntax-sugar)
- [API reference](#api-reference)
- [How it works](#how-it-works)
- [Known limitations](#known-limitations)
- [Testing](#testing)
- [Documentation MCP server](#documentation-mcp-server)
- [Formal foundations](#formal-foundations)
- [Used by](#used-by)
- [Acknowledgments](#acknowledgments)
- [License](#license)

## What you can build

- **Typed validators.** Validate nested Nix values with exact blame paths
  and choose fail-fast, collecting, or logging policy with handlers.
- **Effectful pipelines.** Model eval-time workflows with state, errors,
  scoped context, accumulation, nondeterminism, restarts, and streams.
- **Description-backed DSLs.** Define domain shapes once, then interpret
  them as derivations, descriptors, documentation, schemas, tests, graphs,
  or dashboards.
- **Verified boundaries.** Check proofs or implementations against kernel
  types before extracting ordinary Nix functions.
- **Generic datatype tooling.** Write consumers over datatype descriptions
  instead of repeating per-type traversal and validation code.

## Core concepts

- **Computations** are freer-monad values. `pure` returns a value, `send`
  requests an effect, `bind` sequences work, and `run` interprets the tree.
- **Handlers** own operational policy. The same computation can abort,
  resume, collect errors, hide scoped state, or route unknown effects
  outward depending on the handler.
- **Typed boundaries** connect runtime Nix values to the MLTT kernel.
  Guards decide simple cases, validators emit `typeCheck` effects with
  blame context, and verified HOAS terms can be extracted as plain Nix.
- **Descriptions** are reusable datatype shapes. The public inductive
  prelude and user datatypes share the same description-backed macro
  surface, so generic tools can inspect and consume datatype structure.
- **Streams and pipelines** are effectful programs too. They compose with
  the same `bind`, handler, and trampoline machinery as validation.

### Examples in this repository

- **Category theory library** (`apps/category-theory/`) shows proofs,
  arithmetic, algebraic structures, functors, and Yoneda through the HOAS
  and datatype surface.
- **Expression interpreter and build simulator** (`apps/interp/`,
  `apps/build-sim/`) exercise the effect layer at scale.

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

Or import directly (non-flake):

```nix
let
  pkgs = import <nixpkgs> {};
  fx = import ./path/to/nix-effects { lib = pkgs.lib; };
in ...
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
| `scope` | `run`, `runWith`, `stateful`, `provide`, `val` | Scoped handlers |
| `hasHandler` | `hasHandler` | Runtime handler presence check |

## Typed boundaries

Every type is grounded in an MLTT type-checking kernel. The guard (`check`)
is derived from the kernel's `decide` procedure. The verifier (`validate`)
sends `typeCheck` effects through the freer monad for blame tracking. You
choose the error policy by choosing the handler.

### First-order types

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
element failed. `Record` sends per-field effects (`Record{age, name}.age`)
and delegates to each field type's `.validate`, so nested Records and
ListOf fields decompose recursively. `Variant` delegates to the active
branch's `.validate`.

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

### Dependent and proof terms

`Pi` encodes dependent functions, `Sigma` dependent pairs, and `DepRecord`
dependent records. Identity types expose `Refl` and `J`; `sym`, `trans`,
`cong`, and `transport` are derived from `J`.

`fx.types.hoas` builds proof terms. `fx.types.extract` and
`verifyAndExtract` check a HOAS body at the boundary and return an ordinary
Nix callable when verification succeeds.

### Universe levels

Types themselves have types, stratified to prevent accidental paradoxes.
The kernel is non-cumulative: moving data across universe levels is explicit
via `LiftAt`, `liftAt`, and `lowerAt`:

```nix
Type_0  # Type of value types (Int, String, ...)
Type_1  # Type of Type_0
Type_2  # Type of Type_1
# typeAt n works for any n; Type_0 through Type_4 are convenience aliases.
# 4 is arbitrary — for NixOS configuration you'll rarely need more than Type_1.

(typeAt 0).check Int    # true — Int lives at universe 0
level Int               # 0
```

For kernel-backed types, levels are computed from the typing derivation.
Transport across levels is represented in the term language instead of hidden
behind cumulative subtyping.

### Usage-checked values

`Linear`, `Affine`, and `Graded` types track resource usage with exact,
bounded, or graded counts.

## Datatypes and descriptions

Descriptions are reusable datatype shapes. `Desc` and `μ` provide the
generic induction boundary; the public inductive prelude (`Nat`, `List`,
`Sum`, `Bool`, `Eq`, `Fin`, `Vec`, `W`) and user-defined datatypes share
the same description-backed macro surface.

The datatype macro lets you declare single- or multi-constructor datatypes
directly in HOAS with `datatype`, `datatypeP`, `datatypeI`, `datatypePI`,
`conI`, `field`, `fieldD`, `piField`, `piFieldD`, `recField`, and
`recFieldAt`. Dependent fields see prior fields by name (`prev.op`,
`prev.comp`), parameters thread through a `paramPi` binder, and indexed
families can compute their target index.

Chains of saturated or linear-recursive constructors flatten to flat
`desc-con` terms at elaboration time, so deeply nested generated lists and
natural numbers remain stack-safe.

The category theory library in [`apps/category-theory/`](apps/category-theory/)
uses the same surface for arithmetic proofs, algebraic structures, functors,
and Yoneda's lemma.

## Streams and pipelines

Effectful lazy sequences. Each step yields `Done` (finished) or `More`
(element + continuation):

```nix
# Generate, transform, consume
result = fx.run
  (fold (a: b: a + b) 0 (take 5 (map (x: x * x) (range 1 100))))
  {} null;
# result.value = 55 (1² + 2² + 3² + 4² + 5²)
```

Available: `fromList`, `iterate`, `range`, `replicate`, `map`, `flatMap`,
`filter`, `scanl`, `take`, `takeWhile`, `drop`, `fold`, `toList`, `length`,
`sum`, `signal`, `signalOn`, `any`, `all`, `concat`, `interleave`, `zip`,
`zipWith`.

## Syntax sugar

`fx.sugar` is an opt-in syntax layer. `do` and `letM` replace nested
`bind` chains; `__div` (behind `fx.sugar.operators`) lets you write
`a / f / g` for left-associative bind pipelines; `fx.sugar.types`
pre-wraps the zero-ary primitives with a `__functor` that applies a
predicate via `fx.types.refined`. The kernel doesn't import any of it.
See [`book/src/sugar.md`](book/src/sugar.md) for usage forms, caveats,
and forward-compatibility notes.

## API reference

The `fx` attrset is the entire public API:

```
fx.pure         fx.impure       fx.isPure       fx.isComp      fx.match
fx.send         fx.bind         fx.map          fx.seq
fx.pipe         fx.kleisli
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
fx.types.Type_0 .. fx.types.Type_4      # convenience aliases; typeAt n works for any n

fx.effects.get      fx.effects.put      fx.effects.modify   fx.effects.gets
fx.effects.state    fx.effects.error    fx.effects.typecheck
fx.effects.conditions  fx.effects.reader  fx.effects.writer
fx.effects.acc      fx.effects.choice
fx.effects.linear   fx.effects.scope     fx.effects.hasHandler

fx.stream.done      fx.stream.more      fx.stream.fromList
fx.stream.iterate   fx.stream.range     fx.stream.replicate
fx.stream.map       fx.stream.flatMap   fx.stream.filter    fx.stream.scanl
fx.stream.take      fx.stream.takeWhile fx.stream.drop
fx.stream.fold      fx.stream.toList    fx.stream.length
fx.stream.sum       fx.stream.signal    fx.stream.signalOn
fx.stream.any       fx.stream.all
fx.stream.concat    fx.stream.interleave  fx.stream.zip  fx.stream.zipWith

fx.types.hoas                           fx.types.verified
fx.types.elaborateType                  fx.types.elaborateValue
fx.types.extract                        fx.types.verifyAndExtract
fx.types.decide                         fx.types.decideType

fx.kernel.pure      fx.kernel.send      fx.kernel.bind
fx.kernel.pipe      fx.kernel.kleisli
fx.trampoline.handle

fx.sugar.do         fx.sugar.letM
fx.sugar.operators.__div
fx.sugar.types.wrap
fx.sugar.types.Int  fx.sugar.types.String  fx.sugar.types.Bool
fx.sugar.types.Float  fx.sugar.types.Path  fx.sugar.types.Null
fx.sugar.types.Unit  fx.sugar.types.Any
```

Types additionally expose:

```
T.check v          -- decide via kernel (elaborate + type-check)
T.prove term       -- verify a HOAS proof term against the kernel type
T._kernel          -- the kernel type (HOAS tree)
```

## How it works

Computations are freer monad values: `Pure value` or `Impure effect continuation`,
constructed via `comp.pure` and `comp.impure` (the `comp` module is the single
source of truth for the Computation ADT). `bind` appends to an `FTCQueue`
(catenable queue) in O(1). `send` uses an `Identity` queue sentinel so the
trampoline can skip the identity continuation application entirely.

The interpreter uses `builtins.genericClosure` — Nix's only iterative
primitive — as a trampoline, giving O(1) stack depth for the main
dispatch loop. Each step calls the handler for the current effect, processes
the continuation queue inline via recursive `applyQueue`, and produces the
next computation node — one genericClosure step per effect.
`deepSeq` on the handler state in the `key` field breaks thunk chains
that would otherwise blow memory. Test suite validates 100,000 operations;
deep pure bind chains use the iterative queue path.

## Known limitations

**`Certified` carries a boolean witness, not an inhabitation proof.**
`Certified(A, P) = Σ(v:A).{p : Bool | p ∧ P(v)}` stores the boolean
result of `P(v)` as its second component rather than a term inhabiting
`P(v)`. Predicate evaluation happens at construction time and produces
no transportable proof term. For genuinely propositional content, use
`Pi` with identity types and the `J`-derived combinators (`sym`,
`trans`, `cong`, `transport`) from `fx.types.hoas`.

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

**O(1) stack depth caveat.** The trampoline gives O(1) stack for the main
dispatch loop. Continuation queue application is inlined as a recursive
function (depth-limited to 500) with a `genericClosure` fallback for deep
pure chains, so chains of 10,000+ pure binds are handled iteratively.
Queue rotation (`viewlGo`) uses `genericClosure` for deep left-nested
trees. The remaining stack risk is in user-supplied handler functions
that recurse deeply within a single trampoline step.

**Handler state must be deepSeq-safe.** The trampoline uses
`builtins.deepSeq` on handler state at each step to break thunk chains.
This means handler state must not contain functions (closures), since
`deepSeq` on a function is a no-op in Nix -- thunks captured inside
closures survive the eager evaluation and can accumulate. All built-in
handlers use scalar or flat-attrset state (safe). Custom handlers with
closure-valued state may lose the thunk-breaking guarantee.

## Testing

```bash
# Run all tests via nix-unit (flake)
nix flake check

# Run all tests via nix-unit (non-flake)
nix-unit ./tests.nix

# Evaluate test results directly
nix eval --impure --expr \
  'let fx = import ./. { lib = (builtins.getFlake "nixpkgs").lib; };
   in fx.tests.allPass'
# => true
```

Tests cover algebraic laws (functor, monad), all type constructors
including dependent and linear types, the trampoline at 100k operations,
error paths, streams, and HOAS proof verification.

## Documentation MCP server

The full nix-effects manual is published at `https://docs.kleisli.io/nix-effects`,
and an MCP (Model Context Protocol) server lets AI agents search and fetch it
programmatically.

- **Explainer:** `https://docs.kleisli.io/mcp` (human-readable; lists tools, resources, and copy-pasteable client configs).
- **Transport endpoint:** `https://docs.kleisli.io/mcp/transport` (Streamable HTTP per spec 2025-03-26 — POST/GET/DELETE).
- **Tools:** `search_docs(query)`, `get_page(project, section, page)`, `list_projects()`.
- **Resources:** `docs://kleisli/{project}/{section}/{page}`.

Diag hints (`fx.diag.hints.hints`) carry a `docLink` field pointing at a
per-key heading anchor on the diag module page, so AI tooling that
surfaces hints can deep-link directly to the relevant prose.

### Markdown affordances

Every doc page is also available as raw Markdown — useful for token-efficient
agent consumption:

- Append `.md` to any path: `…/nix-effects.md`, `…/nix-effects/core-api.md`, `…/nix-effects/core-api/diag.md`.
- Or send `Accept: text/markdown` on the original path; the server returns `Content-Type: text/markdown` instead of HTML.
- Doc pages emit a `Link: <{path}.md>; rel="llms-txt-page"` response header pointing at the markdown alternate.

### Connecting from Claude Code

Add the server to `~/.claude/mcp.json` (or per-project `.claude/mcp.json`):

```json
{
  "mcpServers": {
    "kleisli-docs": {
      "type": "http",
      "url": "https://docs.kleisli.io/mcp/transport"
    }
  }
}
```

Tools then surface as `mcp__kleisli-docs__search_docs`,
`mcp__kleisli-docs__get_page`, `mcp__kleisli-docs__list_projects`.

For Cursor and generic JSON-RPC client configs, see
`https://docs.kleisli.io/mcp`.

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

## Used by

Projects that import nix-effects as a dependency. If your project uses
nix-effects and you'd like it listed here, open a PR.

- **[den](https://github.com/denful/den)** by [@vic](https://github.com/vic) —
  an aspect-oriented Nix configuration framework. Den [uses nix-effects at its core](https://den.denful.dev/explanation/effects) to achieve dependency injection via effect-rotation and scoped-handlers. Den configuration pipeline uses effect-handlers for keeping module-provenance and dedup, dependency-tracing, fleet-graphs, custom Nix classes forwarding, cross-host or cross-aspect configurations, and other advanced features.

- **[ned](https://github.com/denful/ned)** by [@vic](https://github.com/vic)  —
  Ned is a minimalist kernel built upon nix-effects to bring effectful stream-based Functional-Reactive-Programming into Nix. Ned was born from the experience and knowledge obtained while using nix-effects in Den. Ned is being used to simplify Den's internal subsystems communication and effect-protocols by using cycle-like composition while keeping effects drive state and events.


## Acknowledgments

[nfx](https://github.com/vic/nfx) by [Victor Borja](https://github.com/vic) (Apache-2.0) shaped the API
design of this project. The `adapt` handler combinator, the `mk { doc, value,
tests }` structured module pattern, and the effect module vocabulary (`state`,
`acc`, `conditions`, `choice`, streams) all come from nfx. nix-effects builds a
different core on freer monads with FTCQueue (Kiselyov & Ishii 2015) and adds a
type-checking kernel and dependent type system that nfx does not attempt, but
the overall API owes a clear debt to that project.

## License

[MIT](LICENSE)
