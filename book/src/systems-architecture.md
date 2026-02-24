# Systems Architecture

nix-effects grounds all types in a small, trusted type-checking kernel
— a Lean-light MLTT core running entirely at `nix eval` time, built on
the effects infrastructure.

The kernel is implemented in `src/tc/` (~2200 lines) and fully integrated.
All types have kernel backing — `.check` is derived mechanically from
the kernel's `decide` procedure. There is no separate contract system
and no adequacy bridge. Universe levels are computed by the kernel's
`checkTypeLevel`. One notion of type, one checking mechanism, with
decidable checking as a derived operation.

## Foundation layers

nix-effects has two foundation layers:

**The effects kernel.** Freer monad with FTCQueue for O(1) bind.
`builtins.genericClosure` trampoline for O(1) stack depth. Handler-swap
pattern for configurable interpretation. This layer is solid — tested at
1,000,000 operations, constant memory, ~3 seconds.

**The type-checking kernel.** Every type is defined by its kernel
representation — an HOAS type tree that the MLTT kernel can check.
`.check` is derived mechanically from the kernel's `decide` procedure.
`.validate` sends `typeCheck` effects through the freer monad for blame
tracking. You choose the error policy by choosing the handler.

For first-order types, the kernel's decision procedure is the full check.
But it has an inherent limitation for higher-order types: `Pi.check`
can only verify `isFunction` — it can't verify that a function maps
every A-value to a B-value. Decision procedures are decidable and total,
which makes them practical, but they can only state properties about the
values in front of them.

"For ALL services in this configuration, if they listen on a port, a
firewall rule exists" — that's a universally quantified statement. No
decision procedure can check it. You need structural verification of a
proof term, not evaluation of a predicate.

An earlier design considered separating decision procedures from the
kernel, with an adequacy bridge connecting two separate notions of type.
That architecture was rejected. If a kernel exists, the type system
should be grounded in it from the start.

## The kernel-first architecture

Instead of two systems with a bridge:

```
Contracts (ad hoc)          Proofs (kernel)
  Record, ListOf, Pi...       Pi, Sigma, Nat, eq...
       \                        /
        \   adequacy bridge    /
         \                    /
          \                  /
           \                /
            v              v
             Effects kernel

```

One system, one source of truth:

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

There is no adequacy gap to bridge. Contracts don't exist as a
separate concept — they're the decidable fragment of kernel type
checking, optimized with proven-correct fast paths.

## The trusted kernel

The kernel is small and auditable. It implements a core dependent type
theory — something in the neighborhood of MLTT with natural numbers,
identity types, and a cumulative universe hierarchy.

### Core judgments

The kernel checks four judgments:

```
ctx ⊢ term : type       (type checking)
ctx ⊢ term ⇒ type       (type inference)
type_a ≡ type_b         (definitional equality, via normalization)
⊢ ctx ok                (context well-formedness)

```

### The term language

Terms are Nix attrsets. Each has a `tag` field for the constructor:

```nix
# Core constructors (see kernel-spec.md §2 for the full grammar)
{ tag = "var"; idx = 0; }                     # de Bruijn index
{ tag = "pi"; name = "x"; domain = ...; codomain = ...; }  # Π type
{ tag = "lam"; name = "x"; domain = ...; body = ...; }     # λ abstraction
{ tag = "app"; fn = ...; arg = ...; }         # application
{ tag = "sigma"; name = "x"; fst = ...; snd = ...; }       # Σ type
{ tag = "pair"; fst = ...; snd = ...; type = ...; }         # pair
{ tag = "fst"; pair = ...; }                  # first projection
{ tag = "snd"; pair = ...; }                  # second projection
{ tag = "nat"; }                              # ℕ
{ tag = "zero"; }                             # 0
{ tag = "succ"; pred = ...; }                 # S(n)
{ tag = "bool"; } { tag = "true"; } { tag = "false"; }    # 𝔹
{ tag = "list"; elem = ...; }                 # List A
{ tag = "nil"; elem = ...; } { tag = "cons"; elem = ...; head = ...; tail = ...; }
{ tag = "unit"; } { tag = "tt"; }             # ⊤
{ tag = "void"; } { tag = "absurd"; type = ...; term = ...; }  # ⊥
{ tag = "sum"; left = ...; right = ...; }     # A + B
{ tag = "inl"; left = ...; right = ...; term = ...; }
{ tag = "inr"; left = ...; right = ...; term = ...; }
{ tag = "eq"; type = ...; lhs = ...; rhs = ...; }   # Id type
{ tag = "refl"; }                                     # reflexivity
{ tag = "j"; type = ...; lhs = ...; motive = ...; base = ...; rhs = ...; eq = ...; }
{ tag = "U"; level = 0; }                    # universe
{ tag = "ann"; term = ...; type = ...; }     # annotation
{ tag = "let"; name = "x"; type = ...; val = ...; body = ...; }  # let
# Eliminators: nat-elim, bool-elim, list-elim, sum-elim

```

We use de Bruijn indices internally. The surface language uses names
(see "Making the syntax livable" below). A small elaborator translates
named terms to de Bruijn core terms.

### The core operations (Normalization by Evaluation)

The kernel uses **NbE** (Normalization by Evaluation) rather than
explicit substitution. Terms (Tm) are interpreted into a semantic
domain (Val) by `eval`, and read back to normal forms by `quote`.
This avoids the quadratic cost of explicit substitution.

**Evaluation** (`eval : Env × Tm → Val`). Interprets a term in an
environment of values, performing beta and iota reductions eagerly.
Closures `(env, body)` capture the environment, avoiding substitution.
Trampolined via `genericClosure` for recursive eliminators (NatElim,
ListElim) to guarantee O(1) stack depth.

**Quotation** (`quote : ℕ × Val → Tm`). Converts a value back to
a term, translating de Bruijn levels to indices. Trampolined for
deep VSucc/VCons chains.

**Conversion** (`conv : ℕ × Val × Val → Bool`). Checks definitional
equality of two values. Purely structural on normalized values — no
type information used. No eta expansion. Trampolined for deep
VSucc and VCons chains.

**Bidirectional type checking** (`check`/`infer`). Inference mode
synthesizes a type from a term; checking mode verifies a term against
an expected type. Switching between modes happens at annotations and
eliminators. The algorithm follows Dunfield & Krishnaswami (2021).
Type errors are reported via effects; the handler determines policy.

### Why the trampoline is essential

Normalization of proof terms is iterative. A proof by induction on a
natural number n unfolds n reduction steps. A naive recursive normalizer
blows the stack for large proofs.

The `builtins.genericClosure` trampoline that nix-effects already uses
for effect interpretation handles this identically:

```nix
normalize = term:
  let
    steps = builtins.genericClosure {
      startSet = [{ key = 0; _term = term; }];
      operator = step:
        let next = whnfStep step._term;
        in if next.done then []
           else [{ key = builtins.deepSeq next.term (step.key + 1);
                   _term = next.term; }];
    };
  in (lib.last steps)._term;

```

O(1) stack depth. `deepSeq` breaks thunk chains. The same technique that
lets nix-effects run 1,000,000 effect operations lets the kernel
normalize complex proof terms without hitting Nix's stack limit.

### Why the FTCQueue matters

During type checking, the checker processes a sequence of obligations:
check this argument, then check that body, then verify this equality.
These are continuations — "after you finish checking A, check B with
the result."

The FTCQueue (catenable queue) from Kiselyov & Ishii gives O(1)
continuation chaining. Without it, a deeply nested proof term with
1000 nested applications would produce O(n^2) overhead from left-nested
bind chains in the checker's own computation. With it: O(n) total.

## The checker as an effectful computation

The checker itself is a nix-effects computation. Its operations are
effects:

```nix
# Core effects of the type-checking kernel
check = ctx: term: type: send "check" { inherit ctx term type; };
infer = ctx: term: send "infer" { inherit ctx term; };
unify = a: b: send "unify" { inherit a b; };
freshLevel = send "freshLevel" null;
typeError = msg: send "typeError" msg;

```

The handler determines checking behavior:

```nix
# Strict: abort on first error
strictChecker = {
  typeError = { param, state }:
    { abort = null; state = state ++ [param]; };
  ...
};

# Collecting: gather all errors
collectingChecker = {
  typeError = { param, state }:
    { resume = null; state = state ++ [param]; };
  ...
};

# Interactive: yield on error for tactic guidance
interactiveChecker = {
  typeError = { param, state }:
    { resume = null; state = state // { paused = param; }; };
  ...
};

```

Same handler-swap pattern that the current `ServiceConfig.validate`
uses. Same trampoline running the computation. The kernel is just
another effectful program running on the effects infrastructure.

## Types grounded in the kernel

This is where the kernel-first approach differs from adding a proof
checker alongside ad hoc contracts. Every type in the public API compiles
to a kernel construction. A type IS its kernel representation, and all
operations are derived from it.

### Elaboration: Nix values to kernel terms

When you check a value against a type, elaboration translates the Nix
value into a kernel term, and the kernel checks it:

```nix
# Nat.check 42
# Elaboration: 42 → succ^42(zero)
# Kernel: ⊢ succ(succ(...(zero)...)) : Nat  ✓

# (ListOf Nat).check [1, 2, 3]
# Elaboration: [1,2,3] → cons(succ(zero), cons(succ(succ(zero)), cons(succ(succ(succ(zero))), nil)))
# Kernel: ⊢ cons(1, cons(2, cons(3, nil))) : List Nat  ✓

```

### Decidable fast paths

Elaborating `42` to `succ^42(zero)` and checking structurally is
correct but expensive. For decidable properties — which is everything
the decision procedure handles — we derive a fast path from the kernel
type definition.

The kernel defines `Nat` as an inductive type with `zero` and `succ`.
From that definition, a decision procedure is mechanically derived:

```nix
# Decision procedure derived from kernel Nat definition
Nat.check = v: builtins.isInt v && v >= 0;

```

This is the same predicate the surface API exposes. It's justified by
the kernel, not ad hoc. You prove once (by structural induction on the
derivation rules) that the decision procedure agrees with the kernel
type. Then you use the fast predicate at eval time and fall back to the
kernel for properties the predicate can't express.

This is how Lean handles `Decidable` instances. For decidable
propositions, evaluation IS proof. The decision procedure is the
computational content of the decidability proof, extracted as a
function.

### How current types map to kernel types

| Current API | Kernel construction | Fast path |
|------------|-------------------|-----------|
| `Nat` | Inductive type (zero, succ) | `isInt v && v >= 0` |
| `String` | Primitive (axiom) | `builtins.isString v` |
| `ListOf A` | Inductive type (nil, cons A) | `builtins.isList v && all A.check v` |
| `Record { a = A; b = B }` | Sigma (a : A) (b : B) | Field-wise guard |
| `DepRecord [...]` | Nested Sigma | Dependent field-wise guard |
| `Sigma { fst, snd }` | Kernel Sigma directly | `fst.check v.fst && (snd v.fst).check v.snd` |
| `Pi { domain, codomain }` | Kernel Pi directly | `isFunction` (guard only) |
| `refined "P" A pred` | Subset type `{ x : A \| P(x) }` | `A.check v && pred v` |
| `Either A B` | Sum type (inl, inr) | Tag-based dispatch |
| `typeAt n` | `Type n` (universe) | `v ? universe && v.universe <= n` |

For first-order types (Nat, String, ListOf, Record), the fast path IS
the full check — these are decidable. The kernel adds nothing at
runtime for individual values; it adds the ability to state and verify
universal properties about families of values.

For higher-order types (Pi), the fast path can only check the
introduction form (`isFunction`). The kernel adds full verification
at elimination: `⊢ f(a) : B(a)` for specific `a`, or `⊢ p : Pi A B`
for a proof term witnessing the universal property.

### Blame tracking as an effect

Elaboration-mode type checking can send blame effects just as the
current `validate` does — the kernel judgment emits `typeCheck` effects
with context paths (`List[Nat][3]`) for error reporting. The handler
determines whether to abort, collect, or log. Same pattern, now backed
by a kernel judgment rather than an ad hoc predicate.

```nix
# Effectful checking with blame: elaboration sends kernel judgments as effects
checkWithBlame = type: value: context:
  let judgment = elaborate type value;
  in bind (send "typeCheck" { inherit type value context; }) (_:
    kernelCheck judgment);

```

## Infinite universes via streams

The current hardcoded `Type_0` through `Type_4` becomes a lazy stream:

```nix
universes = stream.iterate (u: {
  level = u.level + 1;
  type = typeAt (u.level + 1);
}) { level = 0; type = typeAt 0; };

```

The stream unfolds on demand. If your types max out at level 3, level 4
is never computed. The trampoline handles the stream iteration.

### Universe level inference

The kernel computes levels by structural recursion on types:

```
level(Nat)           = 0
level(Pi A B)        = max(level(A), level(B))
level(Sigma A B)     = max(level(A), level(B))
level(Type n)        = n + 1

```

No manual annotations. The kernel infers levels and verifies
stratification. The current `universe` field — a trusted declaration
that nothing enforces — becomes a computed, verified property.

### Universe polymorphism as an effect

Level allocation is an algebraic effect:

```nix
# A universe-polymorphic definition requests a level
polyList = bind freshLevel (u:
  pure (pi (typeAt u) (A: typeAt u)));

# Different handlers instantiate differently
atLevel3 = fx.run polyList (fixedLevel 3) null;

# Or: all instantiations as a stream
allLevels = stream.map (u:
  fx.run polyList (fixedLevel u) null
) (stream.iterate (n: n + 1) 0);

```

The definition doesn't commit to a level. The handler decides.

### Constraint solving via genericClosure

Level constraints (`?u >= max(?v, ?w)`) accumulate during checking.
The solver iterates to a fixed point:

```nix
solveLevels = constraints:
  let
    steps = builtins.genericClosure {
      startSet = [{ key = 0; solved = {}; changed = true; }];
      operator = state:
        if !state.changed then []
        else
          let next = propagate state.solved constraints;
          in [{ key = builtins.deepSeq next.solved (state.key + 1);
                inherit (next) solved changed; }];
    };
  in (lib.last steps).solved;

```

Same trampoline. Same `deepSeq` trick. The universe solver reuses
the exact infrastructure that runs effect handlers.

## Making the syntax livable

Writing proof terms as raw attrsets is not viable. Four techniques,
from least to most ambitious:

### HOAS: Nix lambdas as binders

Higher-Order Abstract Syntax uses Nix's own functions for variable
binding. The combinator applies a Nix lambda to a fresh variable
attrset, getting scope and shadowing for free:

```nix
let inherit (proof) forall lam nat zero succ eq refl cong ind;
in

# Proposition: forall n : Nat, n + 0 = n
prop = forall nat (n: eq nat (plus n zero) n);

# Proof: induction on n
pf = ind nat
  (k: eq nat (plus k zero) k)   # motive
  refl                          # base: 0 + 0 = 0
  (k: ih: cong succ ih)         # step: cong S on IH
;

```

The combinator `forall nat (n: ...)` calls the Nix function with a
fresh `{ tag = "var"; ... }` and builds the `pi` AST node. Variable
names, scope, and alpha-equivalence are handled by Nix's own evaluator.

### Tagless final: construction IS checking

Combinators type-check during construction. If the expression evaluates
without error, the proof is valid:

```nix
let
  # lam checks the body type against the codomain during construction
  lam = domain: bodyFn:
    let v = mkTypedVar domain;
        body = bodyFn v;
    in { term = mkLam domain body.term; type = mkPi domain body.type; };

  # app checks function/argument type compatibility during construction
  app = fn: arg:
    let _ = assertTypeEq fn.type.domain arg.type;
    in { term = mkApp fn.term arg.term;
         type = subst fn.type.codomain arg.term; };
in ...

```

Error messages point to the combinator call that failed, not to a
position in a flat AST. Nix's eval trace tells you which `lam` or
`app` had the wrong types.

### Builder pattern: method chaining for readability

Wrap terms in attrsets with methods for infix-like notation:

```nix
let
  E = expr: type: {
    inherit expr type;
    plus = other: E (mkApp plusFn (mkPair expr other.expr)) nat;
    eq = other: E (mkEq nat expr other.expr) (typeAt 0);
    ap = arg: E (mkApp expr arg.expr) (subst type.codomain arg.expr);
  };
  n = E (var 0) nat;
  z = E zero nat;
in
  (n.plus z).eq n  # reads as: n + 0 = n

```

## The self-reference boundary

The kernel is an effectful computation built on nix-effects. It reasons
about freer monad trees by structural induction. The freer monad trees
include the kernel's own computation.

This is where the Fire Triangle becomes load-bearing. Pedrot & Tabareau
(2020) proved that substitution, dependent elimination, and observable
effects can't coexist in a consistent type theory. In our system:

- The kernel at universe level N reasons about computations at
  levels 0 through N-1.
- The kernel's own effects live at level N.
- If a proof term references the kernel's own universe, the
  constraint solver hits a cycle: level ?u depends on level ?u.
  Unsatisfiable. Rejected.

The Fire Triangle doesn't say "don't do this." It says "the levels must
be strict." The universe stream can go as high as needed, but it can't
loop back. The constraint solver enforces this — not by advisory
convention, but by detecting cycles in level dependencies.

This is the point where universe levels stop being trusted declarations
and become computed, verified properties. The kernel infers them, the
constraint solver checks them, and the Fire Triangle tells us why
skipping this check would be unsound.

## The infrastructure reuse

Every piece of the kernel is built on machinery nix-effects already
provides:

| Component | Built on |
|-----------|---------|
| Normalization loop | `builtins.genericClosure` trampoline |
| Thunk prevention | `builtins.deepSeq` in worklist key |
| Continuation chaining | FTCQueue (O(1) bind) |
| Checker effects | Freer monad (`send`, `bind`, `pure`) |
| Error policy | Handler swap (strict / collecting / interactive) |
| Universe tower | `stream.iterate` |
| Level constraint solving | `genericClosure` as fixed-point |
| Surface syntax parsing | `builtins.match` + `genericClosure` Pratt parser |
| Blame tracking | `typeCheck` effect with context paths |
| Elaboration | Nix attrset → kernel term translation |

The kernel doesn't require new infrastructure. It reuses the trampoline,
the queue, the monad, the handlers, and the streams. nix-effects was
built to do effectful computation in a language that has no effects. A
type checker is effectful computation.

## Current architecture

### Effects substrate

The effects kernel — `pure`, `impure`, `send`, `bind`, `run`, `handle`,
`adapt`, FTCQueue, trampoline, all effect modules (state, error, reader,
writer, acc, choice, conditions, linear), streams — is the substrate
the type-checking kernel runs on.

### Type system grounding

The type system layer in `src/types/` is grounded in the kernel:

- `foundation.nix` — `mkType` with `kernelType` + optional refinement `guard`
- `primitives.nix` — `String`, `Int`, `Bool`, etc. wrapping `builtins.is*`
- `constructors.nix` — `Record`, `ListOf`, `Maybe`, `Either`, `Variant`
- `dependent.nix` — `Pi`, `Sigma`, `Certified`, `Vector`, `DepRecord`
- `refinement.nix` — `refined`, predicate combinators
- `universe.nix` — `typeAt`, `Type_0` through `Type_4`, `level`

All types have kernel backing via `kernelType`. The architecture is:

1. **Kernel module** (`src/tc/`, ~2200 lines) — term/value
   representations, NbE evaluator, quotation, conversion, bidirectional
   checking. Uses environments and closures, not explicit substitution.

2. **Elaboration module** (`src/tc/elaborate.nix`, `hoas.nix`) —
   translates the surface API into kernel types and translates Nix
   values into kernel terms. HOAS combinators for readable proof terms.

3. **Extraction layer** (`extract` in `elaborate.nix`) — reverses
   elaboration: kernel values back to Nix values. Enables verified
   functions: write in HOAS, kernel-check, extract usable Nix code.

4. **Convenience combinators** (`src/tc/verified.nix`) — higher-level
   interface for writing verified implementations with automatic motive
   construction and annotation insertion.

5. **Decision procedures** — `.check` on every type is the kernel's
   `decide` procedure: elaborate value to HOAS, kernel-check, return
   boolean. This is the "one system" architecture — no separate
   contract system, no adequacy bridge.

6. **Surface API** — the public-facing `fx.types.*` attrset. Same
   names, same usage patterns. `Record`, `ListOf`,
   `DepRecord`, `refined`, `Pi`, `Sigma` all work. `T.check v` runs
   the kernel's decide procedure. `T.prove prop` checks a proof term.

### What the API looks like

```nix
# Checking a value (decide via kernel)
fx.types.Nat.check 42                    # true
fx.types.(ListOf Nat).check [1, 2, 3]   # true

# Effectful validation with blame
fx.run (fx.types.Nat.validate 42) handlers []

# Proving a universal property
fx.types.prove (
  forall nat (n: eq nat (plus n zero) n)
) proofTerm                              # { ok = true; } or type error

# Verified function extraction
v.verify (H.forall "x" H.nat (_: H.nat)) (v.fn "x" H.nat (x: H.succ x))
# → Nix function, correct by construction

```

## What exists

1. **Type-checking kernel** (`src/tc/eval.nix`, `check.nix`,
   `quote.nix`, `conv.nix`, `term.nix`, `value.nix`). Pi, Sigma, Nat,
   Bool, List, Sum, Unit, Void, identity types, cumulative universes,
   and 7 axiomatized primitive types (String, Int, Float, Attrs, Path,
   Function, Any). Bidirectional checking with NbE. Fuel-bounded
   evaluation with `genericClosure` trampolining for stack safety.

2. **HOAS surface combinators** (`src/tc/hoas.nix`). `forall`, `lam`,
   `sigma`, `pair`, `natLit`, `natElim`, `boolElim`, `listElim`,
   `sumElim`, `j`, `refl`, `eq`, and more. Variable binding via Nix
   lambdas. Automatic elaboration from HOAS to de Bruijn core terms.

3. **Elaboration and extraction** (`src/tc/elaborate.nix`). Maps all
   type values to kernel terms via `elaborateValue`. `decide` function
   provides `.check` for all types. `extract` reverses elaboration,
   converting kernel values back to Nix values. Sentinel-based
   constant family detection for non-dependent Sigma/Pi.

4. **Kernel-grounded foundation** (`src/types/foundation.nix`). `mkType`
   requires `kernelType` and derives `.check` from `decide`. No
   hand-written predicates. All types — primitives, constructors,
   dependent types — have kernel backing.

5. **Convenience combinators** (`src/tc/verified.nix`). Higher-level
   interface: `v.verify type impl` writes in HOAS, kernel-checks,
   and extracts a usable Nix function. Includes `if_`, `match`,
   `matchList`, `matchSum`, `map`, `fold`, `filter`.

## Future work

The following features remain unimplemented:

- **Universe polymorphism as an effect.** Level allocation via
  `freshLevel` effect with handler-determined instantiation.
- **Constraint solving via genericClosure.** Level constraint
  propagation to a fixed point for universe inference.
- **Tagless final construction.** Type-checking during combinator
  construction.
- **Builder pattern notation.** Method chaining for readable proof terms.

## References

- Dunfield, J., & Krishnaswami, N. (2021). *Bidirectional Typing*.
  ACM Computing Surveys.
- Pedrot, P., & Tabareau, N. (2020). *The Fire Triangle*.
  POPL 2020.
- Kiselyov, O., & Ishii, H. (2015). *Freer Monads, More Extensible
  Effects*. Haskell Symposium 2015.
- Plotkin, G., & Pretnar, M. (2009). *Handlers of Algebraic Effects*.
  ESOP 2009.
- de Bruijn, N. (1972). *Lambda Calculus Notation with Nameless Dummies*.
  Indagationes Mathematicae.
- Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.
- Findler, R., & Felleisen, M. (2002). *Contracts for Higher-Order
  Functions*. ICFP 2002.
