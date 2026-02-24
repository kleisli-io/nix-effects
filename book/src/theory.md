# Theory

Nine papers shaped the design of nix-effects — from its effects kernel
to its MLTT type-checking kernel. Here's how each maps to code.

## Algebraic effects and the freer monad

The basic idea: a computation is a tree of effects with continuations. A
handler walks the tree, interpreting each effect by either resuming the
continuation with a value or aborting it. This is the handler model from
Plotkin & Pretnar (2009).

nix-effects implements it directly. A computation is either:

- `Pure value` — finished, returning a value
- `Impure effect continuation` — suspended, waiting for a handler to
  service `effect` and feed the result to `continuation`

`send` creates an `Impure` node:

```nix
send "get" null
# Impure { effect = { name = "get"; param = null; }; queue = [k]; }

```

`bind` appends to the continuation queue:

```nix
bind (send "get" null) (s: pure (s * 2))
# Impure { effect = get; queue = [k1, k2] }  — O(1) per bind

```

Handlers provide the interpretation:

```nix
handlers = {
  get = { param, state }: { resume = state; inherit state; };
  put = { param, state }: { resume = null; state = param; };
};

```

`resume` feeds a value to the continuation; `abort` discards it and halts.

## FTCQueue: O(1) bind

Naïve free monads have O(n²) bind chains. The problem is reassociation:

```
(m >>= f) >>= g  ≡  m >>= (f >=> g)

```

Each reassociation traverses the whole tree. Kiselyov & Ishii (2015)
solved this by storing continuations in a catenable queue (FTCQueue)
instead of a list. `snoc` is O(1); queue application (`qApp`) amortizes
the reassociation across traversal.

The result: O(n) total for n bind operations, regardless of nesting depth.
This matters because a `DepRecord` with 100 fields sends 100 effects, each
of which binds. Without the queue, validation time would be quadratic in
the number of fields.

## Value-dependent types

Types that depend on values come from Martin-Löf (1984). All types are
grounded in the MLTT kernel (`src/tc/`). The user-facing API provides
convenience constructors, while the kernel provides type checking,
universe level computation, and proof verification.

**Sigma (Σ)** — dependent pair. The second type is a function of the
first value:

```nix
Σ(fipsMode : Bool). if fipsMode then ListOf FIPSCipher else ListOf String

```

In nix-effects:

```nix
Sigma { fst = Bool; snd = b: if b then ListOf FIPSCipher else ListOf String; }

```

`Sigma.validate` decomposes the check: validate `fst` first, then — only
if it passes — evaluate `snd fst-value` and validate that. Dependent
expressions are never evaluated on wrong-typed inputs.

**Pi (Π)** — dependent function type. The return type depends on the
argument:

```nix
Pi { domain = String; codomain = _: Int; }

```

The guard checks `isFunction`. Full verification happens at
elimination via the kernel's type-checking judgment.

**Universe hierarchy.** Types themselves have types, stratified from
`Type_0` through `Type_4` to guard against Russell's paradox:

```nix
(typeAt 0).check Int  # true — Int lives at universe 0
level String           # 0
(typeAt 1).check (typeAt 0)  # true — Type_0 lives at universe 1

```

Universe levels are computed by the kernel's `checkTypeLevel`: `level(Pi(A,B))
= max(level(A), level(B))`, `level(U(i)) = i+1`. The kernel rejects
self-containing universes (`U(i) : U(i)` fails), preventing both accidental
and adversarial paradoxes for all kernel-backed types.

## Refinement types

A refinement type narrows a base type with a predicate. The idea goes back
to Freeman & Pfenning (1991); Rondon et al. (2008) later extended it with
SMT-based inference under the name *Liquid Types*. We use runtime predicate
checking — no solver, just `refined`:

```nix
Port     = refined "Port"     Int (x: x >= 1 && x <= 65535);
NonEmpty = refined "NonEmpty" String (s: builtins.stringLength s > 0);
Nat      = refined "Nat"      Int (x: x >= 0);

```

The guard composes: `Port.check` first checks `Int`, then the predicate.
Combinators for building compound predicates:

```nix
allOf [ pred1 pred2 ]  # conjunction
anyOf [ pred1 pred2 ]  # disjunction
negate pred            # negation

```

## The Fire Triangle and Nix's purity boundary

Pédrot & Tabareau (2020) proved a no-go theorem they call the Fire
Triangle: a type theory with substitution, dependent elimination, and
*observable effects* is inconsistent. You must restrict at least one.

"Observable effects" has a specific meaning in the paper: a closed boolean
term that isn't observationally equivalent to `true` or `false`. The
canonical example is `callcc`-based backtracking, where a boolean changes
its value depending on the continuation — it's not stably either value.
Printing, exceptions, and non-termination *don't* count (the paper is
explicit about this). The effect has to be detectable through the type
system's notion of definitional equality.

Nix at eval time has no observable effects. It's pure, lazy, deterministic.
`builtins.trace` is printing (doesn't count). `builtins.throw` is an
exception (doesn't count). There's no `callcc`, no mutable state, no
first-class continuations. Every boolean evaluates to `true`, `false`, or
diverges. The Fire Triangle can't fire.

nix-effects operates entirely in this pure eval-time world. The freer
monad is a data structure — `Impure` and `Pure` attrsets — not an
operational effect. The handler walks the tree with pure functions. The
"effects" are simulated: a design pattern for structuring validation with
composable handlers, not a language feature.

The real effect boundary in Nix is between `nix eval` (pure evaluation)
and `nix build` (sandboxed side effects: running build scripts, writing
to the store). nix-effects catches configuration errors on the pure side
of that boundary, before any build effects happen. `nix build .#buggyService`
fails at eval time — no sandbox spins up, no build script runs.

So why mention the Fire Triangle at all? Because it validates the design.
If types were themselves effectful — if constructing a `DepRecord` could
trigger effects — dependent types would face the coherence problems
the theorem describes: evaluating a dependent type might trigger effects,
and you'd need to synchronize those effects between term and type (the
paper's ∂CBPV `dlet` binder addresses exactly this). By keeping types as
pure values, nix-effects avoids the problem by construction. The
three-level separation (pure types / effectful validation / handler
interpretation) comes from the handler pattern (Plotkin & Pretnar) and the
guard/verifier decomposition (Findler & Felleisen), but the Fire Triangle
is why keeping Level 1 pure matters in a system with dependent types.

The MLTT type-checking kernel (`src/tc/`) makes the Fire Triangle
argument concrete. The kernel implements a cumulative universe hierarchy
(`U(0) : U(1) : U(2) : ...`) where `checkTypeLevel` computes levels from
the typing derivation — `level(Pi(A, B)) = max(level(A), level(B))`,
`level(U(i)) = i + 1`. This prevents Girard's paradox: `U(i) : U(i)` is
rejected because `level(U(i)) = i + 1 > i`. The kernel verifies this
stratification for every type it checks, making universe levels an
enforced invariant rather than an advisory convention.

## Graded linear types

Resource tracking follows Orchard, Liepelt & Eades (2019), who introduced
a type system where each variable carries a usage grade from a resource
semiring. We implement three points on that spectrum: `Linear` (exactly one
use), `Affine` (at most one), and `Graded` (exactly n uses).

In practice, the handler maintains a resource map counting each `consume`
call against a `maxUses` bound. At handler exit, a finalizer checks that
every resource was consumed the expected number of times. The grade
discipline is enforced at runtime through the effect system, not statically.
You get the usage-tracking semantics without a custom type checker — at the
cost of finding violations at eval time rather than before it.

## Adequacy

The adequacy invariant connects the pure guard to the effectful verifier:

```
T.check v  ⟺  all typeCheck effects in T.validate v pass

```

We test this via the all-pass handler: the final state is `true` iff every
`typeCheck` effect resumed with `true`. The test suite checks this invariant
for every type constructor. It's the main correctness property of the whole
system.

## References

1. Plotkin, G., & Pretnar, M. (2009). *Handlers of Algebraic Effects*.
   ESOP 2009. [[doi](https://doi.org/10.1007/978-3-642-00590-9_7)]

2. Kiselyov, O., & Ishii, H. (2015). *Freer Monads, More Extensible Effects*.
   Haskell Symposium 2015. [[pdf](https://okmij.org/ftp/Haskell/extensible/more.pdf)]

3. Martin-Löf, P. (1984). *Intuitionistic Type Theory*. Bibliopolis.

4. Rondon, P., Kawaguchi, M., & Jhala, R. (2008). *Liquid Types*.
   PLDI 2008. [[doi](https://doi.org/10.1145/1375581.1375602)]

5. Findler, R., & Felleisen, M. (2002). *Contracts for Higher-Order Functions*.
   ICFP 2002. [[doi](https://doi.org/10.1145/581478.581484)]

6. Pédrot, P., & Tabareau, N. (2020). *The Fire Triangle: How to Mix
   Substitution, Dependent Elimination, and Effects*.
   POPL 2020. [[doi](https://doi.org/10.1145/3371126)]

7. Van Horn, D., & Might, M. (2010). *Abstracting Abstract Machines*.
   ICFP 2010. (See [Trampoline](trampoline.md))

8. Freeman, T., & Pfenning, F. (1991). *Refinement Types for ML*.
   PLDI 1991. [[doi](https://doi.org/10.1145/113445.113468)]

9. Orchard, D., Liepelt, V., & Eades, H. (2019). *Quantitative Program
   Reasoning with Graded Modal Types*. ICFP 2019.
   [[doi](https://doi.org/10.1145/3341714)]

## Prior art

- Borja, V. (2026). *nfx: Nix Algebraic Effects System with Handlers*.
  [[github](https://github.com/vic/nfx)] — Implements algebraic effects
  in pure Nix using a context-passing model with `immediate`/`pending`
  constructors. nix-effects adopted nfx's `adapt` handler combinator,
  `mk { doc, value, tests }` API pattern, and effect module vocabulary
  (`state`, `acc`, `conditions`, `choice`, streams), while building a
  new core on the freer monad encoding from Kiselyov & Ishii (2015)
  and adding value-dependent types and a type-checking kernel that nfx
  does not attempt.
