# Theory

Nine papers shaped nix-effects. Here's how each one maps to code.

## Algebraic effects and the freer monad

A computation is a tree of effects with continuations. A handler walks the
tree, interpreting each effect — either resuming the continuation with a
value or aborting it. That's the handler model from Plotkin & Pretnar
(2009), and nix-effects implements it directly.

A computation is either:

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

`resume` feeds a value to the continuation. `abort` discards it and halts.

## FTCQueue: O(1) bind

Naïve free monads have O(n²) bind chains. The problem is reassociation:

```
(m >>= f) >>= g  ≡  m >>= (f >=> g)

```

Each reassociation traverses the whole tree. Kiselyov & Ishii (2015)
solved this by storing continuations in a catenable queue (FTCQueue)
instead of a list. `snoc` is O(1); queue application (`qApp`) amortizes
the reassociation across traversal.

Total cost: O(n) for n bind operations, regardless of nesting depth. This
matters in practice — a `DepRecord` with 100 fields sends 100 effects, each
of which binds. Without the queue, validation time would be quadratic in
the number of fields.

The interpreter that processes these queued continuations uses
defunctionalization (Reynolds 1972): the recursive handler becomes a data
structure — effect name, parameter, handler result — and a worklist loop
(`builtins.genericClosure`) iterates over steps instead of recursing. This
is the pattern Van Horn & Might (2010) identified in *Abstracting Abstract
Machines*: store-allocated continuations plus worklist iteration give you
bounded stack depth. The [Trampoline](trampoline.md) chapter covers the
implementation — how `genericClosure` becomes a trampoline, why `deepSeq`
prevents thunk accumulation, and which automated tests pin stack-safety
behavior.

## Value-dependent types

Martin-Löf (1984) is where types that depend on values come from. In
nix-effects, all types bottom out in the MLTT kernel (`src/tc/`), which
handles type checking, universe level computation, and proof verification.
The user-facing API provides convenience constructors on top.

**Sigma (Σ)** — the dependent pair. The second component's type is a
function of the first component's value:

```nix
Σ(fipsMode : Bool). if fipsMode then ListOf FIPSCipher else ListOf String

```

In nix-effects:

```nix
Sigma { fst = Bool; snd = b: if b then ListOf FIPSCipher else ListOf String; }

```

`Sigma.validate` decomposes the check: validate `fst` first, then — only
if it passes — evaluate `snd fst-value` and validate that. The dependent
expression is never evaluated on a wrong-typed input. That ordering is
the whole point.

**Pi (Π)** — dependent function type. The return type depends on the
argument:

```nix
Pi { domain = String; codomain = _: Int; }

```

The kernel's decision procedure checks `isFunction` — closures are
opaque, so that's all it can verify at introduction. Full verification
happens at elimination via the kernel's type-checking judgment.

**Universe hierarchy.** Types themselves have types, stratified from
`Type_0` through `Type_4` to guard against Russell's paradox:

```nix
(typeAt 0).check Int  # true — Int lives at universe 0
level String           # 0
(typeAt 1).check (typeAt 0)  # true — Type_0 lives at universe 1

```

Universe levels are computed by the kernel's `checkTypeLevel`: `level(Pi(A,B))
= max(level(A), level(B))`, `level(U(i)) = i+1`. Self-containing universes
(`U(i) : U(i)`) are rejected — `level(U(i)) = i+1 > i`, so the check
fails. This prevents both accidental and adversarial paradoxes for every
kernel-backed type.

## Refinement types

Sometimes you need a type that's narrower than `Int` but wider than an
enum. Freeman & Pfenning (1991) introduced the refinement type: given a
base type T and a predicate P, the type {x:T | P(x)} admits only values
of T that satisfy P. `refined` is the direct implementation — `refined
"Port" Int (x: x >= 1 && x <= 65535)` is {x:Int | 1 ≤ x ≤ 65535} with
a name attached. Rondon et al. (2008) later scaled the idea with
SMT-based inference under the name *Liquid Types*. We skip the solver and
use runtime predicate checking:

```nix
Port     = refined "Port"     Int (x: x >= 1 && x <= 65535);
NonEmpty = refined "NonEmpty" String (s: builtins.stringLength s > 0);
Nat      = refined "Nat"      Int (x: x >= 0);

```

`Port.check` composes the kernel's decision (`Int`) with the refinement
predicate.
Combinators for building compound predicates:

```nix
allOf [ pred1 pred2 ]  # conjunction
anyOf [ pred1 pred2 ]  # disjunction
negate pred            # negation

```

## Soundness and what Nix provides

The kernel's soundness is standard MLTT metatheory. Martin-Löf (1984)
set out the rules, and the Mini-TT lineage (Coquand et al. 2009, Kovács
2022, and the elaboration-zoo and pi-forall tutorials) gives the
bidirectional elaboration and normalization-by-evaluation recipe the
kernel follows. Nothing in the kernel is novel on the metatheory side,
and none of the soundness argument routes through anything Nix-specific.

What Nix contributes is a faithful runtime for definitional equality.
NbE requires that reducing open terms is deterministic and side effect
free, and pure Nix evaluation gives you exactly that. `builtins.trace`
and `builtins.throw` are not observable through definitional equality,
so they cannot perturb conversion checking.

The effect layer sits above the kernel as meta-level freer monad data.
`Impure` and `Pure` attrsets are values walked by pure handlers. They
are not object-language effects in the kernel's grammar, and the kernel
has no constructor for them. This is how the effect layer can surface
kernel errors as `typeCheck` effects carrying context paths without
widening the trusted core.

## Graded linear types

Orchard, Liepelt & Eades (2019) introduced a type system where each
variable carries a usage grade from a resource semiring. We implement
three points on that spectrum: `Linear` (exactly one use), `Affine` (at
most one), and `Graded` (exactly n uses).

In practice, the handler maintains a resource map counting each `consume`
call against a `maxUses` bound. At handler exit, a finalizer checks that
every resource was consumed the expected number of times. The grade
discipline is enforced at runtime through the effect system, not
statically — so you get usage tracking without a custom type checker, but
violations show up at eval time rather than before it. That's a real
trade-off, and for configuration validation we're comfortable with it.

## Higher-order contracts and blame

Findler & Felleisen (2002) solved a problem that shows up immediately
when you try to check function types: you can't test a function contract
at the point of definition. A function is a closure — opaque. The only
way to check it is to wrap it and verify at application boundaries.

In nix-effects, this is exactly what happens. `decide(H.forall ..., f)`
can only confirm `builtins.isFunction f` — the kernel can't look inside
a Nix closure. For full verification, you write the implementation in
HOAS, the kernel type-checks the term, and `extract` wraps the result as
a Nix function that elaborates its arguments at every call boundary. The
contract is enforced at application, not definition. That's Findler &
Felleisen.

Their other contribution is blame tracking. When a check fails, the error
needs to say *which* contract was violated and *where*. In nix-effects,
`.validate` sends `typeCheck` effects carrying blame context — type name,
field path, rejected value — and the handler decides the error policy:
`strict` throws immediately, `collecting` accumulates all failures,
`logging` records every check. Same kernel judgment, different reporting
strategy — the handler pattern (Plotkin & Pretnar) composes with the
contract pattern (Findler & Felleisen) to separate what to check from
how to report.

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

6. Van Horn, D., & Might, M. (2010). *Abstracting Abstract Machines*.
   ICFP 2010. (See [Trampoline](trampoline.md))

7. Freeman, T., & Pfenning, F. (1991). *Refinement Types for ML*.
   PLDI 1991. [[doi](https://doi.org/10.1145/113445.113468)]

8. Orchard, D., Liepelt, V., & Eades, H. (2019). *Quantitative Program
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
