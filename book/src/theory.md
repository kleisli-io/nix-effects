# Theory

nix-effects is grounded in several bodies of literature. This page explains
how the main ones map to the implementation.

## Algebraic effects and the freer monad

**Plotkin & Pretnar (2009)** *Handlers of Algebraic Effects* introduced the
handler model: a computation is a tree of effects with continuations; a
handler interprets each effect by either resuming the continuation with a
value or aborting it.

nix-effects implements this directly. A computation is either:

- `Pure value` — a finished computation returning a value
- `Impure effect continuation` — a suspended computation waiting for a
  handler to service `effect` and feed a result to `continuation`

The `send` function creates an `Impure` node:

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

`resume` invokes the continuation; `abort` discards it and halts.

## FTCQueue: O(1) bind

**Kiselyov & Ishii (2015)** *Freer Monads, More Extensible Effects* solved
the left-nested bind problem. Naïve free monads have O(n²) bind chains:

```
(m >>= f) >>= g  ≡  m >>= (f >=> g)
```

Each reassociation traverses the whole tree. Their insight: store
continuations in a catenable queue (FTCQueue).
`snoc` (append to queue) is O(1). Queue application (`qApp`) amortizes the
reassociation across traversal.

The result: O(n) total time for n bind operations, regardless of nesting
depth. This is essential for making effectful validation practical —
a `DepRecord` with 100 fields sends 100 effects, each of which binds.

## Martin-Löf Type Theory: value-dependent contracts

**Martin-Löf (1984)** *Intuitionistic Type Theory* introduced dependent types:
types that depend on values. nix-effects implements the structure of two
key forms as runtime contracts:

**Sigma (Σ)** — dependent pair. The second type is a function of the
first value:

```nix
Σ(fipsMode : Bool). if fipsMode then ListOf FIPSCipher else ListOf String
```

In nix-effects:

```nix
Sigma { fst = Bool; snd = b: if b then ListOf FIPSCipher else ListOf String; }
```

`Sigma.validate` decomposes the check: first validate `fst`, then — only
if `fst` passes — evaluate `snd fst-value` and validate it. Dependent
expressions are never evaluated on wrong-typed inputs.

**Pi (Π)** — dependent function type. The return type is a function of the
argument:

```nix
Pi { domain = String; codomain = _: Int; }
```

The guard checks `isFunction`; full contract is verified at elimination
via `.checkAt arg result`.

**Universe hierarchy** guards against Russell's paradox. Universe levels
are advisory -- the `universe` field is a trusted declaration, not a
computed invariant. Types themselves have
types (universes), stratified to `Type_0` through `Type_4`:

```nix
(typeAt 0).check Int  # true — Int lives at universe 0
level String           # 0
(typeAt 1).check (typeAt 0)  # true — Type_0 lives at universe 1
```

## Refinement types

Refinement types — a base type narrowed by a predicate — trace to
Freeman & Pfenning (1991). Rondon et al. (2008) extended the concept with
SMT-based inference (*Liquid Types*). nix-effects implements runtime
predicate checking via `refined`:

```nix
Port     = refined "Port"     Int (x: x >= 1 && x <= 65535);
NonEmpty = refined "NonEmpty" String (s: builtins.stringLength s > 0);
Nat      = refined "Nat"      Int (x: x >= 0);
```

The guard composes: `Port.check` first checks `Int`, then checks the
predicate. Combined predicates:

```nix
allOf [ pred1 pred2 ]  # conjunction
anyOf [ pred1 pred2 ]  # disjunction
negate pred            # negation
```

## The Fire Triangle (Pédrot & Tabareau 2020)

**Pédrot & Tabareau (2020)** *The Fire Triangle: How to Mix Substitution,
Dependent Elimination, and Effects* proves that substitution, dependent
elimination, and effects cannot all be unrestricted simultaneously. This
no-go result inspired nix-effects' three-level separation:

- **Level 1**: Types as pure values (the `mkType` attrset)
- **Level 2**: Type checking as effectful computation (`validate` sends
  `typeCheck` effects through the freer monad)
- **Level 3**: Error policy as handler (strict, collecting, logging)

This separation allows the same `ServiceConfig.validate config` computation
to be run with different handlers for different error semantics, without
modifying the type definition.

## Graded linear types (Orchard et al. 2019)

**Orchard, Liepelt & Eades (2019)** *Quantitative Program Reasoning with
Graded Modal Types* introduces a type system where each variable carries a
usage grade from a resource semiring. nix-effects implements this as `Linear`
(exactly one use), `Affine` (at most one), and `Graded` (exactly n uses).

The handler maintains a resource map counting each `consume` call against
a `maxUses` bound. At handler exit, a finalizer checks that each resource
was consumed the expected number of times — the grade discipline is enforced
at runtime via the effect system rather than statically.

## Adequacy

The adequacy invariant ties the pure guard to the effectful verifier:

```
T.check v  ⟺  all typeCheck effects in T.validate v pass
```

Tested via the all-pass handler: the final state is `true` iff all
`typeCheck` effects resumed with `true`. This invariant is checked for
every type constructor in the test suite.

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
