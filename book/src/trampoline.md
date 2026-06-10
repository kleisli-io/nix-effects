# Trampoline

The trampoline is how nix-effects interprets freer monad computations
with O(1) stack depth in a language with no iteration primitives and no
tail-call optimization.

## The problem

Nix is a pure, lazy, functional language. It has no loops. Every
"iteration" is recursion. A naïve free monad interpreter using mutual
recursion would build a call stack proportional to the computation length:

```
run (bind (bind (bind ... (send "get" null) ...) ...) ...)
  → run step1
    → run step2
      → run step3
        → ...  (N frames deep)

```

For validation of a large DSL value — say, an aspect graph with hundreds
of declarations — this would blow the stack.

## The solution: `builtins.genericClosure`

Nix's `builtins.genericClosure` is the only built-in iterative primitive.
It implements a worklist algorithm:

```
genericClosure {
  startSet = [ initialNode ];
  operator = node -> [ ...nextNodes ];
}

```

`operator` is called on each node. New nodes returned by `operator` are
added to the worklist if their `key` hasn't been seen before. The result
is the set of all reachable nodes.

nix-effects repurposes this as a trampoline: each step of computation is
a node. The `operator` function handles one effect and produces the next
step as a singleton list. The computation terminates when `operator`
returns `[]` (i.e., when we reach a `Pure` node).

```nix
steps = builtins.genericClosure {
  startSet = [{ key = 0; _comp = comp; _state = initialState; }];
  operator = step:
    if isPure step._comp
    then []          # halt
    else [ nextStep ]; # one more step
};

```

Stack depth: **O(1)**. `genericClosure` handles its own iteration
internally; the `operator` function is never deeply nested.

## The thunk problem and `deepSeq`

`genericClosure` only forces the `key` field of each node (for
deduplication). All other fields — including `_state` and `_comp` — are
lazy thunks.

Without intervention, after N steps the `_state` field would be:

```
f(f(f(... f(initialState) ...)))  # N thunks deep

```

Forcing the final `_state` would then rebuild the entire call stack in
thunk evaluation, defeating the purpose.

The fix: make `key` depend on `builtins.deepSeq newState`:

```nix
key = builtins.deepSeq newState (step.key + 1)

```

Since `genericClosure` forces `key`, it also forces `deepSeq newState`,
which eagerly evaluates the state at each step. No thunk chain builds up.

The test suite validates deep effect chains and pure bind chains so the
stack-safety contract stays covered by automated checks.

### State-shape contract

`builtins.deepSeq newState` imposes a contract on handler-state shape: every
value reachable through state must be deepSeq-tolerant. Scalars, finite
records, and lists of scalars satisfy this trivially. Functions are also
safe — `deepSeq` on a closure forces it to WHNF and stops, never recursing
into the captured environment.

`builtins.deepSeq` detects cycles by object identity: `forceValueDeep` keeps a
seen-set of already-forced values, so a self-referential attrset terminates.
That guard has two gaps. A lazy graph that regenerates a fresh object on each
force — as a derivation's `passthru` can — is never recognized as seen and
overflows. And a traversal that keeps no seen-set at all — `builtins.toJSON`,
or the `api.extractValue` walker — descends any cyclic value until the
evaluator overflows. Deep-forcing a real derivation's full attribute closure at
every step is also prohibitively expensive even where it terminates. None of
these failures is recoverable: a stack overflow and `toJSON`'s "cannot convert
a function to JSON" both escape `tryEval`; only `throw` and `assert false` are
catchable, which is why a fuel-bounded walker that throws on exhaustion is the
one usable divergence signal.

This behavior is identical on every evaluator probed — Nix 2.3.18, 2.18.8,
2.24.8, Lix 2.91.1, and 2.35pre — so the contract rests on stable language
semantics, not an evaluator-specific quirk.

For this case the library ships `fx.state.mkThunk` / `forceThunk`
(`src/state/thunk.nix`). The carrier wraps any value as
`{ _tag = "Thunk"; _force = _: value; }` — a closure shields the value
from deepSeq. The companion kernel type former `H.thunk : Hoas → Hoas`
is decided by a *lazy structural* walker: it verifies `is attrset ∧ has
_force closure` and does NOT recurse into `_force`. Inner-type validation
runs at forget time, post-forced. Forcing in the validator would defeat
the deepSeq-shielding the whole construct exists for.

Effect descriptions that carry derivations through state type their payload
fields as `H.thunk H.derivation`, not `H.derivation`, so `fx.send`-time
validation rejects unwrapped drvs before they reach the trampoline. The
inner type is parametric: any value category that needs trampoline transit
can ride through `H.thunk a` with no bespoke primitive.

## Defunctionalization

The interpreter defunctionalizes (**Reynolds 1972**) the recursive handler:
the continuation moves from the call stack into an explicit data structure
(the FTCQueue). The worklist loop processes these continuations iteratively
rather than recursively — the same pattern identified by **Van Horn & Might
(2010)** in *Abstracting Abstract Machines*.

**Gibbons (2022)** *Continuation-Passing Style, Defunctionalization,
Accumulations, and Associativity* shows the hidden precondition: this transformation is valid
when the accumulated operation is associative. For nix-effects, the
handler state transformations compose associatively because function
composition is associative.

## References

- Reynolds, J. C. (1972). *Definitional Interpreters for Higher-Order Programming Languages*. ACM Annual Conference.
- Van Horn, D., & Might, M. (2010). *Abstracting Abstract Machines*. ICFP 2010.
- Gibbons, J. (2022). *Continuation-Passing Style, Defunctionalization, Accumulations, and Associativity*. The Art, Science, and Engineering of Programming, 6(2). [[doi](https://doi.org/10.22152/programming-journal.org/2022/6/7)]
- Kiselyov, O., & Ishii, H. (2015). *Freer Monads, More Extensible Effects*.
