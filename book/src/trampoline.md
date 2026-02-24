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

For validation of a large config — say, a NixOS module with hundreds of
fields — this would blow the stack.

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
    if step._comp._tag == "Pure"
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

Test suite validates 100,000 operations; manual runs confirm
1,000,000 operations in ~3 seconds with constant memory.

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
