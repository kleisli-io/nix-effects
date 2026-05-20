# Sugar

nix-effects ships an opt-in syntax layer. The kernel doesn't import it,
nothing in the effect interpreter depends on it, and removing it leaves
the library unchanged. What it buys is readability. A three-step state
computation without sugar:

```nix
bind state.get (n:
  bind (state.put (n + 1)) (_:
    bind state.get (n2:
      pure n2)))
```

and with sugar, two forms:

```nix
# Combinator
do [ (_: state.get) (n: state.put (n + 1)) (_: state.get) ]

# Operator
state.get / (n: state.put (n + 1)) / (_: state.get)
```

Both evaluate to the same value under the state handler. A third form
— `letM` — applies to parallel effects whose results you want under
named bindings:

```nix
# Without sugar
bind (reader.asks (e: e.host)) (host:
  bind (reader.asks (e: e.port)) (port:
    pure "${host}:${toString port}"))

# With letM
letM {
  host = reader.asks (e: e.host);
  port = reader.asks (e: e.port);
} (b: pure "${b.host}:${toString b.port}")
```

`letM` evaluates its attrs independently and passes the result attrset
to the continuation. Use it when the effects don't depend on each
other's values.

## Opting in

Sugar is a hybrid namespace. Effect combinators sit at the top level
of `fx.sugar`, so `with fx.sugar;` brings `do`, `letM`, `pure`,
`bind`, `run`, and `handle` into scope immediately. Division and
types are one level deeper, under `operators` and `types`
respectively.

```
fx.sugar
  ├── do, letM
  ├── pure, bind, map, seq, pipe, kleisli
  ├── run, handle
  ├── operators
  │     └── __div
  └── types
        ├── wrap
        └── Int, String, Bool, Float, Path, Null, Unit, Any
```

The combinator-only form is safe under every Nix dialect. No operator
magic, no `with`, no chance of surprising anyone:

```nix
let inherit (fx.sugar) do letM;
in do [
  (_: state.get)
  (n: state.put (n * 3))
  (_: state.get)
]
```

Adding `/` as left-associative bind turns long `bind` chains into
pipelines:

```nix
let inherit (fx.sugar.operators) __div;
in state.get / (s: state.put (s + 7)) / (_: state.get)
```

For a file that's mostly computation, reach for `with fx.sugar;` and
pair it with the `__div` inherit:

```nix
let
  inherit (fx.sugar.operators) __div;
in with fx.sugar;
  state.get / (s: state.put (s * 2)) / (_: state.get)
```

The division operator is always nested under `operators`. `with
fx.sugar;` alone will not activate `/` — you have to reach for
`operators` explicitly. That nesting is the entire reason the
namespace is hybrid.

## Effect combinators

### `do`: sequence of steps

`do` takes a list of functions, each of which receives the previous
step's value and returns the next computation. The first step gets
`null`:

```nix
do [
  (_: pure 1)
  (x: pure (x + 1))
  (x: pure (x * 10))
]
# runs to 20
```

Empty lists produce `pure null`. Singletons are equivalent to calling
the one step on `null`. The argument binding is positional: `(n: ...)`
means "the previous step's value is bound to `n`." If you don't need
it, use `_`.

### `letM`: named results

`letM` collects an attrset of computations, evaluates each one, and
hands the result attrset to a continuation. The Reader-pattern example
from the test suite:

```nix
letM {
  host = reader.asks (e: e.host);
  port = reader.asks (e: e.port);
} (b: pure "${b.host}:${toString b.port}")
# runs to "example.com:443"
```

The continuation receives `{ host; port; }`. When a computation and
its continuation don't need sequencing by intermediate values but do
need named results in scope, `letM` is cleaner than nested `bind`.

### `__div`: operator-style bind

`__div` is a magic attribute name. When both operands of `/` are
non-numeric and `__div` is lexically in scope, Nix dispatches the
operator through it. `fx.sugar.operators.__div` is `fx.bind` under
another name.

```nix
let inherit (fx.sugar.operators) __div;
in state.get / (n: pure (n + 1)) / (n: pure (n * 2))
```

The form is left-associative: `a / f / g` is `bind (bind a f) g`.
This matches the usual reading of a pipeline.

### Re-exports

For convenience, `fx.sugar` re-exports `pure`, `bind`, `map`, `seq`,
`pipe`, `kleisli`, `run`, and `handle` verbatim from `fx`. `with
fx.sugar;` gives you everything the effect layer exposes without
a second `inherit` line.

## Type sugar

### Primitives and refinement

`fx.sugar.types` pre-wraps the eight zero-ary primitives —
`Int`, `String`, `Bool`, `Float`, `Path`, `Null`, `Unit`, `Any` —
with a `__functor` that builds a refinement when you apply a
predicate. A target class, written without sugar:

```nix
let inherit (fx.types) String refined;
in refined "TargetClass" String
  (x: builtins.elem x [ "module" "file" "package" "check" ])
```

and with sugar:

```nix
let inherit (fx.sugar.types) String;
in String (x: builtins.elem x [ "module" "file" "package" "check" ])
```

Both produce a kernel-identical type. The difference is readability
when you're composing several predicates.

### Name cascading

Every refinement appends a `?` to the base type's name. Repeated
refinement cascades:

```nix
let inherit (fx.sugar.types) Int;
  P0 = Int;                       # "Int"
  P1 = Int (x: x >= 0);           # "Int?"
  P2 = Int (x: x >= 0) (x: x < 10); # "Int??"
in builtins.toString P2
# "Int??"
```

The name is what shows up in error messages. If `Int??` isn't
descriptive enough, drop back to `fx.types.refined` and give the type
an explicit name:

```nix
let inherit (fx.types) refined String;
in refined "RendererClass" String
  (x: builtins.elem x [ "module" "file" "package" "check" ])
```

### `wrap` for user-defined types

Types built with `fx.types.mkType` don't get sugar by default. Wrap
them with `fx.sugar.types.wrap` to opt in:

```nix
let
  inherit (fx.types) mkType hoas;
  inherit (fx.sugar.types) wrap;

  UserInt = mkType { name = "UserInt"; kernelType = hoas.int_; };
  Sugared = wrap UserInt;
in
  (Sugared (x: x > 0)).check 5   # true
```

Wrapping is purely additive. It only adds `__functor` (for refinement
application) and `__toString` (for the name). The base type's kernel,
check, description, universe, and every other field stay untouched —
so a sugared type is interchangeable with the desugared original
everywhere the kernel looks at it.

### Sugar inside Record fields

Constructors like `Record`, `ListOf`, `Maybe`, and `Either` already
consume a first argument — their schema. Wrapping them with
`__functor` would collide with that call shape, so `fx.sugar.types`
doesn't wrap them. It doesn't need to: a sugared field-type inside a
Record schema composes for free, because Record reads only the
kernel, which sugar preserves:

```nix
let inherit (fx.types) Record;
    inherit (fx.sugar.types) Int String Bool;
in Record {
  age = Int (x: x >= 0);
  name = String (s: builtins.stringLength s > 0);
  active = Bool;
}
```

This Record has the same `_kernel` as the hand-refined version. The
sugar is pushed *into* the schema, where it needs no special support
from the constructor.

## Caveats

A few details worth knowing before you reach for sugar.

### `+` can't be overloaded

Nix's `+` operator is `ExprConcatStrings` in the parser <sup>1</sup>.
The runtime dispatches on operand types (string, path, number) without
consulting any magic attribute. There's no `__plus` to implement.
Applied to two types, `+` will either concatenate (if they're
strings), add (if they're numbers), or error out. It is not a hook.

For the same reason, there's no way to overload `==`, `<`, or most
other operators. Sugar uses what Nix already dispatches through:
`__functor` for callable attrsets, `__toString` for string coercion,
and `__div` for `/`.

### `with` does not activate `__div`

Nix's `/` operator looks up `__div` by name in the enclosing lexical
scope. It does not search `with`-scoped values. This surprises people
who expect the two forms to be interchangeable:

```nix
# Works:
let inherit (fx.sugar.operators) __div; in (state.get / f)

# Does NOT work — raises an arithmetic division error at runtime:
with fx.sugar.operators; (state.get / f)
```

The reason is that `with` only extends the free-variable lookup
chain — it does not introduce `__div` as a bound name in the scope
that `/` consults. The full-sugar form above wraps `inherit
(fx.sugar.operators) __div;` in the same `let` that brings in the
combinators for exactly this reason.

A witness test lives at `tests/sugar-effects-test.nix` under
`withOperatorsDoesNotActivateDiv`. It asserts that `with
fx.sugar.operators; (6 / 2) == 3` — plain arithmetic, not `__div`
dispatch.

### Lix 2.92+ rejects `__div` shadow

Lix <sup>2</sup> deprecated the pattern of binding a name prefixed
with `__` that shadows a builtin-reserved operator slot. As of Lix
2.92, `let inherit (ops) __div; in ...` produces
`shadow-internal-symbols` errors during parse. If your codebase
targets Lix, stick to `do` and `letM` — they don't touch this
mechanism.

This is not a CppNix limitation. `__div` works under CppNix 2.18+ and
2.31 (the release we test against). The Lix deprecation is a
deliberate policy choice in that fork.

### Scope pollution with `with`

`with fx.sugar.operators;` brings `__div` into the lookup chain as a
value, not as an operator hook. As just noted, it won't make `/`
dispatch to it. But it does make the name `__div` available for
reference — a minor footgun if you were relying on shadowing.
Prefer `inherit` over `with` for operator opt-in.

### Name cascading versus explicit names

Chained refinements produce names like `Int??`. That's intentional
("you refined this twice") but not always helpful in error messages.
If your domain has a real name, use `fx.types.refined` directly:

```nix
let inherit (fx.types) refined Int;
    Even = refined "Even" Int (x: builtins.bitAnd x 1 == 0);
    Positive = refined "Positive" Int (x: x > 0);
    EvenPositive = refined "EvenPositive" Even (x: x > 0);
in EvenPositive.name   # "EvenPositive"
```

Sugar is for in-place predicates, not named types that outlive their
definition.

## Forward-compat notes

Sugar is strictly additive and never references anything the type
system marks for retirement. Three commitments hold across future
changes to the kernel and type modules.

**Kernel preservation.** A sugared type has the same `_kernel` as its
base. Constructors (`Record`, `ListOf`, `Maybe`, `Either`, `Variant`)
read only `_kernel` — so a sugared field is indistinguishable from a
desugared one to every kernel consumer.

**Refinement delegation.** Sugar never constructs refined types
directly. Every `sugared T (pred)` call goes through
`fx.types.refined`, which is the user-facing API point guaranteed to
survive kernel-internal reorganizations. If `refined` changes shape,
sugar follows automatically.

**No diagnostic emission.** Sugar never builds values from
`src/diag/positions.nix` or `src/diag/error.nix`. Error annotation
happens via the base type's `description` and `name`, which
propagate through `refined` without sugar-specific code. When the
diagnostic layer gains structure, sugar will inherit it.

Active witness tests for each of these live in
`tests/sugar-compat-test.nix`. Running the test file as part of
`nix flake check` keeps the commitments observable.

## When to reach for which form

`do` and `letM` are the default. Reach for `__div` when a pipeline
has three or more obvious-effect steps and the parentheses are
hurting readability. Reach for `with fx.sugar;` when you're writing a
file that's mostly computation, not mostly plumbing.

For types, use `fx.sugar.types` for one-off refinements inside Record
schemas. Drop back to `fx.types.refined` when the type deserves a
name you'll reference elsewhere.

---

<sup>1</sup> `src/libexpr/parser.y` in the Nix source, handling
`ExprConcatStrings`.

<sup>2</sup> Lix is a community fork of Nix. Relevant deprecation:
`shadow-internal-symbols` in Lix 2.92 release notes.
