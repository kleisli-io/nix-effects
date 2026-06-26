# Effects and Handlers

nix-effects separates program intent from execution policy. A program
sends operations such as "read state", "write state", or "report a type
error". A handler decides what those operations mean.

That split is the execution model for the rest of the library. Typed
validation, diagnostics, streams, resource tracking, and the checker all
use the same effect substrate. The validator does not decide whether an
error aborts immediately or gets collected with the next ten errors. The
handler decides.

## Computations

A computation is either finished or waiting for a handler:

```nix
Pure value
Impure effect continuation
```

The public constructors are `pure`, `send`, and `bind`:

```nix
let
  inherit (fx) pure bind send;
in
  bind (send "get" null) (state:
    bind (send "put" (state + 1)) (_:
      pure state))
```

Most code uses effect modules rather than raw `send`:

```nix
let
  inherit (fx) pure bind run;
  inherit (fx.effects) state;

  increment =
    bind state.get (n:
      bind (state.put (n + 1)) (_:
        pure n));
in
  run increment state.handler 41
```

The result contains the returned value and final handler state:

```nix
{ value = 41; state = 42; }
```

## Handlers are policy

A handler is an attrset of operations. Each operation receives the
effect parameter, the current handler state, and the continuation
protocol. It can resume the computation or abort it:

```nix
{
  get = { param, state }: {
    resume = state;
    inherit state;
  };

  put = { param, state }: {
    resume = null;
    state = param;
  };
}
```

The computation above never mentions how state is represented. It only
sends `get` and `put`. That is why the same validation logic can run
under a strict handler in CI, a collecting handler in a documentation
test, or a logging handler in a development shell.

## Type checking as an effect

Validation uses the same shape. A type can expose both:

- `.check value` for a fast boolean boundary.
- `.validate value` for an effectful check with diagnostics.

```nix
let
  inherit (fx.types) String refined;
  TargetClass = refined "TargetClass" String
    (x: builtins.elem x [ "module" "file" "package" "check" ]);
in
  fx.run (TargetClass.validate "fleet")
    fx.effects.typecheck.collecting []
```

The type sends a `typeCheck` request with context. The handler turns
that request into an error list, a thrown exception, or a trace. The
type does not need separate implementations for each policy.

## Composition

Handlers compose because computations are ordinary values. `adapt` and
`adaptHandlers` let a local computation run under a different handler
view without rewriting the computation itself. Streams use the same
substrate to request the next value lazily. Linear resources use it to
count consumption. The kernel uses it to report type errors without
placing diagnostics inside the trusted evaluator.

The implementation details live in the
[Trampoline](/nix-effects/internals/trampoline) chapter. For day-to-day
use, the rule is simple: write computations in
terms of operations, then choose the handler that matches the boundary
where the computation runs.
