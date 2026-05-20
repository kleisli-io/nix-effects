# nix-effects adapt: Handler context transformation
#
# Adapted from nfx by Victor Borja (https://github.com/vic/nfx),
# licensed under Apache-2.0. The adapt combinator for composing
# handlers with different state shapes originates from that project.
#
#   adapt : { get : P -> S, set : P -> S -> P } -> Handler<S> -> Handler<P>
#
# Contravariant on context (get: extract child state from parent),
# covariant on result (set: incorporate child state back into parent).
#
# This enables modular handler composition: each handler manages its own
# state slice, and adapt wires them together.
{ api, ... }:

let
  adapt = { get, set }: handler: { param, state }:
    let
      childState = get state;
      result = handler { inherit param; state = childState; };
    in
    if result ? abort then {
      abort = result.abort;
      state = set state result.state;
    }
    else {
      resume = result.resume;
      state = set state result.state;
    };

  adaptHandlers = lens: handlers:
    builtins.mapAttrs (_: handler: adapt lens handler) handlers;

in
api.namespace {
  description = "Handler context transformation: `adapt`/`adaptHandlers` reposition handlers onto larger state via lenses — contravariant on context, covariant on continuation.";
  doc = "Handler context transformation. Contravariant on context, covariant on continuation.";
  value = {
    adapt = api.leaf {
      value = adapt;
      description = "adapt: lift a child-state handler through a `get`/`set` lens onto parent state; contravariant on context extraction, covariant on result incorporation.";
      signature = "adapt : { get : P -> S, set : P -> S -> P } -> Handler S -> Handler P";
      doc = ''
        Transform a handler's state context.

        Wraps a handler that works with child state `S` so it works with
        parent state `P`, using a `get`/`set` lens. Propagates both
        `resume` and `abort`.

        ```nix
        counterHandler = { param, state }: { resume = null; state = state + param; };
        adapted = adapt { get = s: s.counter; set = s: c: s // { counter = c; }; } counterHandler;
        # adapted now works with { counter = 0; logs = []; } state
        ```
      '';
      tests = {
        "adapts-simple-state" = {
          expr =
            let
              inner = { param, state }: { resume = null; state = state + param; };
              outer = adapt
                {
                  get = s: s.counter;
                  set = s: c: s // { counter = c; };
                }
                inner;
              result = outer { param = 5; state = { counter = 10; other = true; }; };
            in
            result.state.counter;
          expected = 15;
        };
        "preserves-parent-state" = {
          expr =
            let
              inner = { param, state }: { resume = null; state = state + param; };
              outer = adapt
                {
                  get = s: s.counter;
                  set = s: c: s // { counter = c; };
                }
                inner;
              result = outer { param = 5; state = { counter = 10; other = true; }; };
            in
            result.state.other;
          expected = true;
        };
        "passes-resume-through" = {
          expr =
            let
              inner = { param, state }: { resume = param * 2; inherit state; };
              outer = adapt
                {
                  get = s: s;
                  set = _: s: s;
                }
                inner;
              result = outer { param = 21; state = null; };
            in
            result.resume;
          expected = 42;
        };
        "propagates-abort" = {
          expr =
            let
              inner = { param, state }: { abort = "stopped"; inherit state; };
              outer = adapt
                {
                  get = s: s.x;
                  set = s: x: s // { inherit x; };
                }
                inner;
              result = outer { param = null; state = { x = 0; y = 1; }; };
            in
            { gotAbort = result ? abort; abortVal = result.abort; yPreserved = result.state.y; };
          expected = { gotAbort = true; abortVal = "stopped"; yPreserved = 1; };
        };
      };
    };

    adaptHandlers = api.leaf {
      value = adaptHandlers;
      description = "adaptHandlers: lift an entire handler set through the same `get`/`set` lens; equivalent to mapping `adapt` over each handler in the attrset.";
      signature = "adaptHandlers : { get : P -> S, set : P -> S -> P } -> Handlers S -> Handlers P";
      doc = ''
        Adapt an entire handler set (attrset of handlers) to a different state context.
        Applies the same `get`/`set` lens to every handler in the set.

        ```nix
        stateHandlers = {
          get = { param, state }: { value = state; inherit state; };
          put = { param, state }: { value = null; state = param; };
        };
        adapted = adaptHandlers { get = s: s.data; set = s: d: s // { data = d; }; } stateHandlers;
        ```
      '';
      tests = {
        "adapts-all-handlers" = {
          expr =
            let
              handlers = {
                inc = { param, state }: { resume = null; state = state + param; };
                get = { param, state }: { resume = state; inherit state; };
              };
              adapted = adaptHandlers
                {
                  get = s: s.n;
                  set = s: n: s // { inherit n; };
                }
                handlers;
              r1 = adapted.inc { param = 5; state = { n = 10; }; };
              r2 = adapted.get { param = null; state = r1.state; };
            in
            r2.resume;
          expected = 15;
        };
      };
    };
  };
}
