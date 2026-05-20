{ fx, lib, ... }:

let
  inherit (fx.binds) bindAttrs;
in {
  scope = rec {
    do = steps: lib.foldl' (acc: step: bind acc step) (pure null) steps;

    letM = attrs: k: bind (bindAttrs attrs) k;

    inherit (fx.kernel) pure bind map seq pipe kleisli;
    inherit (fx.trampoline) run handle;
  };

  tests = {};

  __docs = {
    do = {
      description = "do: sequence a list of `Comp` steps left-to-right via `bind`, returning a single composed `Comp`; each step receives the previous result as its argument.";
      signature = "do : [Comp a -> Comp b] -> Comp b";
      doc = ''
        Use when steps form a strictly linear pipeline where each step
        consumes the previous result. The seed value is `pure null`, so
        the first step's argument is `null` — discard it if the first
        step is producer-shaped (`_: pure x`). An empty list returns
        `pure null`.

        Prefer `kleisli` when composing Kleisli arrows without an initial
        value, and `pipe` when threading a non-monadic seed through
        effectful transforms. For non-linear data-flow where multiple
        independent results feed into one continuation, use `letM`.
      '';
    };
    letM = {
      description = "letM: `attrs`-based monadic binding — runs `bindAttrs attrs` to gather a record of results, then passes the record to continuation `k` for the next step.";
      signature = "letM : { name = Comp a } -> ({ name = a } -> Comp b) -> Comp b";
      doc = ''
        Use when several independent computations must complete before a
        single dependent step runs — `letM { a = ca; b = cb; } ({ a, b }: ...)`
        replaces a nested `bind ca (a: bind cb (b: ...))` chain with a
        flat record. Field order in the resulting record is unspecified;
        ordering of side effects across fields is determined by
        `bindAttrs`, not by the caller's attribute layout.

        Prefer over `do` when the bound values are siblings rather than a
        left-to-right pipeline. For a single bind, plain `bind` is
        clearer.
      '';
    };
    pure   = { description = "Re-export of fx.kernel.pure. See fx.kernel for details."; };
    bind   = { description = "Re-export of fx.kernel.bind. See fx.kernel for details."; };
    map    = { description = "Re-export of fx.kernel.map. See fx.kernel for details."; };
    seq    = { description = "Re-export of fx.kernel.seq. See fx.kernel for details."; };
    pipe   = { description = "Re-export of fx.kernel.pipe. See fx.kernel for details."; };
    kleisli = { description = "Re-export of fx.kernel.kleisli. See fx.kernel for details."; };
    run    = { description = "Re-export of fx.trampoline.run. See fx.trampoline for details."; };
    handle = { description = "Re-export of fx.trampoline.handle. See fx.trampoline for details."; };
  };
}
