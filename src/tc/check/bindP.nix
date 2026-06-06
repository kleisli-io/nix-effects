# bindP: position-tagged bind for kernel rule bodies.
#
# Signatures:
#
#   bindP      : Position -> Computation a
#                          -> (a -> Computation b) -> Computation b
#   bindPR     : Position -> String -> Computation a
#                          -> (a -> Computation b) -> Computation b
#   bindPChain : [Position] -> Computation a
#                          -> (a -> Computation b) -> Computation b
#
# `bindP` sequences two computations like `bind`, but brackets the inner
# computation `m` with a push/pop of a blame frame so any typeError `m`
# raises is wrapped under the given Position before it reaches the
# top-level handler. A pure `m` threads its value straight to `k` with no
# frame (it raises nothing, so push-then-pop is a no-op); an impure `m`
# emits the push (`tcBlamePush`) outermost — `Impure` in O(1), forcing `m`
# only to WHNF — so recursion in `m` defers into the trampoline. The wrapping
# declares the descent coordinate at the caller site — precision that
# generic downstream paths (the check->infer catch-all fallback, conv
# failures deep inside a sub-term) cannot supply on their own.
#
# `bindPR` extends `bindP` with a rule annotation: the wrapping Position
# is decorated via `P.withRule rule pos` before nestUnder, recording which
# kernel rule emitted the descent alongside the structural coordinate.
#
# `bindPChain` threads a list of positions through ONE composite frame
# whose wrap nests them outermost-first (`positions[0]` on top),
# collapsing N sequential bindPs into a single push/pop bracket.
#
# The continuation `k` runs AFTER the matching pop, so a typeError it
# raises is not wrapped by this frame — wrapping applies only to errors
# raised by `m`. The blame frames live in handler state (see `_blame`);
# the single top-level typeError handler folds them onto the leaf error
# to reconstruct the nested trace.
#
# Narrow dependencies, satisfying the trust-boundary discipline:
#   fx.kernel          — send, bind, pure
#   fx.trampoline      — handle (tests only)
#   fx.diag.error      — nestUnder, appendTrace
#   fx.diag.positions  — withRule (rule decoration on Position)
# No fx.diag.pretty / fx.diag.hints imports.
{ fx, api, ... }:

let
  K = fx.kernel;
  TR = fx.trampoline; # tests only
  D = fx.diag.error;
  P = fx.diag.positions;
  isPure = fx.comp.isPure;

  pushEff = "tcBlamePush";
  popEff = "tcBlamePop";
  yieldEff = "tcYield";

  # Wrap an emitted error: append `{ rule = position.rule, position }`
  # to the Kernel-layer trace (no-op on Generic/Contract), then
  # nestUnder the position.
  wrapWithTrace = position: err:
    D.nestUnder position (D.appendTrace (position.rule or null) position err);

  # A pure `m` threads its value straight to `k` (no frame: it raises
  # nothing, so push-then-pop is a no-op). An impure `m` is bracketed with
  # push/pop of a wrap frame; `tcBlamePush` is the outermost send, so this
  # is `Impure` in O(1) and forces `m` only to WHNF — the recursion in `m`
  # defers into the trampoline. `k` runs after the pop, so an error it
  # raises escapes this frame. The fast path is forcing-safe only because
  # recursive checker entries are effect-first at their head (see `_yield`).
  scoped = wrapErr: m: k:
    if isPure m then k m.value
    else
      K.bind (K.send pushEff wrapErr) (_:
        K.bind m (v:
          K.bind (K.send popEff null) (_: k v)));

  bindP = position: scoped (wrapWithTrace position);

  bindPR = position: rule: scoped (wrapWithTrace (P.withRule rule position));

  reverseList = xs:
    let n = builtins.length xs;
    in builtins.genList (i: builtins.elemAt xs (n - 1 - i)) n;

  # Non-empty `positions` push ONE composite frame nesting them
  # outermost-first; empty falls back to a plain bind.
  bindPChain = positions: m: k:
    if positions == [ ]
    then K.bind m k
    else
      scoped
        (err: builtins.foldl' (acc: p: wrapWithTrace p acc) err (reverseList positions))
        m k;

  # Blame stack as an opaque cons list: each cell is a closure, so the
  # trampoline's per-step `deepSeq newState` forces it to WHNF only
  # (functions are atomic to deepSeq) and never walks the shared tail.
  # Push is O(1) and structurally shared, so the N retained trampoline
  # steps cost O(N) total rather than the O(N²) a forced Nix vector
  # would (vector cons copies the whole spine each push). `emptyBlame`
  # is the nil; `consBlame` prepends the innermost live frame.
  emptyBlame = _: null;
  consBlame = w: rest: (_: { head = w; tail = rest; });

  # Blame-frame stack in handler state (head = innermost live frame).
  blameHandlers = {
    "${pushEff}" = { param, state }: {
      resume = null;
      state = state // { blame = consBlame param (state.blame or emptyBlame); };
    };
    "${popEff}" = { param, state }: {
      resume = null;
      state = state // { blame = (state.blame null).tail; };
    };
  };

  # Reconstruct the nested-wrapped error. Walk the opaque cons list
  # ITERATIVELY via a genericClosure worklist (collecting frames
  # innermost-first) — never a recursive or lazy `[w] ++ rest` walk,
  # which would re-overflow the host stack at consume on a deep blame
  # stack — then apply each frame innermost-first so the outermost frame
  # ends up the top edge. Runs only on the error path, never on a
  # successful check.
  foldBlame = blame: err:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; rest = blame; }];
        operator = s:
          let cell = s.rest null;
          in if cell == null then [ ]
          else [{ key = s.key + 1; rest = cell.tail; w = cell.head; }];
      };
      wraps = builtins.map (s: s.w) (builtins.tail steps);
    in
    builtins.foldl' (acc: w: w acc) err wraps;

in
{
  scope = {
    bindP = api.leaf {
      description = "bindP: position-tagged bind for kernel rule bodies — brackets the inner computation with a push/pop blame frame so any typeError it raises is wrapped under the given Position before reaching the top-level handler.";
      signature = "bindP : Position -> Computation a -> (a -> Computation b) -> Computation b";
      doc = ''
        Brackets an impure inner computation `m` with a
        `tcBlamePush`/`tcBlamePop` frame whose wrap calls
        `D.nestUnder position` on every `diag.Error` `m` raises. A pure
        `m` skips the frame and threads its value to `k` (it raises
        nothing, so push-then-pop is a no-op). The push is emitted before
        an impure `m`, so the combinator is `Impure` in O(1) and forces
        `m` only to WHNF — recursion in `m` defers into the trampoline.
        The wrapping records the descent coordinate at the caller site —
        precision that downstream generic paths (the `check → infer`
        catch-all, deep conv failures) cannot supply.

        The continuation `k` runs after the pop, so errors it raises
        are not wrapped by this frame. Frames are reconstructed onto
        the leaf error by the single top-level handler (see `_blame`).
        Use over `K.bind` whenever the failing site has a definite
        positional identity in the surface syntax; pair with
        `bindPChain` to thread N positions through one bracket.
      '';
      value = bindP;
    };

    bindPR = api.leaf {
      description = "bindPR: rule-annotated variant of `bindP` — wraps the inner computation under `withRule rule position` so the blame edge records both the structural coordinate and the kernel-rule identity that emitted the descent.";
      signature = "bindPR : Position -> String -> Computation a -> (a -> Computation b) -> Computation b";
      doc = ''
        Equivalent to `bindP (fx.diag.positions.withRule rule position)
        m k`. The hint resolver consults only `position.tag`, so the
        rule annotation never changes hint lookup — it surfaces in
        pretty-printed output and is available to any consumer reading
        `Position.rule` directly.
      '';
      value = bindPR;
    };

    bindPChain = api.leaf {
      description = "bindPChain: fused sequential variant of `bindP` — threads a list of positions through a single shared typeError handler so the emitted blame chain has `positions[0]` as the outermost edge.";
      signature = "bindPChain : [Position] -> Computation a -> (a -> Computation b) -> Computation b";
      doc = ''
        Equivalent to nested `bindP p_1 (bindP p_2 (... (bindP p_n m)
        k_pure) k_pure) k` when intermediate continuations are pure
        passthroughs, but pushes a single composite frame nesting the
        positions outermost-first. Empty `positions` falls back to
        `K.bind`.
      '';
      value = bindPChain;
    };

    _blame = api.leaf {
      description = "_blame: shared blame-frame discipline for bindP — { handlers, fold, empty } installed by every trampoline that runs a kernel check Computation so position wrapping is reconstructed at the single top-level typeError handler. `blame` is an opaque cons list (deepSeq-opaque ⇒ O(1)/step, structurally shared); `empty` is its nil for state init.";
      signature = "_blame : { handlers : Handlers, fold : Blame -> Error -> Error, empty : Blame }";
      value = { handlers = blameHandlers; fold = foldBlame; empty = emptyBlame; };
    };

    _yield = api.leaf {
      description = "_yield: tcYield defer discipline — { handlers, wrap } installed alongside _blame by every trampoline running a kernel check Computation. A head `wrap` makes a recursive checker entry effect-first (O(1) WHNF), so the bindP `isPure` fast path stays flat on recursive arms while leaving syntactic leaves Pure. `tcYield` carries no state and no blame frame — observationally invisible.";
      signature = "_yield : { handlers : Handlers, wrap : Computation a -> Computation a }";
      value = {
        handlers = { "${yieldEff}" = { param, state }: { resume = null; inherit state; }; };
        wrap = comp: K.bind (K.send yieldEff null) (_: comp);
      };
    };
  };

  tests =
    let
      P = fx.diag.positions;

      # Discharge a computation with the blame discipline + a typeError
      # handler that surfaces the folded diag.Error. The result is either
      # the success value (when no typeError fires) or an attrset
      # { __surfacedError = diag.Error } (when one does). Used by tests to
      # inspect error structure.
      runSurfacing = comp:
        let
          r = TR.handle
            {
              state = { blame = emptyBlame; };
              handlers = blameHandlers // {
                typeError = { param, state }: {
                  abort = { __surfacedError = foldBlame state.blame param.error; };
                  inherit state;
                };
              };
            }
            comp;
        in
        r.value;

      # Raise a new-shape typeError directly.
      raiseDiag = err: K.send "typeError" { error = err; };

      sampleKernelErr = D.mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      };
    in
    {
      # -- Success passthrough --
      "bindP-pure-threads-value-to-k" = {
        expr = runSurfacing (bindP P.DArgSort (K.pure 42) (x: K.pure (x + 1)));
        expected = 43;
      };
      "bindP-pure-does-not-wrap-success" = {
        expr = runSurfacing (bindP P.DArgSort (K.pure 7) K.pure);
        expected = 7;
      };
      "bindP-pure-continuation-may-emit-error" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (K.pure 1)
                (_: raiseDiag sampleKernelErr));
          in
          err.__surfacedError;
        expected = sampleKernelErr;
      };

      # -- Pure `m`: the value threads straight to `k` via the fast path
      # (0 effects); behavior asserted by running rather than byte-identity.
      "bindP-pure-runs-k-on-value" = {
        expr = runSurfacing (bindP P.DArgSort (K.pure 99) (x: K.pure (x + 1)));
        expected = 100;
      };
      # `k` runs after the pop, so the error it raises is not wrapped by
      # this frame — surfaces as the raw leaf.
      "bindP-pure-continuation-error-unwrapped" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort (K.pure 5) (_: raiseDiag sampleKernelErr));
          in
          err.__surfacedError;
        expected = sampleKernelErr;
      };

      # -- Error from m gets wrapped --
      "bindP-wraps-inner-error-under-position" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          err.__surfacedError;
        expected = D.nestUnder P.DArgSort
          (D.appendTrace null P.DArgSort sampleKernelErr);
      };
      "bindP-wrapped-error-has-one-child-edge" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          builtins.length err.__surfacedError.children;
        expected = 1;
      };
      "bindP-child-position-is-the-supplied-one" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          (builtins.elemAt err.__surfacedError.children 0).position;
        expected = P.DArgBody;
      };
      "bindP-child-error-is-the-inner-error" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          (builtins.elemAt err.__surfacedError.children 0).error;
        expected = D.appendTrace null P.DArgBody sampleKernelErr;
      };
      "bindP-short-circuits-continuation-on-error" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (raiseDiag sampleKernelErr)
                (_: raiseDiag (D.mkKernelError {
                  rule = "k-should-not-run";
                  msg = "k fired despite m erroring";
                })));
          in
          (builtins.elemAt err.__surfacedError.children 0).error.detail.rule;
        expected = "check";
      };

      # -- Nested bindP: positional chain --
      "bindP-nested-outer-position-is-outermost-edge" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (bindP P.DArgBody
                  (raiseDiag sampleKernelErr)
                  K.pure)
                K.pure);
          in
          (builtins.elemAt err.__surfacedError.children 0).position;
        expected = P.DArgSort;
      };
      "bindP-nested-inner-position-is-second-edge" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (bindP P.DArgBody
                  (raiseDiag sampleKernelErr)
                  K.pure)
                K.pure);
            outerEdge = builtins.elemAt err.__surfacedError.children 0;
            innerEdge = builtins.elemAt outerEdge.error.children 0;
          in
          innerEdge.position;
        expected = P.DArgBody;
      };
      "bindP-nested-leaf-error-preserved" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (bindP P.DArgBody
                  (raiseDiag sampleKernelErr)
                  K.pure)
                K.pure);
            outerEdge = builtins.elemAt err.__surfacedError.children 0;
            innerEdge = builtins.elemAt outerEdge.error.children 0;
          in
          innerEdge.error;
        expected = D.appendTrace null P.DArgBody sampleKernelErr;
      };

      # -- Composition --
      "bindP-success-composes-with-bind" = {
        expr = runSurfacing (
          bindP P.DArgSort
            (K.pure 10)
            (x: K.bind (K.pure (x * 2)) (y: K.pure (y + 1))));
        expected = 21;
      };
      "bindP-covers-bind-chain-in-m" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (K.bind (K.pure 5)
                  (x: K.bind (K.pure (x * 2))
                    (_: raiseDiag sampleKernelErr)))
                K.pure);
            leaf = (builtins.elemAt err.__surfacedError.children 0).error;
          in
          leaf;
        expected = D.appendTrace null P.DArgSort sampleKernelErr;
      };

      # -- bindPChain: fused sequential positions --
      "bindPChain-empty-positions-falls-back-to-bind" = {
        expr = runSurfacing (bindPChain [ ] (K.pure 11) (x: K.pure (x + 1)));
        expected = 12;
      };
      "bindPChain-single-position-equals-bindP" = {
        expr =
          let
            fused = runSurfacing (
              bindPChain [ P.DArgSort ]
                (raiseDiag sampleKernelErr)
                K.pure);
            nested = runSurfacing (
              bindP P.DArgSort
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          fused.__surfacedError == nested.__surfacedError;
        expected = true;
      };
      "bindPChain-two-positions-matches-nested-bindP" = {
        expr =
          let
            fused = runSurfacing (
              bindPChain [ P.DArgSort P.DArgBody ]
                (raiseDiag sampleKernelErr)
                K.pure);
            nested = runSurfacing (
              bindP P.DArgSort
                (bindP P.DArgBody
                  (raiseDiag sampleKernelErr)
                  K.pure)
                K.pure);
          in
          fused.__surfacedError == nested.__surfacedError;
        expected = true;
      };
      "bindPChain-three-positions-outermost-first" = {
        expr =
          let
            err = runSurfacing (
              bindPChain [ P.PiDom P.DArgSort P.DArgBody ]
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          (builtins.elemAt err.__surfacedError.children 0).position;
        expected = P.PiDom;
      };
      "bindPChain-three-positions-leaf-preserved" = {
        expr =
          let
            err = runSurfacing (
              bindPChain [ P.PiDom P.DArgSort P.DArgBody ]
                (raiseDiag sampleKernelErr)
                K.pure);
            walkToLeaf = e:
              if builtins.length e.children == 0 then e
              else walkToLeaf (builtins.elemAt e.children 0).error;
          in
          walkToLeaf err.__surfacedError;
        expected = D.appendTrace null P.DArgBody sampleKernelErr;
      };
      "bindPChain-pure-threads-value" = {
        expr = runSurfacing (bindPChain [ P.DArgSort P.DArgBody ] (K.pure 3) K.pure);
        expected = 3;
      };
      "bindPChain-success-threads-value" = {
        expr = runSurfacing (
          bindPChain [ P.DArgSort P.DArgBody ]
            (K.pure 10)
            (x: K.pure (x * 2)));
        expected = 20;
      };

      # -- bindPR: rule-annotated wrapping --
      "bindPR-success-threads-value-to-k" = {
        expr = runSurfacing (
          bindPR P.DArgSort "desc-arg" (K.pure 42) (x: K.pure (x + 1)));
        expected = 43;
      };
      "bindPR-pure-runs-k-on-value" = {
        expr = runSurfacing (bindPR P.DArgSort "r" (K.pure 99) (x: K.pure (x + 1)));
        expected = 100;
      };
      "bindPR-wraps-inner-error-with-rule-decoration" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgSort "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          err.__surfacedError;
        expected =
          let pos' = P.withRule "desc-arg" P.DArgSort;
          in D.nestUnder pos' (D.appendTrace "desc-arg" pos' sampleKernelErr);
      };
      "bindPR-edge-position-has-rule-set" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgBody "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            edge = builtins.elemAt err.__surfacedError.children 0;
          in
          edge.position.rule;
        expected = "desc-arg";
      };
      "bindPR-edge-position-tag-unchanged" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgBody "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            edge = builtins.elemAt err.__surfacedError.children 0;
          in
          edge.position.tag;
        expected = "DArgBody";
      };
      "bindPR-edge-position-intent-preserved" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.PiDom "pi-dom"
                (raiseDiag sampleKernelErr)
                K.pure);
            edge = builtins.elemAt err.__surfacedError.children 0;
          in
          edge.position.intent;
        expected = "the domain type of Π";
      };
      "bindPR-leaf-error-preserved" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgSort "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            edge = builtins.elemAt err.__surfacedError.children 0;
          in
          edge.error;
        expected = D.appendTrace "desc-arg"
          (P.withRule "desc-arg" P.DArgSort)
          sampleKernelErr;
      };
      "bindPR-short-circuits-continuation-on-error" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgSort "desc-arg"
                (raiseDiag sampleKernelErr)
                (_: raiseDiag (D.mkKernelError {
                  rule = "k-should-not-run";
                  msg = "k fired despite m erroring";
                })));
            edge = builtins.elemAt err.__surfacedError.children 0;
          in
          edge.error.detail.rule;
        expected = "check";
      };

      # -- bindPR is observationally equal to
      # `bindP (P.withRule rule position) m k`.
      "bindPR-equals-bindP-with-pre-decorated-position" = {
        expr =
          let
            fused = runSurfacing (
              bindPR P.DArgSort "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            decomposed = runSurfacing (
              bindP (P.withRule "desc-arg" P.DArgSort)
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          fused.__surfacedError == decomposed.__surfacedError;
        expected = true;
      };

      # -- Trace auto-capture: each wrap appends one entry; rule is
      # null on plain bindP, populated on bindPR.
      "bindP-trace-appends-one-entry" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          err.__surfacedError.detail.trace;
        expected = [{ rule = null; position = P.DArgSort; }];
      };
      "bindPR-trace-records-rule-on-entry" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgSort "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            t = err.__surfacedError.detail.trace;
          in
          (builtins.head t).rule;
        expected = "desc-arg";
      };
      "bindPR-trace-entry-position-has-rule-decoration" = {
        expr =
          let
            err = runSurfacing (
              bindPR P.DArgBody "desc-arg"
                (raiseDiag sampleKernelErr)
                K.pure);
            t = err.__surfacedError.detail.trace;
          in
          (builtins.head t).position.rule;
        expected = "desc-arg";
      };
      "bindP-nested-trace-innermost-first" = {
        expr =
          let
            err = runSurfacing (
              bindP P.DArgSort
                (bindP P.DArgBody
                  (raiseDiag sampleKernelErr)
                  K.pure)
                K.pure);
          in
          map (e: e.position.tag) err.__surfacedError.detail.trace;
        expected = [ "DArgBody" "DArgSort" ];
      };
      "bindPChain-trace-records-each-position" = {
        expr =
          let
            err = runSurfacing (
              bindPChain [ P.PiDom P.DArgSort P.DArgBody ]
                (raiseDiag sampleKernelErr)
                K.pure);
          in
          map (e: e.position.tag) err.__surfacedError.detail.trace;
        expected = [ "DArgBody" "DArgSort" "PiDom" ];
      };
      "bindP-trace-preserves-existing-entries" = {
        expr =
          let
            seeded = D.appendTrace "seed" P.AppHead sampleKernelErr;
            err = runSurfacing (
              bindP P.DArgSort
                (raiseDiag seeded)
                K.pure);
          in
          map (e: e.position.tag) err.__surfacedError.detail.trace;
        expected = [ "AppHead" "DArgSort" ];
      };
      "bindP-generic-error-passes-through-without-trace" = {
        expr =
          let
            genErr = D.mkGenericError {
              value = 17;
              guard = { predicate = "x > 18"; };
              msg = "refinement";
            };
            err = runSurfacing (
              bindP P.DArgSort (raiseDiag genErr) K.pure);
            wrapped = err.__surfacedError;
            innerEdge = builtins.elemAt wrapped.children 0;
          in
          [
            wrapped.layer.tag
            innerEdge.error.layer.tag
            (innerEdge.error.detail ? trace)
          ];
        expected = [ "Generic" "Generic" false ];
      };
    };
}
