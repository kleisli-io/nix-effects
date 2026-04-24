# bindP: position-tagged bind for kernel rule bodies.
#
# Signature:
#
#   bindP : Position -> Computation a -> (a -> Computation b) -> Computation b
#
# Sequences two computations like `bind`, but installs a local typeError
# handler around the inner computation that wraps any emitted diagnostic
# error under the given Position before re-raising. The wrapping declares
# the descent coordinate at the caller site — precision that generic
# downstream paths (the check->infer catch-all fallback, conv failures
# deep inside a sub-term) cannot supply on their own.
#
# If the inner computation succeeds, the continuation `k` is invoked with
# the success value and the outer computation continues normally. A
# typeError emitted by `k` itself is not intercepted — bindP's wrapping
# applies only to errors raised by the inner `m`.
#
# Pure fast path: when `m` is `K.pure v`, no handler is installed; the
# combinator reduces to `k v` directly. This removes handler-install
# overhead from sub-delegations whose sub-computation has already
# resolved to a value.
#
# bindPChain threads a list of position/computation pairs through a
# single shared handler, collapsing N sequential bindPs into one
# handler install with a pre-composed nestUnder chain.
#
# Narrow dependencies, satisfying the trust-boundary discipline:
#   fx.kernel     — send, pure, isPure
#   fx.trampoline — handle (for the local interception)
#   fx.diag.error — nestUnder
# No fx.diag.pretty / fx.diag.hints imports; no new effects.
{ fx, ... }:

let
  K  = fx.kernel;
  TR = fx.trampoline;
  D  = fx.diag.error;
  isPure = fx.comp.isPure;

  # Internal sentinel used to smuggle a wrapped diag.Error back out of
  # the local typeError handler. An attrset carrying `_bindPErr` is not
  # a value any kernel rule can legitimately produce, so the post-handle
  # tag-check is unambiguous.
  bindPErrTag = "_bindPErr";

  # Build the local typeError handler that wraps emitted errors with a
  # pre-composed wrapping function. `wrapErr : Error -> Error` folds
  # the relevant nestUnder chain onto the captured leaf.
  mkHandler = wrapErr: {
    handlers.typeError = { param, state }: {
      abort = {
        "${bindPErrTag}" = wrapErr param.error;
      };
      inherit state;
    };
  };

  # Discharge an inner computation under a pre-composed wrap. Returns
  # either the handled success value directly, or a fresh typeError
  # impure node carrying the wrapped error.
  runScoped = wrapErr: k: m:
    let
      handled = TR.handle (mkHandler wrapErr) m;
      v = handled.value;
    in
      if builtins.isAttrs v && v ? ${bindPErrTag}
      then K.send "typeError" { error = v.${bindPErrTag}; }
      else k v;

  bindP = position: m: k:
    if isPure m then k m.value
    else runScoped (D.nestUnder position) k m;

  reverseList = xs:
    let n = builtins.length xs;
    in builtins.genList (i: builtins.elemAt xs (n - 1 - i)) n;

  # bindPChain positions m k
  #
  # Equivalent to the nested composition
  #   bindP p_1 (bindP p_2 (... (bindP p_n m) k_pure) k_pure) k
  # when intermediate continuations are pure passthroughs, but installs
  # only ONE typeError handler whose wrap function is
  #   err -> foldl' (acc, pos) -> nestUnder pos acc) err (reverse positions)
  # so the emitted chain has `positions[0]` as the outermost edge.
  #
  # Positions must be non-empty; pass [] to fall back to pure bind.
  bindPChain = positions: m: k:
    if positions == [] then K.bind m k
    else if isPure m then k m.value
    else
      let
        wrap = err: builtins.foldl'
          (acc: p: D.nestUnder p acc)
          err
          (reverseList positions);
      in runScoped wrap k m;

in {
  scope = { inherit bindP bindPChain; };
  tests =
    let
      P = fx.diag.positions;

      # Discharge a computation with a typeError handler that surfaces the
      # diag.Error directly. The resulting value is either the success a
      # (when no typeError fires) or an attrset { __surfacedError = diag.Error }
      # (when one does). Used by tests to inspect error structure.
      runSurfacing = comp:
        let r = TR.handle {
          handlers.typeError = { param, state }: {
            abort = { __surfacedError = param.error; };
            inherit state;
          };
        } comp;
        in r.value;

      # Raise a new-shape typeError directly.
      raiseDiag = err: K.send "typeError" { error = err; };

      sampleKernelErr = D.mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      };
    in {
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
          let err = runSurfacing (
            bindP P.DArgSort
              (K.pure 1)
              (_: raiseDiag sampleKernelErr));
          in err.__surfacedError;
        expected = sampleKernelErr;
      };

      # -- Pure fast path: bindP reduces to `k m.value`. The returned
      # computation is byte-identical to `k m.value` — no wrapper, no
      # queue changes, no sentinel attrset. Structural equality
      # pins both paths to the same result shape; distinguishing the
      # fast from the slow path requires a resource-use probe, not
      # available from inside a nix-unit test.
      "bindP-pure-equals-k-applied-directly" = {
        expr =
          let k = x: K.pure (x + 1);
          in (bindP P.DArgSort (K.pure 99) k) == (k 99);
        expected = true;
      };
      "bindP-pure-threads-to-impure-k" = {
        expr =
          let c = bindP P.DArgSort (K.pure 5) (_: raiseDiag sampleKernelErr);
          in c.effect.name;
        expected = "typeError";
      };

      # -- Error from m gets wrapped --
      "bindP-wraps-inner-error-under-position" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgSort
              (raiseDiag sampleKernelErr)
              K.pure);
          in err.__surfacedError;
        expected = D.nestUnder P.DArgSort sampleKernelErr;
      };
      "bindP-wrapped-error-has-one-child-edge" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgBody
              (raiseDiag sampleKernelErr)
              K.pure);
          in builtins.length err.__surfacedError.children;
        expected = 1;
      };
      "bindP-child-position-is-the-supplied-one" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgBody
              (raiseDiag sampleKernelErr)
              K.pure);
          in (builtins.elemAt err.__surfacedError.children 0).position;
        expected = P.DArgBody;
      };
      "bindP-child-error-is-the-inner-error" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgBody
              (raiseDiag sampleKernelErr)
              K.pure);
          in (builtins.elemAt err.__surfacedError.children 0).error;
        expected = sampleKernelErr;
      };
      "bindP-short-circuits-continuation-on-error" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgSort
              (raiseDiag sampleKernelErr)
              (_: raiseDiag (D.mkKernelError {
                rule = "k-should-not-run";
                msg = "k fired despite m erroring";
              })));
          in (builtins.elemAt err.__surfacedError.children 0).error.detail.rule;
        expected = "check";
      };

      # -- Nested bindP: positional chain --
      "bindP-nested-outer-position-is-outermost-edge" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgSort
              (bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure)
              K.pure);
          in (builtins.elemAt err.__surfacedError.children 0).position;
        expected = P.DArgSort;
      };
      "bindP-nested-inner-position-is-second-edge" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgSort
              (bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure)
              K.pure);
              outerEdge = builtins.elemAt err.__surfacedError.children 0;
              innerEdge = builtins.elemAt outerEdge.error.children 0;
          in innerEdge.position;
        expected = P.DArgBody;
      };
      "bindP-nested-leaf-error-preserved" = {
        expr =
          let err = runSurfacing (
            bindP P.DArgSort
              (bindP P.DArgBody
                (raiseDiag sampleKernelErr)
                K.pure)
              K.pure);
              outerEdge = builtins.elemAt err.__surfacedError.children 0;
              innerEdge = builtins.elemAt outerEdge.error.children 0;
          in innerEdge.error;
        expected = sampleKernelErr;
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
          let err = runSurfacing (
            bindP P.DArgSort
              (K.bind (K.pure 5)
                (x: K.bind (K.pure (x * 2))
                  (_: raiseDiag sampleKernelErr)))
              K.pure);
              leaf = (builtins.elemAt err.__surfacedError.children 0).error;
          in leaf;
        expected = sampleKernelErr;
      };

      # -- bindPChain: fused sequential positions --
      "bindPChain-empty-positions-falls-back-to-bind" = {
        expr = runSurfacing (bindPChain [] (K.pure 11) (x: K.pure (x + 1)));
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
          in fused.__surfacedError == nested.__surfacedError;
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
          in fused.__surfacedError == nested.__surfacedError;
        expected = true;
      };
      "bindPChain-three-positions-outermost-first" = {
        expr =
          let err = runSurfacing (
            bindPChain [ P.PiDom P.DArgSort P.DArgBody ]
              (raiseDiag sampleKernelErr)
              K.pure);
          in (builtins.elemAt err.__surfacedError.children 0).position;
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
          in walkToLeaf err.__surfacedError;
        expected = sampleKernelErr;
      };
      "bindPChain-pure-fast-path" = {
        expr = (bindPChain [ P.DArgSort P.DArgBody ] (K.pure 3) K.pure).value;
        expected = 3;
      };
      "bindPChain-success-threads-value" = {
        expr = runSurfacing (
          bindPChain [ P.DArgSort P.DArgBody ]
            (K.pure 10)
            (x: K.pure (x * 2)));
        expected = 20;
      };
    };
}
