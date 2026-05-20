# bindP slow-path workloads.
#
# `bindP pos m k` has two paths:
#   - fast: `isPure m` → `k m.value`; no handler install.
#   - slow: install a local `TR.handle` typeError handler around `m`
#     that wraps emitted errors under `pos` before re-raising.
#
# The fast path is exercised whenever kernel rules descend into a
# sub-computation that already resolved (constant literals, cached
# evaluations). The slow path fires when the sub-computation may emit
# `typeError` — which in kernel use is common at failure and rare at
# success (the fast-path branch subsumes most success traffic).
#
# `slow-path-chain-5000` below isolates the slow-path handler-install
# cost by constructing 5000 layered `bindP` applications whose inner
# computation is a `typeError` emit (impure → slow path fires at
# every level). Each layer pays one `TR.handle` install + re-emit;
# the whole chain is then discharged via `runCheck`.
#
# `universal-blame-chain` exercises the same handler-install
# discipline across the *full* surface of position constructors —
# nullary kernel positions, parameterised `Elem` / `Field` / `Case`,
# and the `DConLayer` quotient. Each layer uses a different position
# so a refactor that breaks a single constructor path surfaces here.
#
# `desc-con-trampoline-blame-5000` drives the kernel desc-con
# trampoline at depth 5000 with a failure at an intermediate layer.
# This is the only workload that exercises the trampoline's
# `bindPChain [DConLayer k, ...]` discipline at scale; it gates the
# `DConLayer` quotient (per-blame chain depth stays constant
# regardless of trampoline depth).
#
# Regressions these workloads catch:
#   - `runScoped` or `mkHandler` taking more thunks than baseline.
#   - A refactor that accidentally switches all bindPs to slow path.
#   - Changes to `TR.handle` that increase per-install overhead.
#   - Per-position regressions in any new position constructor.
#   - Loss of the `DConLayer` quotient (chain depth scaling with
#     trampoline depth instead of staying constant).
{ fx }:

let
  K = fx.src.kernel;
  C = fx.src.tc.check;
  D = fx.src.diag.error;
  P = fx.src.diag.positions;
  H = fx.types.hoas;

  idxs = builtins.genList (x: x) 5000;

  leafErr = D.mkKernelError {
    rule = "check";
    msg = "bindP-slow-path-stress";
  };

  # Each `bindP P.DArgSort acc K.pure` folds `acc` (impure, carrying a
  # typeError) through the slow path: TR.handle intercepts the error,
  # wraps under DArgSort, re-emits at outer scope. Next iteration
  # sees that re-emit as its `m`, triggering another slow-path
  # install. Total: 5000 handler installs.
  chainComp = builtins.foldl'
    (acc: _: C.bindP P.DArgSort acc K.pure)
    (K.send "typeError" { error = leafErr; })
    idxs;

  # Rotation of distinct positions exercised at each layer of the
  # universal chain. Covers nullary kernel positions, parameterised
  # `Elem` / `Field` / `Case`, and the `DConLayer` quotient. The
  # outer `foldl'` indexes into this list mod its length, so each
  # layer's handler installs a different `nestUnder` wrap. Catches
  # regressions in individual position constructors that the
  # single-position chain misses.
  positionMix = [
    P.DArgSort
    P.PiDom
    P.SigmaFst
    P.LamBody
    P.LetBody
    P.Sub
    (P.Elem 0)
    (P.Field "f")
    (P.Case "step")
    P.MuIndex
    P.MuPayload
    (P.DConLayer 0)
  ];
  positionMixCount = builtins.length positionMix;

  universalChainComp = builtins.foldl'
    (acc: i:
      let pos = builtins.elemAt positionMix (i - i / positionMixCount * positionMixCount);
      in C.bindP pos acc K.pure)
    (K.send "typeError" { error = leafErr; })
    idxs;

  # 5000-deep cons chain at `List Nat` with a wrong-typed element at
  # depth 4000. The kernel's desc-con trampoline classifies the
  # description as a linear-recursive plus, peels along its single
  # recursive position, and runs the per-layer check loop. The blame
  # fires at layer 4000's payload field — under the new scheme this
  # produces a chain ending `[DConLayer 4000, Elem 0]` (depth 2 at
  # the outer blame edge), independent of the surrounding trampoline
  # depth.
  badConsAt = depth: total:
    let
      mk = i: acc:
        if i == 0 then acc
        else
          let
            elem = if i == (total - depth) then H.unit else H.zero;
          in
          mk (i - 1) (H.cons elem acc);
    in
    mk total H.nil;

in
{
  # Chain of 5000 slow-path bindPs over a single position. The final
  # `runCheck` discharges the outermost typeError, projecting the
  # flat error record.
  slow-path-chain-5000 = (C.runCheck chainComp).msg;

  # 5000-deep slow-path chain rotating through the position alphabet.
  # Same handler-install count as the single-position chain, but every
  # layer touches a different `positionKey` path and `nestUnder` wrap
  # — exercises the full slow-path surface in one workload.
  universal-blame-chain = (C.runCheck universalChainComp).msg;

  # Failure inside the desc-con trampoline at depth 4000 of a
  # 5000-deep cons chain. Gates the `DConLayer` quotient: blame
  # cost stays bounded regardless of trampoline depth.
  # Failure path on `checkHoas` returns `{ error, msg, ... }`; `.msg`
  # forces the leaf error projection without rendering the chain.
  desc-con-trampoline-blame-5000 = (H.checkHoas (H.listOf H.nat) (badConsAt 4000 5000)).msg;
}
