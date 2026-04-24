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
# Regressions this workload catches:
#   - `runScoped` or `mkHandler` taking more thunks than baseline.
#   - A refactor that accidentally switches all bindPs to slow path.
#   - Changes to `TR.handle` that increase per-install overhead.
{ fx }:

let
  K = fx.src.kernel;
  C = fx.src.tc.check;
  D = fx.src.diag.error;
  P = fx.src.diag.positions;

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

in {
  # Chain of 5000 slow-path bindPs. The final `runCheck` discharges
  # the outermost typeError, projecting the flat error record.
  slow-path-chain-5000 = (C.runCheck chainComp).msg;
}
