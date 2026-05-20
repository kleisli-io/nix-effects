# Description-toolkit fold workloads.
#
# `foldDescM` (monadic catamorphism) and `foldDescWithPath` (positional-
# blame variant using `bindP` at each descent) are the description-
# toolkit primitives downstream phases (generic `checkD`/`inferD`,
# ornament-driven elaboration) build on. Both must preserve the
# allocation envelope of the kernel CHECK list-chain budget so they
# can be hot-path additions without regressing list-chain headroom.
#
# Depth note. The chain depth is 2000, not 5000. `foldDescM` is a
# plain recursive Nix function; its frame budget is the Nix
# interpreter's max-call-depth (default 10000) minus the per-node
# overhead of `applyDescFn`/`rawView`/`K.bind`, which empirically
# sits around 2000–2300 for the current shape. The kernel CHECK
# chain at depth 5000 fits because every sub-delegation routes
# through `TR.handle`'s trampoline (worklist via genericClosure,
# bounded stack). Trampolinising `foldDescM` is a separate
# concern that lands when `checkD`/`inferD` need it — at that
# point the bench depth scales to 5000 alongside the kernel CHECK
# envelope.
#
# Two workloads:
#
# `foldM-chain-2000` exercises the **fast path** — every sub-handler
# returns `K.pure …`. The combinator's per-node overhead is bound only
# by `K.bind` and the description-view peeling, no handler install.
# Regressions this catches:
#   - `foldDescM` switching from the `isPure` short-circuit to a slow
#     bind path on success.
#   - A refactor that adds spurious thunks to the `rawView` /
#     `applyDescFn` loop.
#
# `foldWithPath-blame-chain-2000` exercises the **slow path** — the
# leaf handler emits `typeError` and every arg-layer's `bindP` fires,
# wrapping the leaf error under `DArgBody` before re-raising. After
# 2000 descents the surfaced error carries a 2000-deep chain of
# `DArgBody` edges with the original error preserved at the leaf.
# Regressions this catches:
#   - `foldDescWithPath` switching from `bindP` back to `K.bind`
#     (losing positional auto-wrapping).
#   - `bindP`'s `nestUnder`/handler-install overhead growing on the
#     description-fold call path.
#   - The fold accidentally short-circuiting at the first impure
#     sub-walk (which would skip remaining descents and shorten the
#     emitted chain).
{ fx }:

let
  K = fx.src.kernel;
  D = fx.src.diag.error;
  H = fx.src.tc.hoas;
  E = fx.src.tc.eval;
  TR = fx.src.trampoline;
  G = fx.src.tc.generic;

  # 2000-deep arg-chain description. Each layer wraps the inner sub-
  # description in `descArg Unit 0 Unit (λ_:Unit. ...)`; the deepest
  # layer is `retI Unit 0 tt`. Built top-down via foldl' so the
  # innermost layer is the original retI and each outer layer wraps
  # it. The resulting HOAS tree is evaluated once via H.elab + E.eval
  # so the fold can re-peel layers from a fully-evaluated Val without
  # paying repeated HOAS-elaboration cost.
  argChainHoas =
    builtins.foldl'
      (acc: _: H.descArg H.unit 0 H.unit (_: acc))
      (H.retI H.unit 0 H.tt)
      (builtins.genList (x: x) 2000);

  argChainVal = E.eval [ ] (H.elab argChainHoas);

  # Fast-path fold: every handler returns `K.pure …`. Counter handler
  # accumulates depth (1 for `ret`, 1 + sub for `arg`). The result
  # discharges to a Pure 5001 with no impure-effect node.
  foldMCount =
    G.desc.foldDescM
      {
        ret = _: K.pure 1;
        arg = x: K.pure (1 + x.sample);
        default = _: K.pure 0;
      }
      argChainVal;

  # Slow-path fold: ret handler emits typeError. Each arg-layer's
  # bindP wraps the captured leaf error under `DArgBody`. The outer
  # `TR.handle` surfaces the wrapped error so its chain length is
  # observable to the workload result.
  leafErr = D.mkKernelError {
    rule = "foldDescWithPath";
    msg = "foldWithPath-bench-leaf";
  };

  blameComp =
    G.desc.foldDescWithPath [ ]
      {
        ret = _: K.send "typeError" { error = leafErr; };
        arg = x: K.pure x.sample;
        default = _: K.pure null;
      }
      argChainVal;

  surfaced = TR.handle
    {
      handlers.typeError = { param, state }: {
        abort = { __surfacedError = param.error; };
        inherit state;
      };
    }
    blameComp;

  # Walk the surfaced error tree counting edges to the leaf. Returns
  # an integer so the runner can pin the result deterministically.
  chainLength = err:
    let
      go = e: acc:
        if builtins.length e.children == 0
        then acc
        else go (builtins.elemAt e.children 0).error (acc + 1);
    in
    go err 0;

in
{
  # 2000-step fast-path fold. Result = sum of `1` over 2001 nodes
  # (2000 arg layers + the inner ret). Pins the per-node fold cost
  # at the `K.pure` discharge.
  foldM-chain-2000 = foldMCount.value;

  # 2000-step slow-path bindP-per-descent chain. Result = the
  # `DArgBody`-edge count, which must equal 2000 after every arg
  # layer's bindP has wrapped the captured leaf error.
  foldWithPath-blame-chain-2000 = chainLength surfaced.value.__surfacedError;
}
