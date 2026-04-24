# Diagnostic-walker workloads.
#
# The kernel's diagnostic layer (`fx.diag.error` / `fx.diag.pretty` /
# `fx.diag.hints`) ships with a stack-safety discipline: direct
# recursion up to depth 500, `builtins.genericClosure` beyond. The
# synthetic checks in `src/diag/**` validate correctness at 5000 deep;
# these workloads track the allocation cost of the same walkers so a
# regression in the fast/slow split (e.g. an accidental early switch
# to recursion, or loss of `builtins.seq` forcing on the slow path) is
# caught by the bench gate.
#
# A 5000-deep `nestUnder` chain is the canonical stress target from
# the kernel spec; all three workloads share it so alloc deltas are
# directly comparable. The chain is built inside the workload
# expression so the builder's allocation cost is included in the
# measurement — matching real use, where walkers run on errors
# produced during elaboration.
{ fx }:

let
  D = fx.src.diag.error;
  P = fx.src.diag.positions;
  Pr = fx.src.diag.pretty;
  H = fx.src.diag.hints;

  idxs = builtins.genList (x: x) 5000;

  # Leaf matches the (DArgSort, universe-mismatch) hint key so
  # `hints.resolve` has a real entry to find, not a null lookup.
  baseErr = D.mkKernelError {
    rule = "desc-arg";
    msg = "type mismatch";
    expected = { tag = "VU"; level = 0; };
    got = { tag = "VU"; level = 1; };
  };

  deepErr = builtins.foldl'
    (err: _: D.nestUnder P.DArgSort err)
    baseErr
    idxs;

in {
  # One-line pretty render of a 5000-deep chain. Exercises the
  # position-chain walker's fast (≤500) + slow (genericClosure) paths.
  pretty-one-line-5000 = builtins.stringLength (Pr.oneLine deepErr);

  # Multi-line indented render. Same chain, different formatter —
  # catches regressions specific to the indent/newline emission path.
  pretty-multi-line-5000 = builtins.stringLength (Pr.multiLine deepErr);

  # Hint resolution: walk to leaf position, classify detail, look up
  # `DArgSort::universe-mismatch` in the hints table. Returns a
  # non-null string for this chain, so the full resolution path runs.
  hint-resolve-5000 =
    let r = H.resolve deepErr;
    in if r == null then 0 else builtins.stringLength r;
}
