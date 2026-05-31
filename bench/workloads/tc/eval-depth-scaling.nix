# Depth-scaling sweep for the CEK evaluator's three recursive hotspots.
#
# The kernel evaluator was defunctionalized into a CEK abstract machine
# so that user-level recursion depth N consumes O(1) libnix call frames
# and O(1) Nix call-depth per step. This workload is the forward
# regression detector for that property: each chain drives one of the
# three migrated hotspots to a parameterized depth N, and the gate
# tracks the per-step heap-allocation cost. Depth-flatness shows up as
# alloc-count scaling LINEARLY in N; a regression that reintroduces
# super-linear work (or per-call driver allocation) trips the gate.
#
# Three chains, each N in {10, 100, 1000, 5000, 10000}:
#
#   * desc-ind — `decideLeNat n n` walks the `ind`-recursive interior
#     to depth n (the vDescIndF hotspot). The `decElim`-against-a-
#     constant-Nat motive collapses the proof to `zero`, so the forced
#     NF is tiny; the cost is the depth-n step-induction it took to get
#     there. Mirrors `tc.decidable.leDiag50`'s probe shape.
#   * vAppF — n sequential beta-reductions of a fixed arity-1 identity
#     (`((λx:Nat.x):Nat→Nat)` reapplied n times). Each NF step is one
#     `vAppF (VLam …) arg` redex, so the chain is exactly n vAppF calls.
#   * conv — checking an n-deep `Nat` literal. `checkHoas` walks the
#     n-deep desc-con chain and conv compares each successor's payload
#     against the elaborated `Nat` description. Mirrors
#     `tc.conv.identical-deep` (which is this chain pinned at n=5000).
#
# Tiered per depth in meta.nix: N≤1000 are `quick` (pre-commit),
# N=5000 is `standard`, N=10000 is `heavy` (merge/nightly only).
{ fx }:

let
  H = fx.types.hoas;
  Q = fx.src.tc.quote;

  depths = [ 10 100 1000 5000 10000 ];

  # --- desc-ind chain (vDescIndF) ---
  # `decElim` against a constant-Nat motive maps `yes` to `zero`;
  # forcing `Q.nf` and comparing to the elaborated `zero` forces the
  # full depth-n step-induction spine.
  yesSentinel = Q.nf [ ] (H.elab H.zero);
  descIndAtDepth = n:
    let
      nv = H.natLit n;
      d = H.app (H.app H.decideLeNat nv) nv;
      P = H.le nv nv;
      probe = H.decElim P
        (H.lam "_" (H.dec P) (_: H.nat))
        (H.lam "_" P (_: H.zero))
        (H.lam "_" (H.not P) (_: H.succ H.zero))
        d;
    in
    (Q.nf [ ] (H.elab probe)) == yesSentinel;

  # --- vAppF chain ---
  # A fixed `Nat → Nat` identity reapplied n times. Normalizing the
  # spine fires n `vAppF` redexes, one per layer, each O(1).
  #
  # The spine is annotated with its type so `H.elab`'s outer tag is `ann`,
  # not `app`. An `app`-headed term routes `H.elab` through the meta-aware
  # `elabInfer` inference walk (lower.nix:1493) — a recursive, super-linear
  # structural pass over the n-deep spine that is OUT OF SCOPE for the
  # evaluator (it lives in tc/elaborate, not tc/eval) and would dominate the
  # measurement, masking the vAppF depth-flatness this leaf exists to detect.
  # With the annotation, `H.elab` does the cheap iterative `lower` only, and
  # `Q.nf` measures the n defunctionalized vAppF beta-reductions.
  idFn = H.ann (H.lam "x" H.nat (x: x)) (H.forall "_" H.nat (_: H.nat));
  vAppAtDepth = n:
    let
      term = builtins.foldl' (acc: _: H.app idFn acc) H.zero
        (builtins.genList (i: i) n);
    in
    builtins.seq (Q.nf [ ] (H.elab (H.ann term H.nat))) "ok";

  # --- conv chain ---
  # Checking an n-deep `Nat` literal walks per-level conv against the
  # elaborated `Nat` description.
  convAtDepth = n: (H.checkHoas H.nat (H.natLit n)).tag;

  forDepths = f: builtins.listToAttrs
    (map (n: { name = "n${toString n}"; value = f n; }) depths);

in
{
  desc-ind = forDepths descIndAtDepth;
  vAppF = forDepths vAppAtDepth;
  conv = forDepths convAtDepth;
}
