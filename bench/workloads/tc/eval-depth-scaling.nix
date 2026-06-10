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
  terms = import ./eval-depth-terms.nix { inherit fx; };
  inherit (terms) H depths vAppElab descIndElab;
  Q = fx.src.tc.quote;

  # --- desc-ind chain (vDescIndF) ---
  # `decElim` against a constant-Nat motive maps `yes` to `zero`; forcing
  # `Q.nf` and comparing to the elaborated `zero` forces the full depth-n
  # step-induction spine.
  yesSentinel = Q.nf [ ] (H.elab H.zero);
  descIndAtDepth = n: (Q.nf [ ] (descIndElab n)) == yesSentinel;

  # --- vAppF chain ---
  # A fixed `Nat → Nat` identity reapplied n times; normalizing the spine fires
  # n `vAppF` redexes, one per layer, each O(1).
  vAppAtDepth = n: builtins.seq (Q.nf [ ] (vAppElab n)) "ok";

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
