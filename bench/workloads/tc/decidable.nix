# Decidability-witness throughput.
#
# Closed kernel `decideLeNat` is a `lam`-bound recursive term: applied
# at `(zero, x)` it bottoms out in the base case after a single `ind`
# step and emits `yes (le zero x) (leZ x)`. Each call is therefore
# constant-cost at the value level; the workload's expense is dominated
# by elaboration of the closed term (re-resolved at each `H.app`) and
# the per-call NF traversal performed by `Q.nf`. Useful as a smoke /
# regression sentinel for the proof-bearing-kernel-terms surface.
#
# Two scales:
#   * leRange1000 — 1001 base-case evaluations against `decideLeNat`.
#     Stresses the surface combinator's repeated elaboration cost
#     without exercising deep `ind` recursion.
#   * leDiag50   — 51 evaluations of `decideLeNat n n`, walking the
#     `ind`-recursive path through both `m` and `n` up to depth 50.
#     Exercises the full step-induction interior alongside the
#     `decElim`-on-inner-IH lift through `leSS` / `leInjSS`.
{ fx }:

let
  H = fx.types.hoas;
  Q = fx.src.tc.quote;

  # NF-equality probe: `decElim` against a constant-Nat motive maps yes
  # to `zero` and no to `succ zero`. Forcing `Q.nf` on both sides and
  # comparing for equality forces the full spine of the elaborated term
  # — the same forcing the inline test corpus performs, transplanted
  # here as a bench-time workload.
  yesSentinel = Q.nf [] (H.elab H.zero);
  noSentinel  = Q.nf [] (H.elab (H.succ H.zero));

  probeAtZero = n:
    let nv = H.natLit n;
        d = H.app (H.app H.decideLeNat H.zero) nv;
        P = H.le H.zero nv;
        probe = H.decElim P
                  (H.lam "_" (H.dec P) (_: H.nat))
                  (H.lam "_" P (_: H.zero))
                  (H.lam "_" (H.not P) (_: H.succ H.zero))
                  d;
        nf = Q.nf [] (H.elab probe);
    in nf == yesSentinel;

  probeAtDiag = n:
    let nv = H.natLit n;
        d = H.app (H.app H.decideLeNat nv) nv;
        P = H.le nv nv;
        probe = H.decElim P
                  (H.lam "_" (H.dec P) (_: H.nat))
                  (H.lam "_" P (_: H.zero))
                  (H.lam "_" (H.not P) (_: H.succ H.zero))
                  d;
        nf = Q.nf [] (H.elab probe);
    in nf == yesSentinel;

in {
  leRange1000 =
    let results = builtins.genList probeAtZero 1001;
        allYes  = builtins.all (b: b) results;
    in if allYes then 1001 else 0;

  leDiag50 =
    let results = builtins.genList probeAtDiag 51;
        allYes  = builtins.all (b: b) results;
    in if allYes then 51 else 0;
}
