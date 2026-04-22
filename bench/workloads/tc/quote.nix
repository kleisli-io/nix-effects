# Quote-dominated whole-pipeline checks.
#
# `fx.tc.quote.nf` — the kernel-internal value-to-Tm normaliser — is
# not exposed through the public surface. The closest public proxies
# that exercise quote-style traversal are `verifyAndExtract` (which
# walks a kernel Val tree to produce a Nix value) and `reifyType`
# (which walks a kernel type Val to produce an HOAS tree). Both share
# the structural walk-the-tree cost the quote path bears, so
# regressions on either track regressions on quote even though the
# module under measurement is not literally `quote.nf`.
#
# A stuck-VNe-rooted workload (vDescElim applied to a VNe head) has
# no public route — constructing a stuck VNe requires direct access
# to the Val constructors. The `stuck` workload below substitutes a
# reify-on-deep-Pi case that walks the type-Val tree without
# extraction; same recursive-walk cost path, different leaf
# operation.
{ fx }:

let
  H = fx.types.hoas;
  T = fx.types;

  natToNat = H.forall "_" H.nat (_: H.nat);

  # Build a 20-deep nested Pi `Π(_:Nat). Π(_:Nat). … Π(_:Nat). Nat` and
  # a constant lambda inhabiting it. `inferHoas (ann lam pi)` returns
  # `{ term; type = <VPi spine>; }`; the type slot is the Val we feed
  # into reifyType, mirroring the recursion quote performs over its
  # own value trees.
  deepPi = builtins.foldl'
    (acc: _: H.forall "_" H.nat (_: acc))
    H.nat
    (builtins.genList (x: x) 20);

  deepLam = builtins.foldl'
    (acc: _: H.lam "_" H.nat (_: acc))
    H.zero
    (builtins.genList (x: x) 20);

in {
  # Closed VMu walk: `succ^100 zero` extracted to integer `100`. The
  # extractInner Nat branch (src/tc/elaborate/extract.nix) trampolines
  # through a 100-deep VDescCon chain via `genericClosure` — a
  # quote-shaped traversal of the entire value tree.
  closed = T.verifyAndExtract H.nat (H.natLit 100);

  # Opaque-lambda extract: an opaque-bound identity at `Nat → Nat`.
  # The extract path for VOpaqueLam returns the wrapped Nix function
  # without recursive walking, so this workload measures the
  # check + eval surface around the opaque trust boundary, anchoring
  # the closed/stuck deltas against an open-leaf cost floor.
  # `verifyAndExtract` returns a Nix function (opaque lambdas pass
  # through verbatim) which is not JSON-serialisable; sentinelling
  # via `seq` keeps the workload value forceable by the bench
  # harness while still committing to evaluation of the extract.
  open =
    let extracted = T.verifyAndExtract natToNat
                      (H.opaqueLam (x: x) natToNat);
    in builtins.seq extracted "extracted-opaque-lambda";

  # Reify a 20-deep VPi back to an HOAS tree. `reifyType` recurses
  # through the type Val exactly as quote recurses through its term
  # tree; forcing `_htag` commits the outer reify, with children
  # remaining lazy as in quote's own normalisation. The deep Pi
  # supplies the recursive depth without invoking any datatype
  # eliminator, isolating the recursive walk from constructor work.
  stuck =
    let inf = H.inferHoas (H.ann deepLam deepPi);
    in (T.reifyType inf.type)._htag;
}
