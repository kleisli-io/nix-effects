# Shared depth-scaling term builders: the alloc/cpu workload
# (eval-depth-scaling.nix) and the step axis (step-probes.nix) gate IDENTICAL terms.
{ fx }:
let
  H = fx.types.hoas;

  # vAppF — n sequential β-redexes. Type-annotated so `H.elab` takes the cheap
  # `ann` path, not `elabInfer`'s super-linear inference walk over the spine.
  idFn = H.ann (H.lam "x" H.nat (x: x)) (H.forall "_" H.nat (_: H.nat));
  vAppTerm = n:
    builtins.foldl' (acc: _: H.app idFn acc) H.zero (builtins.genList (i: i) n);
  vAppElab = n: H.elab (H.ann (vAppTerm n) H.nat);

  # desc-ind — `decideLeNat n n` walks the `ind` interior to depth n (the
  # vDescIndF hotspot); `decElim` against a constant motive collapses the NF.
  descIndProbe = n:
    let
      nv = H.natLit n;
      d = H.app (H.app H.decideLeNat nv) nv;
      P = H.le nv nv;
    in
    H.decElim P
      (H.lam "_" (H.dec P) (_: H.nat))
      (H.lam "_" P (_: H.zero))
      (H.lam "_" (H.not P) (_: H.succ H.zero))
      d;
  descIndElab = n: H.elab (descIndProbe n);
in
{
  inherit H idFn vAppTerm vAppElab descIndProbe descIndElab;
  depths = [ 10 100 1000 5000 10000 ];
}
