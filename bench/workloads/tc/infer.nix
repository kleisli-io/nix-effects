# Infer-dominated whole-pipeline workloads.
#
# `inferHoas` exits the bidirectional check loop on the synthesise
# side: every `app` node is an `infer` site, so a deep app-spine
# stresses the infer path more than any other shape.
{ fx }:

let
  H = fx.types.hoas;

  # n-ary nat-consumer: `Π(_:Nat). Π(_:Nat). … Π(_:Nat). Nat`. Saturated
  # application requires `n` `H.zero` arguments and the spine inference
  # walks the codomain at every frame.
  natFunTy = n:
    builtins.foldl' (acc: _: H.forall "_" H.nat (_: acc)) H.nat
      (builtins.genList (x: x) n);

  natFunBody = n:
    builtins.foldl' (acc: _: H.lam "_" H.nat (_: acc)) H.zero
      (builtins.genList (x: x) n);

  # n-ary application of an `ann`-wrapped n-ary function to `n` zeros.
  # `ann` pins a Pi type the kernel can infer at the head; each app
  # frame above forces an inferer step against the head's codomain.
  deepAppSpine = n:
    let head = H.ann (natFunBody n) (natFunTy n);
    in builtins.foldl' (acc: _: H.app acc H.zero) head
         (builtins.genList (x: x) n);

in {
  # 100-frame saturated app spine. The inferred top-level type is
  # `Nat`; the inference walk traverses all 100 app frames, popping a
  # `Pi` codomain at each level.
  deep-app-100 = (H.inferHoas (deepAppSpine 100)).type.tag;
}
