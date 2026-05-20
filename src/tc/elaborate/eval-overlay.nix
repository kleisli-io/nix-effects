# Meta-aware overlay evaluator.
#
# Reuses the kernel `mkValueF` parameterized over a dispatch algebra
# (`tc/eval/core.nix`), substituting meta-aware variants for the
# eliminators that may encounter a `VMeta` head — kernel-purity
# (`tc/elaborate/value.nix:13-17`) prevents the kernel itself from
# inspecting `VMeta` values.
#
# Use at elaboration sites that may invoke a closure on a VMeta
# argument (notably `insertImplicits` peeling implicit Pi binders
# and `sigmaFlatten` allocating a fresh first-component meta).
{ self, fx, api, ... }:

let
  E = fx.tc.eval;
  V = fx.tc.value;

  isVMeta = v:
    builtins.isAttrs v && (v ? _vTag) && v._vTag == "VMeta";

  extendVMeta = v: frame:
    v // { spine = v.spine ++ [ frame ]; };

  # Meta-aware dispatch table. `evalF` and `instantiateF` recurse
  # through `overlaySelf`, so closure bodies opened on a VMeta env
  # route every internal app/elim through the overlay's variants.
  overlaySelf = E.dispatch // {
    evalF = E.mkValueF overlaySelf;

    instantiateF = fuel: cl: arg:
      overlaySelf.evalF fuel ([ arg ] ++ cl.env) cl.body;

    vAppF = fuel: fn: arg:
      if isVMeta fn then extendVMeta fn (V.eApp arg)
      else if fn.tag == "VDescViewFn" then fn.apply arg
      else if fn.tag == "VLam" then overlaySelf.instantiateF fuel fn.closure arg
      else if fn.tag == "VNe" then V.vNe fn.level (fn.spine ++ [ (V.eApp arg) ])
      else throw "tc.overlay: vApp on non-function (tag=${fn.tag})";

    vBootSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
      if isVMeta scrut
      then extendVMeta scrut (V.eBootSumElim left right motive onLeft onRight)
      else if scrut.tag == "VBootInl" then overlaySelf.vAppF fuel onLeft scrut.val
      else if scrut.tag == "VBootInr" then overlaySelf.vAppF fuel onRight scrut.val
      else if scrut.tag == "VNe"
      then V.vNe scrut.level (scrut.spine ++ [ (V.eBootSumElim left right motive onLeft onRight) ])
      else throw "tc.overlay: vBootSumElim on non-bootstrap-sum (tag=${scrut.tag})";

    vSquashElimF = fuel: A: B: f: x:
      if isVMeta x then extendVMeta x (V.eSquashElim A B f)
      else if x.tag == "VSquashIntro" then overlaySelf.vAppF fuel f x.a
      else if x.tag == "VNe" then V.vNe x.level (x.spine ++ [ (V.eSquashElim A B f) ])
      else throw "tc.overlay: vSquashElim on non-Squash (tag=${x.tag})";

    # Remaining eliminators reuse the existing overlay versions from
    # `tc/elaborate/value.nix` — their signatures already match the
    # kernel's dispatch shape and they handle `VMeta` via spine
    # extension.
    vFst = self.elabFst;
    vSnd = self.elabSnd;
    vBootJ = self.elabBootJ;
    vLiftElimF = self.elabLiftElimF;
    vDescIndF = self.elabDescIndF;
    vInterpDF = self.elabInterpDF;
    vAllDF = self.elabAllDF;
    vEverywhereDF = self.elabEverywhereDF;
  };
in
{
  scope = {
    instantiateOverlayF = api.leaf {
      description = "instantiateOverlayF fuel cl arg: meta-aware closure instantiation. Where kernel `instantiateF` crashes when the closure environment contains a `VMeta` (kernel `vAppF` reads `.tag` which `VMeta` lacks), this overlay routes app/elim dispatch through `VMeta`-aware variants and threads overlay evaluation transitively through closure bodies.";
      signature = "instantiateOverlayF : Fuel -> Closure -> ElabVal -> ElabVal";
      value = overlaySelf.instantiateF;
    };

    instantiateOverlay = api.leaf {
      description = "instantiateOverlay: default-fuel wrapper around `instantiateOverlayF`.";
      signature = "instantiateOverlay : Closure -> ElabVal -> ElabVal";
      value = overlaySelf.instantiateF E.dispatch.defaultFuel;
    };

    evalOverlayF = api.leaf {
      description = "evalOverlayF fuel env tm: meta-aware kernel-term evaluator. Substitute for `evalF` at sites that may evaluate closure bodies whose environment contains `VMeta` values.";
      signature = "evalOverlayF : Fuel -> Env -> Tm -> ElabVal";
      value = overlaySelf.evalF;
    };

    evalOverlay = api.leaf {
      description = "evalOverlay: default-fuel wrapper around `evalOverlayF`.";
      signature = "evalOverlay : Env -> Tm -> ElabVal";
      value = overlaySelf.evalF E.dispatch.defaultFuel;
    };
  };
}
