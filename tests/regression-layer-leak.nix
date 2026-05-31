# Regression: `VLazyDescIndAccLayer` must not leak into observable Val
# sub-fields.
#
# The CEK driver maintains a three-layer invariant that makes layers
# unreachable from external observers:
#
#   1. `machine.nix:1116-1128` (`stepIf` Done-transform): on every
#      `runMachineAtF` exit, if the returned outer Val is a layer it is
#      force-cascaded via the kont stack before the driver exits Done.
#   2. `machine.nix:142-171` (`ev`'s tier-3 dispatch): every eliminator /
#      desc-ind family Tm routes through `self.evalF = runMachineF`, so
#      any sub-Tm whose evaluation could produce a layer inherits (1).
#   3. `datatype.nix:880-936` (`dispatchStep`): every user-step `ih` arg
#      is wrapped as `fst_ (snd_ … payloadIH)` — a tier-3 chain that
#      forces through (2) before binding into the step's closure env.
#
# Together: a step body of any shape — embedding `ih` directly in a pair,
# round-tripping through `lower (lift ih)`, capturing `ih` in a sum-elim
# closure, etc. — observes `ih` as a forced concrete Val, never as a raw
# layer. Conversely, if any of (1)-(3) breaks in a future refactor, the
# adversarial step bodies below will surface the regression as a
# `false` from `conv` (silent wrong result, not a throw — soundness
# defect at the type-checking level).
#
# Provenance: Phase 1 reproducers (v1-v5) from task
# `2026-05-20-defunctionalize-kernel-evaluator-cek`. Each step shape
# corresponds to an audit-flagged consumer in `core.nix:441-577`.
{ lib, fx }:

let
  H = fx.tc.hoas;
  E = fx.tc.eval;
  C = fx.tc.conv;

  inherit (H) lam ind nat zero succ sigma pair fst_ snd_ tt unit let_
    levelZero levelSuc;
  inherit (H._internal) bootSum bootInl bootSumElim;
  inherit (H._internal._indexed) liftAt lowerAt;

  natOf = n: builtins.foldl' (acc: _: succ acc) zero (builtins.genList (i: i) n);
  motiveTy = sigma "_a" nat (_: unit);
  motive   = lam "_n" nat (_: motiveTy);
  baseV    = pair zero tt;

  evalAtK = step: K:
    E.eval [ ] (H.elab (ind 0 motive baseV step (natOf K)));

  # Step shapes matching the audit-flagged consumer patterns.
  variants = {
    # Audit literal: `Pair ihM np` embedding ih in the result.
    # Targets vFst consumer on the resulting VPair.fst.
    pairIhNp = lam "np" nat (np:
      lam "ih" motiveTy (ih:
        pair ih np));

    # Alternate projection: `Pair np (snd_ ih)`.
    # Targets vFst/vSnd dispatch on a ih-derived sub-field.
    pairNpSndIh = lam "np" nat (np:
      lam "ih" motiveTy (ih:
        pair np (snd_ ih)));

    # let-aliased ih embedded — defeats any aliasing-based shortcut
    # in conv or in the binder dispatch path.
    letAliasIh = lam "np" nat (np:
      lam "ih" motiveTy (ih:
        let_ "alias" motiveTy ih (alias: pair alias np)));

    # Identity step: chain machinery fires through K layers; baseV
    # propagates upward. Enables cross-path conv vs the direct literal.
    identity = lam "np" nat (_: lam "ih" motiveTy (ih: ih));

    # Silent-propagation case (audit Table 1): vLiftIntroF and
    # vLiftElimF wrap a layer rather than throwing. Step body
    # round-trips ih through lift / lower at distinct levels (l ≠ m
    # required to defeat the sameLevelSyntax shortcut).
    liftRoundTrip = lam "np" nat (np:
      lam "ih" motiveTy (ih:
        pair (lowerAt levelZero (levelSuc levelZero) motiveTy
                (liftAt levelZero (levelSuc levelZero) motiveTy ih)) np));

    # Silent-propagation case (audit Table 1): vBootSumElimF
    # dispatches scrut only. Captures ih in onLeft/onRight closures;
    # scrut commits to inl → onLeft VLam applied to vTt → its body
    # reads ih from the outer step's env.
    bootSumCapture = lam "np" nat (np:
      lam "ih" motiveTy (ih:
        let scrut = bootInl unit unit tt; in
        pair (bootSumElim unit unit
                (lam "_s" (bootSum unit unit) (_: motiveTy))
                (lam "_x" unit (_: ih))
                (lam "_x" unit (_: ih))
                scrut) np));
  };

  K = 20;

  # A step body has no layer leak iff:
  #   (a) the outer Val is not a layer (stepIf Done-transform held);
  #   (b) the outer VPair's .fst is not a layer (tier-3 routing forced
  #       it before binding into the result ctor);
  #   (c) self-conv returns true (no path inside conv triggers the
  #       §6.5 catch-all `false` on a layer);
  #   (d) cross-copy conv returns true (defeats thunk-identity
  #       shortcuts; the two Vals are separately evaluated).
  noLeak = step:
    let v1 = evalAtK step K;
        v2 = evalAtK step K;
    in v1.tag != "VLazyDescIndAccLayer"
       && (v1.fst.tag or "no-fst") != "VLazyDescIndAccLayer"
       && C.conv 0 v1 v1
       && C.conv 0 v1 v2;

  # Cross-path: identity step at K=N produces a Val that, after the
  # cascade unwinds all K layers, is structurally baseV. If any layer
  # leaked into the cascade's terminal Val, conv against the direct
  # baseV literal would silently return false.
  crossPath_identityVsLiteral =
    let v_chain   = evalAtK variants.identity K;
        v_literal = E.eval [ ] (H.elab baseV);
    in C.conv 0 v_chain v_literal
       && C.conv 0 v_literal v_chain;
in
{
  noLeak_pairIhNp        = noLeak variants.pairIhNp;
  noLeak_pairNpSndIh     = noLeak variants.pairNpSndIh;
  noLeak_letAliasIh      = noLeak variants.letAliasIh;
  noLeak_identity        = noLeak variants.identity;
  noLeak_liftRoundTrip   = noLeak variants.liftRoundTrip;
  noLeak_bootSumCapture  = noLeak variants.bootSumCapture;
  inherit crossPath_identityVsLiteral;
}
