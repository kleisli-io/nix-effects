# Closes UShortHand morphisms under `composeHandlers` by direct Val
# construction. The functor diagram (`shortcut` of compose = compose of
# `shortcut`) commutes by construction; soundness is anchored kernel-
# side by `composeHandlersInl/InrLemma` + per-effect uniform-shortcut
# lemmas. Returns `null` on unknown ops to fall back to the kernel path.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  Extract = fx.experimental.desc-interp.extract;
  C = fx.experimental.desc-interp.compose;

  # `respHoas` is the ι-reduced response type at the canonical inner op
  # (`S_A` for state-get, `H.unit` for state-put/error-collecting-raise,
  # `H.void` for error-strict/result-raise). Composed atType factories
  # precompute a tag-keyed table once per instantiation.
  mkComposedMeta = { SigmaSHoas, A, respHoas }:
    let
      leftSigHoas = H.sigma "_r" respHoas (_: SigmaSHoas);
      rightSigHoas = H.sigma "_a" A (_: SigmaSHoas);
    in
    {
      leftSigVal = fx.tc.eval.eval [ ] (H.elab leftSigHoas);
      rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
      sumDescVal = Extract.sumDescValOf leftSigHoas rightSigHoas;
    };

  # `H_short_X : op → stateVal → UniRetVal | null` are UShortHand morphisms
  # (e.g. state's `handlerShortcut` or error's `uniformOfShort{,At}`).
  # `metaFor` returns `null` for unknown inner ops, triggering kernel
  # fallback at this step.
  composedHandlerShortcut = H_short_A: H_short_B: metaFor:
    op: stateVal:
      let
        side = op._side or null;
        innerOp = op._inner or null;
      in
      if side == null || innerOp == null then null
      else
        let
          isLeft = side == "composed-inl";
          isRight = side == "composed-inr";
        in
        if !(isLeft || isRight) then null
        else
          let
            s_A = Extract.extract (Extract.Project "fst" stateVal);
            s_B = Extract.extract (Extract.Project "snd" stateVal);
            subRet =
              if isLeft then H_short_A innerOp s_A
              else H_short_B innerOp s_B;
          in
          if subRet == null then null
          else
            let md = metaFor op; in
            if md == null then null
            else
              Extract.extract (Extract.OfElim subRet
                (pair_rs:
                  let
                    repackedState =
                      if isLeft
                      then Extract.extract (Extract.PairRaw pair_rs.snd s_B)
                      else Extract.extract (Extract.PairRaw s_A pair_rs.snd);
                  in
                  Extract.extract (Extract.Resume
                    md.sumDescVal
                    md.leftSigVal
                    md.rightSigVal
                    pair_rs.fst
                    repackedState))
                (pair_as:
                  let
                    repackedState =
                      if isLeft
                      then Extract.extract (Extract.PairRaw pair_as.snd s_B)
                      else Extract.extract (Extract.PairRaw s_A pair_as.snd);
                  in
                  Extract.extract (Extract.Abort
                    md.sumDescVal
                    md.leftSigVal
                    md.rightSigVal
                    pair_as.fst
                    repackedState)));

  # `_side`/`_inner` sidecars survive `K.send`'s `impureCon` wrap and
  # are ignored by `H.elab`.
  composedInl = Op_A: Op_B: subOp:
    (HI.inlAtExplicit H.levelZero Op_A Op_B subOp) // { _side = "composed-inl"; _inner = subOp; };
  composedInr = Op_A: Op_B: subOp:
    (HI.inrAtExplicit H.levelZero Op_A Op_B subOp) // { _side = "composed-inr"; _inner = subOp; };

in
{
  scope = {
    "composed-shortcut" = api.namespace {
      description = "fx.experimental.desc-interp.composed-shortcut: closes per-effect UShortHand shortcuts under `composeHandlers`. `composedHandlerShortcut` mirrors `eval (composeHandlers … opVal stateVal)` by direct Val construction; `composedInl`/`composedInr` are HOAS smart constructors threading `_side`/`_inner` sidecars for shortcut dispatch.";
      doc = ''
        Pipeline per Impure step on a composed op: read `op._side` /
        `op._inner`, project the composed state with `extract.Project`,
        recurse via the matching per-side shortcut, then `extract.OfElim`
        on the sub-UniRet — Resume → composed Resume; Abort → composed
        Abort — repacking the sibling state slot via `extract.PairRaw`.

        Soundness: kernel-side `composedHandlerShortcutLemma`
        (`composed-shortcut-laws.nix`) chains `composeHandlersInl/InrLemma`
        with per-effect uniform-shortcut lemmas; emitter-side, the
        `_self.tests` below conv-check kernel-composed vs shortcut-emitted
        Vals at concrete canonical ops.
      '';
      tests = {
        # inl branch with state's UniRet-direct `handlerShortcut`.
        "composedHandlerShortcut-state-get-inl-conv-eq-kernel-path" = {
          expr =
            let
              State = fx.experimental.desc-interp.effects.state;
              Error = fx.experimental.desc-interp.effects.error;
              S_A = H.nat;
              E = H.string;
              S_B = H.listOf E;
              A = H.nat;
              Op_A = H.app State.EffState.T S_A;
              Op_B = H.app Error.EffError.T E;
              Resp_A = H.app State.Resp_State S_A;
              Resp_B = H.app Error.Resp_collecting E;
              SigmaSHoas = H.sigma "_sA" S_A (_: S_B);

              H_A_HOAS = H.app (H.app State.handle_State S_A) A;
              H_B_HOAS = H.app (H.app Error.uniformOf_collecting E) A;

              kernelHandler =
                H.app
                  (H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app (H.app C.composeHandlers S_A) S_B)
                              Op_A)
                            Op_B)
                          Resp_A)
                        Resp_B)
                      A)
                    H_A_HOAS)
                  H_B_HOAS;

              taggedGet = (State.getAt S_A)
                // { _opTag = "state-get"; };
              composedOp = composedInl Op_A Op_B taggedGet;
              composedState = H.pair (H.succ H.zero) (HI.nilAtExplicit E);

              kernelOut = H.app (H.app kernelHandler composedOp) composedState;
              kernelVal = fx.tc.eval.eval [ ] (H.elab kernelOut);

              stateAt = State.atType S_A A;
              errorAt = Error.atType_collecting E;
              H_short_A = stateAt.handlerShortcut;
              H_short_B = errorAt.uniformOfShortAt A;

              metaFor = op:
                let innerTag = op._inner._opTag or null; in
                if (op._side or null) == "composed-inl"
                  && innerTag == "state-get"
                then
                  mkComposedMeta
                    {
                      inherit SigmaSHoas A;
                      respHoas = S_A;
                    }
                else null;

              shortFn = composedHandlerShortcut H_short_A H_short_B metaFor;
              composedStateVal = fx.tc.eval.eval [ ] (H.elab composedState);
              shortVal = shortFn composedOp composedStateVal;
            in
            fx.tc.conv.conv 0 kernelVal shortVal;
          expected = true;
        };

        # inr branch through error-collecting's `uniformOfShortAt` lift
        # (PairRaw → Resume).
        "composedHandlerShortcut-error-collecting-inr-conv-eq-kernel-path" = {
          expr =
            let
              State = fx.experimental.desc-interp.effects.state;
              Error = fx.experimental.desc-interp.effects.error;
              S_A = H.nat;
              E = H.string;
              S_B = H.listOf E;
              A = H.nat;
              Op_A = H.app State.EffState.T S_A;
              Op_B = H.app Error.EffError.T E;
              Resp_A = H.app State.Resp_State S_A;
              Resp_B = H.app Error.Resp_collecting E;
              SigmaSHoas = H.sigma "_sA" S_A (_: S_B);

              H_A_HOAS = H.app (H.app State.handle_State S_A) A;
              H_B_HOAS = H.app (H.app Error.uniformOf_collecting E) A;

              kernelHandler =
                H.app
                  (H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app (H.app C.composeHandlers S_A) S_B)
                              Op_A)
                            Op_B)
                          Resp_A)
                        Resp_B)
                      A)
                    H_A_HOAS)
                  H_B_HOAS;

              taggedRaise =
                (H.app (H.app Error.EffError.error E) (H.stringLit "boom"))
                // { _opTag = "error-raise"; };
              composedOp = composedInr Op_A Op_B taggedRaise;
              composedState = H.pair H.zero (HI.nilAtExplicit E);

              kernelOut = H.app (H.app kernelHandler composedOp) composedState;
              kernelVal = fx.tc.eval.eval [ ] (H.elab kernelOut);

              stateAt = State.atType S_A A;
              errorAt = Error.atType_collecting E;
              H_short_A = stateAt.handlerShortcut;
              H_short_B = errorAt.uniformOfShortAt A;

              metaFor = op:
                let innerTag = op._inner._opTag or null; in
                if (op._side or null) == "composed-inr"
                  && innerTag == "error-raise"
                then
                  mkComposedMeta
                    {
                      inherit SigmaSHoas A;
                      respHoas = H.unit;
                    }
                else null;

              shortFn = composedHandlerShortcut H_short_A H_short_B metaFor;
              composedStateVal = fx.tc.eval.eval [ ] (H.elab composedState);
              shortVal = shortFn composedOp composedStateVal;
            in
            fx.tc.conv.conv 0 kernelVal shortVal;
          expected = true;
        };
      };

      value = {
        composedHandlerShortcut = api.leaf {
          value = composedHandlerShortcut;
          description = "composedHandlerShortcut H_short_A H_short_B metaFor op stateVal — composed UniRet Val mirroring `eval (composeHandlers … H_A H_B opVal stateVal)`. `op` carries `_side`/`_inner` sidecars from `composedInl`/`composedInr`; `metaFor` is the composed-UniRet metadata lookup keyed by inner-op tag; per-side shortcuts must return UniRet Vals. `null` propagates from any of the inputs (kernel fallback).";
        };
        composedInl = api.leaf {
          value = composedInl;
          description = "composedInl Op_A Op_B subOp — `H.inl Op_A Op_B subOp` with `_side = \"composed-inl\"`, `_inner = subOp`. Sidecars are ignored by elab and survive `K.send`'s `impureCon` wrap.";
        };
        composedInr = api.leaf {
          value = composedInr;
          description = "composedInr Op_A Op_B subOp — `H.inr` counterpart of `composedInl`.";
        };
        mkComposedMeta = api.leaf {
          value = mkComposedMeta;
          description = "mkComposedMeta { SigmaSHoas; A; respHoas; } — precompute `{ sumDescVal; leftSigVal; rightSigVal; }` for the composed UniRet at one canonical inner op (response type already ι-reduced).";
        };
      };
    };
  };
}
