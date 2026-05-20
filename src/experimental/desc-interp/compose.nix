# Universal handler-result type for kernel-resident handler composition.
#
# `UniRet S Op Resp op A` ≜
#     Sum (Σ _r:(Resp op), S)     -- Left  = resume (response + new state)
#         (Σ _a:A,         S)     -- Right = abort  (final value + new state)
#
# Per-effect handlers re-shaped into this form feed `composeHandlers`,
# which threads a product state slot `Σ StateA StateB` and dispatches on
# Sum-tagged ops. State's `handle_StateTy` (`effects/state.nix:44-51`)
# already has this shape verbatim — see the inline conv test below.
#
# `Op` and `op` are separate binders because `Resp : Op → U` needs the
# carrier universe `Op : U`, and the smart-constructor return type
# `UniRet S Op Resp op A` needs the specific value `op : Op` for
# `Resp op` to be the response type. Resulting signature:
#
#   UniRet : Π (S:U) (Op:U) (Resp:Op→U) (op:Op) (A:U). U
#
# Ref: Plotkin & Pretnar (2009) Handlers of Algebraic Effects §3 for
# the resume/abort encoding.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;

  UniRetTy =
    H.forall "S" (H.u 0) (_S:
      H.forall "Op" (H.u 0) (Op:
        H.forall "Resp" (H.forall "_o" Op (_: H.u 0)) (_Resp:
          H.forall "op" Op (_op:
            H.forall "A" (H.u 0) (_A:
              H.u 0)))));

  # `H.ann`-wrapped so kernel inference recovers UniRet's type at use
  # sites (the uniRetAt spine in mkResume/mkAbort's return-type slot
  # would otherwise have no annotation to pick up).
  UniRet = H.ann
    (H.lam "S" (H.u 0) (S:
      H.lam "Op" (H.u 0) (Op:
        H.lam "Resp" (H.forall "_o" Op (_: H.u 0)) (Resp:
          H.lam "op" Op (op:
            H.lam "A" (H.u 0) (A:
              H.sum
                (H.sigma "_r" (H.app Resp op) (_r: S))
                (H.sigma "_a" A (_a: S))))))))
    UniRetTy;

  # Fully-applied UniRet spine; returns a type.
  uniRetAt = S: Op: Resp: op: A:
    H.app (H.app (H.app (H.app (H.app UniRet S) Op) Resp) op) A;

  # Sigma skeletons shared by mkResume / mkAbort and the conv tests.
  leftFor = S: Resp: op: H.sigma "_r" (H.app Resp op) (_r: S);
  rightFor = S: A: H.sigma "_a" A (_a: S);
  inlBase = HI.inlAtExplicit H.levelZero;
  inrBase = HI.inrAtExplicit H.levelZero;

  mkResumeTy =
    H.forall "S" (H.u 0) (S:
      H.forall "Op" (H.u 0) (Op:
        H.forall "Resp" (H.forall "_o" Op (_: H.u 0)) (Resp:
          H.forall "op" Op (op:
            H.forall "A" (H.u 0) (A:
              H.forall "r" (H.app Resp op) (_r:
                H.forall "s" S (_s:
                  uniRetAt S Op Resp op A)))))));

  mkResume = H.ann
    (H.lam "S" (H.u 0) (S:
      H.lam "Op" (H.u 0) (Op:
        H.lam "Resp" (H.forall "_o" Op (_: H.u 0)) (Resp:
          H.lam "op" Op (op:
              H.lam "A" (H.u 0) (A:
                H.lam "r" (H.app Resp op) (r:
                  H.lam "s" S (s:
                    inlBase (leftFor S Resp op) (rightFor S A) (H.pair r s)))))))))
    mkResumeTy;

  mkAbortTy =
    H.forall "S" (H.u 0) (S:
      H.forall "Op" (H.u 0) (Op:
        H.forall "Resp" (H.forall "_o" Op (_: H.u 0)) (Resp:
          H.forall "op" Op (op:
            H.forall "A" (H.u 0) (A:
              H.forall "a" A (_a:
                H.forall "s" S (_s:
                  uniRetAt S Op Resp op A)))))));

  mkAbort = H.ann
    (H.lam "S" (H.u 0) (S:
      H.lam "Op" (H.u 0) (Op:
        H.lam "Resp" (H.forall "_o" Op (_: H.u 0)) (Resp:
          H.lam "op" Op (op:
              H.lam "A" (H.u 0) (A:
                H.lam "a" A (a:
                  H.lam "s" S (s:
                    inrBase (leftFor S Resp op) (rightFor S A) (H.pair a s)))))))))
    mkAbortTy;

  # Fully-applied smart-constructor spines; consumers avoid hand-rolling
  # the 7-arg apps. Match `uniRetAt`'s naming.
  mkResumeAt = S: Op: Resp: op: A: r: s:
    H.app (H.app (H.app (H.app (H.app (H.app (H.app mkResume S) Op) Resp) op) A) r) s;
  mkAbortAt = S: Op: Resp: op: A: a: s:
    H.app (H.app (H.app (H.app (H.app (H.app (H.app mkAbort S) Op) Resp) op) A) a) s;

  # Composed response family: `Resp_AB op = case op of inl opA → Resp_A opA
  # | inr opB → Resp_B opB`. Iota fires on canonical `inl`/`inr`, so
  # `composedResp Op_A Op_B Resp_A Resp_B (inl Op_A Op_B opA) ≡ Resp_A opA`
  # by conv — exactly what `mkResume`'s `r`-argument needs in the
  # composeHandlers left branch.
  composedRespTy =
    H.forall "Op_A" (H.u 0) (Op_A:
      H.forall "Op_B" (H.u 0) (Op_B:
        H.forall "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (_Resp_A:
          H.forall "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (_Resp_B:
            H.forall "op" (H.sum Op_A Op_B) (_op:
              H.u 0)))));

  # sumElim's `k` is the level of the motive's codomain. Here the motive
  # body is `H.u 0` (the type former U₀), which itself lives at U₁ —
  # hence `k = 1`. The composeHandlers sumElims below use `k = 0`
  # because their motive bodies are Π/Σ-types at U₀.
  composedResp = H.ann
    (H.lam "Op_A" (H.u 0) (Op_A:
      H.lam "Op_B" (H.u 0) (Op_B:
        H.lam "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (Resp_A:
          H.lam "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (Resp_B:
            H.lam "op" (H.sum Op_A Op_B) (op:
              H.sumElim 1
                Op_A
                Op_B
                (H.lam "_op" (H.sum Op_A Op_B) (_op: H.u 0))
                (H.lam "opA" Op_A (opA: H.app Resp_A opA))
                (H.lam "opB" Op_B (opB: H.app Resp_B opB))
                op))))))
    composedRespTy;

  # Nix-side spine helper; result has type `Π op:(Sum Op_A Op_B). U 0`.
  composedRespAt = Op_A: Op_B: Resp_A: Resp_B:
    H.app (H.app (H.app (H.app composedResp Op_A) Op_B) Resp_A) Resp_B;

  # composeHandlers takes two UniRet-shaped handlers (one per sub-effect),
  # threads a product state `Σ S_A S_B`, dispatches on `op : Sum Op_A
  # Op_B`, and re-packages the per-effect UniRet result back into the
  # composed UniRet shape. The composed-law witness lifts per-effect
  # laws through this shape.
  #
  # Type-parameter order: S, Op, Resp pairs first (varies least across
  # call sites — typically fixed by the effect modules), then A (the
  # program-return type), then the handler arguments. Partial application
  # to `(S_A S_B Op_A Op_B Resp_A Resp_B A)` yields a 2-arg combinator
  # `(H_A, H_B) → composedHandler`.
  composeHandlersTy =
    H.forall "S_A" (H.u 0) (S_A:
      H.forall "S_B" (H.u 0) (S_B:
        H.forall "Op_A" (H.u 0) (Op_A:
          H.forall "Op_B" (H.u 0) (Op_B:
            H.forall "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (Resp_A:
              H.forall "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (Resp_B:
                H.forall "A" (H.u 0) (A:
                  H.forall "H_A"
                    (H.forall "op" Op_A (op:
                      H.forall "_s" S_A (_s:
                        uniRetAt S_A Op_A Resp_A op A)))
                    (_H_A:
                      H.forall "H_B"
                        (H.forall "op" Op_B (op:
                          H.forall "_s" S_B (_s:
                            uniRetAt S_B Op_B Resp_B op A)))
                        (_H_B:
                          H.forall "op" (H.sum Op_A Op_B) (op:
                            H.forall "_s" (H.sigma "_sA" S_A (_: S_B)) (_s:
                              uniRetAt
                                (H.sigma "_sA" S_A (_: S_B))
                                (H.sum Op_A Op_B)
                                (composedRespAt Op_A Op_B Resp_A Resp_B)
                                op
                                A)))))))))));

  composeHandlers = H.ann
    (H.lam "S_A" (H.u 0) (S_A:
      H.lam "S_B" (H.u 0) (S_B:
        H.lam "Op_A" (H.u 0) (Op_A:
          H.lam "Op_B" (H.u 0) (Op_B:
            H.lam "Resp_A" (H.forall "_o" Op_A (_: H.u 0)) (Resp_A:
              H.lam "Resp_B" (H.forall "_o" Op_B (_: H.u 0)) (Resp_B:
                H.lam "A" (H.u 0) (A:
                  H.lam "H_A"
                    (H.forall "op" Op_A (op:
                      H.forall "_s" S_A (_s:
                        uniRetAt S_A Op_A Resp_A op A)))
                    (H_A:
                      H.lam "H_B"
                        (H.forall "op" Op_B (op:
                          H.forall "_s" S_B (_s:
                            uniRetAt S_B Op_B Resp_B op A)))
                        (H_B:
                          let
                            SigmaS = H.sigma "_sA" S_A (_: S_B);
                            SumOp = H.sum Op_A Op_B;
                            RespC = composedRespAt Op_A Op_B Resp_A Resp_B;

                            # Outer motive (over `op:Sum Op_A Op_B`): `UniRet (Σ S_A S_B)
                            # (Sum Op_A Op_B) RespC op A`. `_s` is bound at the outer
                            # `H.lam "_s"`, so the per-side branches receive it via
                            # closure and return UniRet directly — no Π over `_s` here.
                            outerMotive = H.lam "_op" SumOp (_op:
                              uniRetAt SigmaS SumOp RespC _op A);

                            # Per-side branch: project state slot, run the sub-handler, then
                            # `sumElim` on the UniRet result to re-package into the composed
                            # UniRet. `composedOp` is the canonical sum injection; `RespC
                            # composedOp` reduces to `Resp_A opA` (resp. `Resp_B opB`) by
                            # iota, making the `mkResume` r-arg well-typed.
                            dispatchSide = isLeft: subOp: _s:
                              let
                                s_A = H.fst_ _s;
                                s_B = H.snd_ _s;
                                subS = if isLeft then S_A else S_B;
                                subResp = if isLeft then Resp_A else Resp_B;
                                subH = if isLeft then H_A else H_B;
                                r = H.app (H.app subH subOp) (if isLeft then s_A else s_B);
                                composedOp =
                                  if isLeft
                                  then inlBase Op_A Op_B subOp
                                  else inrBase Op_A Op_B subOp;
                                # State re-pack: left handler updates s_A slot, right
                                # handler updates s_B slot. `newSubS` is the new sub-state
                                # extracted from r's payload sigma.
                                repack = newSubS:
                                  if isLeft then H.pair newSubS s_B else H.pair s_A newSubS;
                                leftForInner = H.sigma "_r" (H.app subResp subOp) (_: subS);
                                rightForInner = H.sigma "_a" A (_: subS);
                                innerMotive = H.lam "_r" (H.sum leftForInner rightForInner) (_r:
                                  uniRetAt SigmaS SumOp RespC composedOp A);
                                onInnerLeft = H.lam "pair_r_s" leftForInner (pair_rs:
                                  mkResumeAt SigmaS SumOp RespC composedOp A
                                    (H.fst_ pair_rs)
                                    (repack (H.snd_ pair_rs)));
                                onInnerRight = H.lam "pair_a_s" rightForInner (pair_as:
                                  mkAbortAt SigmaS SumOp RespC composedOp A
                                    (H.fst_ pair_as)
                                    (repack (H.snd_ pair_as)));
                              in
                              H.sumElim 0
                                leftForInner
                                rightForInner
                                innerMotive
                                onInnerLeft
                                onInnerRight
                                r;

                          in
                          H.lam "op" SumOp (op:
                            H.lam "_s" SigmaS (_s:
                              H.sumElim 0
                                Op_A
                                Op_B
                                outerMotive
                                (H.lam "opA" Op_A (opA: dispatchSide true opA _s))
                                (H.lam "opB" Op_B (opB: dispatchSide false opB _s))
                                op))))))))))))
    composeHandlersTy;

in
{
  scope = {
    compose = api.namespace {
      description = "fx.experimental.desc-interp.compose: universal handler-result type UniRet and its smart constructors. Every kernel-resident handler can be re-shaped into a UniRet-returning form; composeHandlers operates uniformly on that shape.";

      value = {
        UniRetTy = api.leaf {
          value = UniRetTy;
          description = "Π-type of UniRet: `Π (S:U) (Op:U) (Resp:Op→U) (op:Op) (A:U). U`.";
          tests = {
            "UniRetTy-well-formed" = {
              expr = !((H.inferHoas UniRetTy) ? error);
              expected = true;
            };
          };
        };
        UniRet = api.leaf {
          value = UniRet;
          description = ''
            UniRet : `Π (S:U) (Op:U) (Resp:Op→U) (op:Op) (A:U). U` — universal handler-result type. Left summand `Σ _r:(Resp op). S` = resume (response + new state). Right summand `Σ _a:A. S` = abort (final value + new state). State's `handle_StateTy` is conv-equal to `Π S A. Π op:EffState S. Π _s:S. UniRet S (EffState S) (Resp_State S) op A` — see the inline conv test below.
          '';
          tests = {
            "UniRet-checks-against-UniRetTy" = {
              expr = !((H.checkHoas UniRetTy UniRet) ? error);
              expected = true;
            };

            # Uniform-shape claim: handle_StateTy IS UniRet specialised at
            # state's parameters, wrapped in the same outer Π-frame.
            "UniRet-specialises-handle_StateTy" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  lhs =
                    H.forall "S" (H.u 0) (S:
                      H.forall "A" (H.u 0) (A:
                        H.forall "op" (H.app State.EffState.T S) (op:
                          H.forall "_s" S (_s:
                            uniRetAt S
                              (H.app State.EffState.T S)
                              (H.app State.Resp_State S)
                              op
                              A))));
                  rhs = State.handle_StateTy;
                  lhsVal = fx.tc.eval.eval [ ] (H.elab lhs);
                  rhsVal = fx.tc.eval.eval [ ] (H.elab rhs);
                in
                fx.tc.conv.conv 0 lhsVal rhsVal;
              expected = true;
            };
          };
        };
        mkResumeTy = api.leaf {
          value = mkResumeTy;
          description = "Π-type of mkResume.";
          tests = {
            "mkResumeTy-well-formed" = {
              expr = !((H.inferHoas mkResumeTy) ? error);
              expected = true;
            };
          };
        };
        mkResume = api.leaf {
          value = mkResume;
          description = "mkResume : `Π S Op Resp op A. (Resp op) → S → UniRet S Op Resp op A` — left-injection smart constructor.";
          tests = {
            "mkResume-checks-against-mkResumeTy" = {
              expr = !((H.checkHoas mkResumeTy mkResume) ? error);
              expected = true;
            };

            # `Resp_State S (get S) ≡ S` by iota, so `H.zero` is a valid
            # response payload at state's parameters.
            "mkResume-produces-bootInl-at-state" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  S = H.nat;
                  A = H.nat;
                  op = State.getAt S;
                  t = H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                mkResume
                                S)
                              (H.app State.EffState.T S))
                            (H.app State.Resp_State S))
                          op)
                        A)
                      H.zero)
                    H.zero;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInl";
            };
          };
        };
        mkAbortTy = api.leaf {
          value = mkAbortTy;
          description = "Π-type of mkAbort.";
          tests = {
            "mkAbortTy-well-formed" = {
              expr = !((H.inferHoas mkAbortTy) ? error);
              expected = true;
            };
          };
        };
        mkAbort = api.leaf {
          value = mkAbort;
          description = "mkAbort : `Π S Op Resp op A. A → S → UniRet S Op Resp op A` — right-injection smart constructor.";
          tests = {
            "mkAbort-checks-against-mkAbortTy" = {
              expr = !((H.checkHoas mkAbortTy mkAbort) ? error);
              expected = true;
            };

            "mkAbort-produces-bootInr-at-state" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  S = H.nat;
                  A = H.nat;
                  op = State.getAt S;
                  t = H.app
                    (H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                mkAbort
                                S)
                              (H.app State.EffState.T S))
                            (H.app State.Resp_State S))
                          op)
                        A)
                      H.zero)
                    H.zero;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInr";
            };
          };
        };
        uniRetAt = api.leaf {
          value = uniRetAt;
          description = "uniRetAt S Op Resp op A — Nix-level helper for the fully-applied UniRet spine; consumers avoid hand-rolling the 5-arg app each time.";
        };
        mkResumeAt = api.leaf {
          value = mkResumeAt;
          description = "mkResumeAt S Op Resp op A r s — Nix-level helper for the fully-applied mkResume spine.";
        };
        mkAbortAt = api.leaf {
          value = mkAbortAt;
          description = "mkAbortAt S Op Resp op A a s — Nix-level helper for the fully-applied mkAbort spine.";
        };
        composedRespTy = api.leaf {
          value = composedRespTy;
          description = "Π-type of composedResp: `Π (Op_A Op_B : U). Π (Resp_A : Op_A → U). Π (Resp_B : Op_B → U). Π op:(Sum Op_A Op_B). U`.";
          tests = {
            "composedRespTy-well-formed" = {
              expr = !((H.inferHoas composedRespTy) ? error);
              expected = true;
            };
          };
        };
        composedResp = api.leaf {
          value = composedResp;
          description = "composedResp Op_A Op_B Resp_A Resp_B op — paired response family for the sum effect. sumElim-driven so `composedResp … (inl opA) ≡ Resp_A opA` and `composedResp … (inr opB) ≡ Resp_B opB` by iota; composeHandlers relies on this conv-equality to retype the mkResume r-argument.";
          tests = {
            "composedResp-checks-against-composedRespTy" = {
              expr = !((H.checkHoas composedRespTy composedResp) ? error);
              expected = true;
            };

            # Iota witness: `composedResp Op_A Op_B Resp_A Resp_B (inl opA)`
            # reduces to `Resp_A opA`. At state's parameters, `Resp_State S
            # (get S) ≡ S`, so the whole expression reduces to `nat`.
            "composedResp-iota-reduces-on-state-get" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  S = H.nat;
                  E = H.string;
                  Op_A = H.app State.EffState.T S;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S;
                  Resp_B = H.app Error.Resp_collecting E;
                  opA = State.getAt S;
                  lhs = H.app (composedRespAt Op_A Op_B Resp_A Resp_B)
                    (inlBase Op_A Op_B opA);
                  rhs = H.nat;
                  lhsVal = fx.tc.eval.eval [ ] (H.elab lhs);
                  rhsVal = fx.tc.eval.eval [ ] (H.elab rhs);
                in
                fx.tc.conv.conv 0 lhsVal rhsVal;
              expected = true;
            };
          };
        };
        composedRespAt = api.leaf {
          value = composedRespAt;
          description = "composedRespAt Op_A Op_B Resp_A Resp_B — Nix-level helper for the 4-arg composedResp spine; result has type `Π op:(Sum Op_A Op_B). U`.";
        };
        composeHandlersTy = api.leaf {
          value = composeHandlersTy;
          description = "Π-type of composeHandlers: `Π (S_A S_B Op_A Op_B : U). Π (Resp_A : Op_A → U). Π (Resp_B : Op_B → U). Π (A : U). (Π op:Op_A. Π _s:S_A. UniRet S_A Op_A Resp_A op A) → (Π op:Op_B. Π _s:S_B. UniRet S_B Op_B Resp_B op A) → Π op:(Sum Op_A Op_B). Π _s:(Σ S_A S_B). UniRet (Σ S_A S_B) (Sum Op_A Op_B) (composedResp Op_A Op_B Resp_A Resp_B) op A`.";
          tests = {
            "composeHandlersTy-well-formed" = {
              expr = !((H.inferHoas composeHandlersTy) ? error);
              expected = true;
            };
          };
        };
        composeHandlers = api.leaf {
          value = composeHandlers;
          description = ''
            composeHandlers S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B —
            kernel-resident combinator taking two UniRet-shaped handlers and
            producing a UniRet-shaped handler over the sum effect. Body
            dispatches outer `sumElim` on `op`, projects the matching state
            slot, runs the per-effect handler, then inner-`sumElim`s on the
            UniRet result to re-package into the composed shape with the
            threaded product state. The composed-law witness lifts
            per-effect laws through this shape.
          '';
          tests = {
            "composeHandlers-checks-against-composeHandlersTy" = {
              expr = !((H.checkHoas composeHandlersTy composeHandlers) ? error);
              expected = true;
            };

            # Smoke #1: state + collecting, dispatched on `inl get`, must
            # inhabit the resume side (state never aborts).
            "composeHandlers-state-collecting-get-produces-bootInl" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  S_A = H.nat;
                  E = H.string;
                  S_B = H.listOf E;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_collecting E;
                  A = H.nat;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_collecting E) A;
                  handler =
                    H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                (H.app
                                  (H.app (H.app composeHandlers S_A) S_B)
                                  Op_A)
                                Op_B)
                              Resp_A)
                            Resp_B)
                          A)
                        H_A)
                      H_B;
                  composedOp = inlBase Op_A Op_B (State.getAt S_A);
                  _s = H.pair H.zero H.nil;
                  t = H.app (H.app handler composedOp) _s;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInl";
            };

            # Smoke #2: state + collecting, dispatched on `inr raise`, must
            # inhabit the resume side (collecting always resumes).
            "composeHandlers-state-collecting-raise-produces-bootInl" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  S_A = H.nat;
                  E = H.string;
                  S_B = H.listOf E;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_collecting E;
                  A = H.nat;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_collecting E) A;
                  handler =
                    H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                (H.app
                                  (H.app (H.app composeHandlers S_A) S_B)
                                  Op_A)
                                Op_B)
                              Resp_A)
                            Resp_B)
                          A)
                        H_A)
                      H_B;
                  composedOp = inrBase Op_A Op_B
                    (H.app (H.app Error.EffError.error E) (H.stringLit "boom"));
                  _s = H.pair H.zero H.nil;
                  t = H.app (H.app handler composedOp) _s;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInl";
            };

            # Smoke #3: state + strict, dispatched on `inr raise`, must
            # inhabit the abort side (strict always aborts). A := E for
            # strict's surrender-value-as-program-return shape.
            "composeHandlers-state-strict-raise-produces-bootInr" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  E = H.string;
                  S_A = H.nat;
                  S_B = H.nat;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_strict E;
                  A = E;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_strict E) S_B;
                  handler =
                    H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                (H.app
                                  (H.app (H.app composeHandlers S_A) S_B)
                                  Op_A)
                                Op_B)
                              Resp_A)
                            Resp_B)
                          A)
                        H_A)
                      H_B;
                  composedOp = inrBase Op_A Op_B
                    (H.app (H.app Error.EffError.error E) (H.stringLit "boom"));
                  _s = H.pair H.zero H.zero;
                  t = H.app (H.app handler composedOp) _s;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                in
                v.d.tag;
              expected = "VBootInr";
            };

            # Smoke #4: resume payload equals projected `s_A` on state's
            # get. The composed UniRet shape matches state's own UniRet
            # shape on the left summand, so `State.atType S_A A`'s dispatch
            # reads the response slot correctly — `Elab.extract H.nat` on
            # that payload yields the input counter.
            "composeHandlers-state-collecting-get-resume-equals-counter" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  Elab = fx.tc.elaborate;
                  S_A = H.nat;
                  E = H.string;
                  S_B = H.listOf E;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_collecting E;
                  A = H.nat;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_collecting E) A;
                  handler =
                    H.app
                      (H.app
                        (H.app
                          (H.app
                            (H.app
                              (H.app
                                (H.app
                                  (H.app (H.app composeHandlers S_A) S_B)
                                  Op_A)
                                Op_B)
                              Resp_A)
                            Resp_B)
                          A)
                        H_A)
                      H_B;
                  composedOp = inlBase Op_A Op_B (State.getAt S_A);
                  _s = H.pair (H.succ H.zero) H.nil;
                  t = H.app (H.app handler composedOp) _s;
                  v = fx.tc.eval.eval [ ] (H.elab t);
                  dispatched = (State.atType S_A A).dispatch { outputVal = v; };
                in
                Elab.extract H.nat dispatched.response;
              expected = 1;
            };
          };
        };
      };
    };
  };
}
