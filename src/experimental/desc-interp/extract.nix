# Partial-evaluation emitter for kernel-resident handler shortcuts.
#
# Per-canonical-op handler lemmas (compose-laws.nix style) certify
# `handle_X op s ≡_kernel mkResumeAt … r s` (resp. `mkAbortAt`) by
# `H.refl` + ι. The trampoline's per-Impure step currently realises the
# LHS via `vApp (vApp handlerCore opVal) stateVal`; `extract` realises
# the RHS directly as a Val without `eval`, closing the residual cost.
#
# Soundness splits across two layers:
#
#   1. kernel-side (HOAS lemmas, per effect):
#        handle_X op s ≡_kernel mkResumeAt S Op Resp op A r s
#
#   2. emitter-side (this file, Val conv):
#        eval (mkResumeAt …) ≡_Val extract (Resume {…})
#
# Together: kernel-path Val ≡_Val shortcut-path Val at every canonical op.
#
# UniRet shape. `Sum (Σ _r:(Resp op), S) (Σ _a:A, S)` evaluates via
# SumDT (`datatype.nix:1269-1284`) to a `VDescCon`-headed Val whose
# `.d` carries a `VBootInl`/`VBootInr` selector and whose nested
# payload is `VPair (VPair payload state) VBootRefl` — the
# `arg(Σ). ret` descArg encoding. `effects/state.nix:dispatch` reads
# exactly this shape, so the emitter targets it verbatim.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  V = fx.tc.value;

  # ---- primitives ------------------------------------------------------
  #
  # One-to-one mirrors of `V.v*` constructors. Each primitive is a
  # tagged RF; `extract` translates a tree of primitives to the
  # corresponding nested Val. Leaf slots are raw kernel Vals (no
  # `_rfTag`); sub-RFs in slot positions extract recursively.

  DescCon = D: i: d: { _rfTag = "DescCon";  inherit D i d; };
  BootInl = left: right: val: { _rfTag = "BootInl";  inherit left right val; };
  BootInr = left: right: val: { _rfTag = "BootInr";  inherit left right val; };
  Pair = fst_: snd_: { _rfTag = "Pair";     inherit fst_ snd_; };
  Tt = { _rfTag = "Tt"; };
  BootRefl = { _rfTag = "BootRefl"; };

  # ---- sugars ----------------------------------------------------------
  #
  # Folded shapes for frequently-needed Val constructions. Each sugar
  # rewrites into a nested primitive RF tree; capability is unchanged
  # from the primitives.

  # Mirrors `eval (mkResumeAt S Op Resp op A resp state)`. The bootInl
  # payload `Pair (Pair resp state) BootRefl` is the `arg(Σ).ret`
  # descArg encoding for the UniRet's left-summand Σ.
  Resume = sumDescVal: leftSig: rightSig: resp: state:
    DescCon sumDescVal Tt
      (BootInl leftSig rightSig
        (Pair (Pair resp state) BootRefl));

  # Mirrors `eval (mkAbortAt S Op Resp op A value state)`. Used by
  # error-strict (surrender), error-result (Sum-typed channel), and
  # composed-abort paths.
  Abort = sumDescVal: leftSig: rightSig: value: state:
    DescCon sumDescVal Tt
      (BootInr leftSig rightSig
        (Pair (Pair value state) BootRefl));

  # Direct Σ-pair residual — alias for `Pair` documenting intent as a
  # bare `H.pair _ _` shape rather than UniRet-inner. Used by error's
  # three strategies whose reduced RHS isn't UniRet-wrapped.
  PairRaw = fst_: snd_: Pair fst_ snd_;

  # ---- consumers -------------------------------------------------------
  #
  # Cover the additional shapes needed when a composed shortcut repacks
  # a sub-handler's state slot and dispatches on its UniRet result.

  Project = side: of_:
    { _rfTag = "Project"; inherit side of_; };

  # `onResume`/`onAbort` are Nix `Val → Val` functions receiving the
  # bootInl/bootInr payload (a `(payload, state)` VPair).
  OfElim = scrutinee: onResume: onAbort:
    { _rfTag = "OfElim"; inherit scrutinee onResume onAbort; };

  # ---- evaluator -------------------------------------------------------
  #
  # Polymorphic on input: RF (via `_rfTag`) walks per-tag to a Val; raw
  # Val (no `_rfTag`) passes through. Slot positions may freely mix
  # primitives, sugars, and pre-computed Val leaves.

  extract = rf:
    let t = rf._rfTag or null; in
    if t == null then rf
    else if t == "DescCon" then V.vDescCon (extract rf.D) (extract rf.i) (extract rf.d)
    else if t == "BootInl" then V.vBootInl (extract rf.left) (extract rf.right) (extract rf.val)
    else if t == "BootInr" then V.vBootInr (extract rf.left) (extract rf.right) (extract rf.val)
    else if t == "Pair" then V.vPair (extract rf.fst_) (extract rf.snd_)
    else if t == "Tt" then V.vTt
    else if t == "BootRefl" then V.vBootRefl
    else if t == "Project" then
      let of_Val = extract rf.of_; in
      if rf.side == "fst" then of_Val.fst
      else if rf.side == "snd" then of_Val.snd
      else throw "fx.experimental.desc-interp.extract: Project side must be \"fst\" or \"snd\", got '${rf.side}'"
    else if t == "OfElim" then
      let d = (extract rf.scrutinee).d; in
      if d.tag == "VBootInl" then rf.onResume d.val.fst
      else if d.tag == "VBootInr" then rf.onAbort d.val.fst
      else throw "fx.experimental.desc-interp.extract: OfElim scrutinee.d.tag must be VBootInl/VBootInr, got '${d.tag or "<unknown>"}'"
    else throw "fx.experimental.desc-interp.extract: unknown _rfTag '${t}'";

  # In-file conv-soundness witnesses below use these.
  C = fx.experimental.desc-interp.compose;
  State = fx.experimental.desc-interp.effects.state;
  Error = fx.experimental.desc-interp.effects.error;

  # Recover the VDescCon `.D` slot for a `H.sum leftSig rightSig`
  # instantiation by evaluating a canonical `H.inl` skeleton and
  # reading its `.D`. Sidesteps re-encoding SumDT's underlying
  # plus-of-args description by hand.
  sumDescValOf = leftSig: rightSig:
    let
      skelHoas = HI.inlAtExplicit H.levelZero leftSig rightSig (H.pair H.tt H.tt);
      skelVal = fx.tc.eval.eval [ ] (H.elab skelHoas);
    in
    skelVal.D;

in
{
  scope = {
    extract = api.namespace {
      description = "fx.experimental.desc-interp.extract: partial-evaluation emitter for kernel-resident handler shortcuts. ResidualForm algebra + `extract : RF → Val` mirroring `eval (mkResumeAt …)` / `eval (mkAbortAt …)` / fst-snd / sumElim by direct VDescCon/VBootInl/VBootInr/VPair construction. Per-effect handlers consume it for the canonical-op fast path; composed handlers use `OfElim` to dispatch over a sub-handler's UniRet result.";
      doc = ''
        ## Soundness layering

        - **kernel-side (HOAS)**: per-canonical-op lemma
          `handle_X op s ≡_kernel mkResumeAt … r s` proved by `H.refl`
          + ι (mirrors `compose-laws.nix`).
        - **emitter-side (Val)**: per-primitive conv test
          `eval (HOAS witness) ≡_Val extract (Primitive …)` shown via
          `fx.tc.conv.conv 0`. Sugar tests are consequences of the
          primitive tests + composition.
        - **chain**: kernel-path Val ≡ shortcut-path Val at every
          canonical op.

        ## Algebra

        - **Primitives** — `DescCon`, `BootInl`, `BootInr`, `Pair`,
          `Tt`, `BootRefl`. One-to-one mirrors of `V.vDescCon` /
          `vBootInl` / `vBootInr` / `vPair` / `vTt` / `vBootRefl`.
        - **Sugars** — `Resume`, `Abort`, `PairRaw`. Folded shapes
          rewriting into nested primitive RF trees; no capability
          beyond the primitives.
        - **Consumers** — `Project`, `OfElim`. Read a Val (or RF, via
          polymorphic `extract`) back into a Val; used by composed
          shortcuts.

        Caller supplies `sumDescVal` / `leftSig` / `rightSig` once per
        `atType` instance. `sumDescValOf leftSig rightSig` recovers
        the VDescCon `.D` slot from a HOAS sum type by evaluating a
        canonical `H.inl` skeleton.
      '';
      tests = {
        # Emitter conv-soundness at state's `get`: the kernel-eval'd
        # mkResumeAt Val matches the directly-built extract Val.
        "extract-Resume-conv-eq-eval-mkResumeAt-state-get" = {
          expr =
            let
              S = H.nat;
              A = H.nat;
              Op = H.app State.EffState.T S;
              Resp = H.app State.Resp_State S;
              op = State.getAt S;
              s = H.zero;
              # Resp_State S (get S) ≡ S by ι; pick S-typed witness.
              r = s;

              kernelMkR = C.mkResumeAt S Op Resp op A r s;
              kernelVal = fx.tc.eval.eval [ ] (H.elab kernelMkR);

              leftSigHoas = H.sigma "_r" (H.app Resp op) (_: S);
              rightSigHoas = H.sigma "_a" A (_: S);
              leftSigVal = fx.tc.eval.eval [ ] (H.elab leftSigHoas);
              rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
              sumDescVal_ = sumDescValOf leftSigHoas rightSigHoas;
              respVal = fx.tc.eval.eval [ ] (H.elab r);
              stateVal = fx.tc.eval.eval [ ] (H.elab s);

              extractVal = extract
                (Resume sumDescVal_ leftSigVal rightSigVal respVal stateVal);
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        # Emitter conv-soundness at error-strict's `raise`: A := E for
        # the surrender-payload-on-abort encoding.
        "extract-Abort-conv-eq-eval-mkAbortAt-error-strict-raise" = {
          expr =
            let
              E = H.string;
              State = H.nat;
              Op = H.app Error.EffError.T E;
              Resp = H.app Error.Resp_strict E;
              op = H.app (H.app Error.EffError.error E) (H.stringLit "boom");
              # `uniformOf_strict` folds A := E.
              A = E;
              s = H.zero;
              v = H.stringLit "boom";

              kernelMkA = C.mkAbortAt State Op Resp op A v s;
              kernelVal = fx.tc.eval.eval [ ] (H.elab kernelMkA);

              leftSigHoas = H.sigma "_r" (H.app Resp op) (_: State);
              rightSigHoas = H.sigma "_a" A (_: State);
              leftSigVal = fx.tc.eval.eval [ ] (H.elab leftSigHoas);
              rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
              sumDescVal_ = sumDescValOf leftSigHoas rightSigHoas;
              valueVal = fx.tc.eval.eval [ ] (H.elab v);
              stateVal = fx.tc.eval.eval [ ] (H.elab s);

              extractVal = extract
                (Abort sumDescVal_ leftSigVal rightSigVal valueVal stateVal);
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        # Project selects a VPair component verbatim.
        "extract-Project-fst-returns-first-component" = {
          expr =
            let pair = V.vPair (V.vIntLit 7) (V.vIntLit 9);
            in (extract (Project "fst" pair)).value;
          expected = 7;
        };
        "extract-Project-snd-returns-second-component" = {
          expr =
            let pair = V.vPair (V.vIntLit 7) (V.vIntLit 9);
            in (extract (Project "snd" pair)).value;
          expected = 9;
        };

        # OfElim dispatches on the scrutinee's bootInl/bootInr tag.
        # Build the scrutinee via `extract Resume` / `extract Abort`
        # so OfElim composes with the same shapes produced by per-effect
        # shortcuts.
        "extract-OfElim-on-Resume-routes-to-onResume" = {
          expr =
            let
              S = H.nat;
              A = H.nat;
              Resp = H.app State.Resp_State S;
              op = State.getAt S;
              leftSigHoas = H.sigma "_r" (H.app Resp op) (_: S);
              rightSigHoas = H.sigma "_a" A (_: S);
              leftSigVal = fx.tc.eval.eval [ ] (H.elab leftSigHoas);
              rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
              sumDescVal_ = sumDescValOf leftSigHoas rightSigHoas;
              resumeVal = extract (Resume sumDescVal_ leftSigVal rightSigVal
                (V.vIntLit 3)
                (V.vIntLit 5));
              dispatched = extract (OfElim resumeVal
                (pair: pair.fst)    # resp slot of (resp, state)
                (_: V.vIntLit (-1)));
            in
            dispatched.value;
          expected = 3;
        };
        # PairRaw mirrors `eval (H.pair x y)` verbatim.
        "extract-PairRaw-conv-eq-eval-pair-intLits" = {
          expr =
            let
              kernelPair = H.pair (H.intLit 7) (H.intLit 9);
              kernelVal = fx.tc.eval.eval [ ] (H.elab kernelPair);
              extractVal = extract
                (PairRaw (V.vIntLit 7) (V.vIntLit 9));
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        "extract-OfElim-on-Abort-routes-to-onAbort" = {
          expr =
            let
              S = H.nat;
              A = H.nat;
              Resp = H.app State.Resp_State S;
              op = State.getAt S;
              leftSigHoas = H.sigma "_r" (H.app Resp op) (_: S);
              rightSigHoas = H.sigma "_a" A (_: S);
              leftSigVal = fx.tc.eval.eval [ ] (H.elab leftSigHoas);
              rightSigVal = fx.tc.eval.eval [ ] (H.elab rightSigHoas);
              sumDescVal_ = sumDescValOf leftSigHoas rightSigHoas;
              abortVal = extract (Abort sumDescVal_ leftSigVal rightSigVal
                (V.vIntLit 11)
                (V.vIntLit 22));
              dispatched = extract (OfElim abortVal
                (_: V.vIntLit (-1))
                (pair: pair.snd)); # state slot of (value, state)
            in
            dispatched.value;
          expected = 22;
        };

        # ---- primitive conv soundness -------------------------------
        #
        # Direct primitive ↔ V-side correspondence at the HOAS witnesses
        # each primitive mirrors. Sugars (Resume/Abort/PairRaw) become
        # consequences of these tests via composition.

        # Pair ↔ `H.pair`.
        "extract-Pair-conv-eq-eval-H-pair" = {
          expr =
            let
              kernelVal = fx.tc.eval.eval [ ]
                (H.elab (H.pair (H.intLit 7) (H.intLit 9)));
              extractVal = extract (Pair (V.vIntLit 7) (V.vIntLit 9));
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        # Tt ↔ `H.tt`.
        "extract-Tt-conv-eq-eval-H-tt" = {
          expr =
            let
              kernelVal = fx.tc.eval.eval [ ] (H.elab H.tt);
              extractVal = extract Tt;
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        # DescCon+BootInl ↔ `H.inl`. Witnesses descArg `arg(X).ret`
        # encoding: bootInl val is `Pair payload BootRefl`.
        "extract-DescCon-BootInl-conv-eq-eval-H-inl" = {
          expr =
            let
              X = H.nat;
              Y = H.string;
              payloadHoas = H.intLit 42;
              kernelVal = fx.tc.eval.eval [ ]
                (H.elab (HI.inlAtExplicit H.levelZero X Y payloadHoas));
              Xval = fx.tc.eval.eval [ ] (H.elab X);
              Yval = fx.tc.eval.eval [ ] (H.elab Y);
              payloadVal = fx.tc.eval.eval [ ] (H.elab payloadHoas);
              sumDescVal_ = sumDescValOf X Y;
              extractVal = extract (DescCon sumDescVal_ Tt
                (BootInl Xval Yval
                  (Pair payloadVal BootRefl)));
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };

        # DescCon+BootInr ↔ `H.inr`.
        "extract-DescCon-BootInr-conv-eq-eval-H-inr" = {
          expr =
            let
              X = H.nat;
              Y = H.string;
              payloadHoas = H.stringLit "right";
              kernelVal = fx.tc.eval.eval [ ]
                (H.elab (HI.inrAtExplicit H.levelZero X Y payloadHoas));
              Xval = fx.tc.eval.eval [ ] (H.elab X);
              Yval = fx.tc.eval.eval [ ] (H.elab Y);
              payloadVal = fx.tc.eval.eval [ ] (H.elab payloadHoas);
              sumDescVal_ = sumDescValOf X Y;
              extractVal = extract (DescCon sumDescVal_ Tt
                (BootInr Xval Yval
                  (Pair payloadVal BootRefl)));
            in
            fx.tc.conv.conv 0 kernelVal extractVal;
          expected = true;
        };
      };

      value = {
        DescCon = api.leaf {
          value = DescCon;
          description = "DescCon D i d — primitive mirror of `V.vDescCon D i d`. `D` is a descriptor Val, `i` the index Val, `d` the constructor payload.";
        };
        BootInl = api.leaf {
          value = BootInl;
          description = "BootInl left right val — primitive mirror of `V.vBootInl left right val`. Left-summand selector inside a `DescCon` for a plus-of-args description.";
        };
        BootInr = api.leaf {
          value = BootInr;
          description = "BootInr left right val — primitive mirror of `V.vBootInr left right val`. Right-summand counterpart of `BootInl`.";
        };
        Pair = api.leaf {
          value = Pair;
          description = "Pair fst_ snd_ — primitive mirror of `V.vPair fst snd`.";
        };
        Tt = api.leaf {
          value = Tt;
          description = "Tt — primitive mirror of `V.vTt`. Unit Val constant.";
        };
        BootRefl = api.leaf {
          value = BootRefl;
          description = "BootRefl — primitive mirror of `V.vBootRefl`. Structural marker for the `ret` slot of descArg.";
        };
        Resume = api.leaf {
          value = Resume;
          description = "Resume sumDescVal leftSig rightSig resp state — UniRet left summand sugar. Folds to `DescCon sumDescVal Tt (BootInl leftSig rightSig (Pair (Pair resp state) BootRefl))`. Mirrors `eval (mkResumeAt S Op Resp op A resp state)`.";
        };
        Abort = api.leaf {
          value = Abort;
          description = "Abort sumDescVal leftSig rightSig value state — UniRet right summand sugar. Folds to `DescCon sumDescVal Tt (BootInr leftSig rightSig (Pair (Pair value state) BootRefl))`. Used by error-strict (surrender), error-result (Sum-typed channel), and composed abort paths.";
        };
        PairRaw = api.leaf {
          value = PairRaw;
          description = "PairRaw fst_ snd_ — alias for `Pair`. Documents intent as a bare `H.pair _ _` residual (as opposed to UniRet-inner pair). Used by error's three strategies whose reduced RHS isn't UniRet-wrapped.";
        };
        Project = api.leaf {
          value = Project;
          description = "Project side of_ — first or second projection of a VPair-typed Val. `side ∈ {\"fst\",\"snd\"}`. Used by composed-shortcut state-slot repack.";
        };
        OfElim = api.leaf {
          value = OfElim;
          description = "OfElim scrutinee onResume onAbort — Val-side pattern match on a UniRet-shaped scrutinee. `onResume`/`onAbort` are Nix `Val → Val` functions receiving the bootInl/bootInr payload (a `(payload, state)` VPair). Used by composed shortcuts to dispatch on inner sub-handler results.";
        };
        extract = api.leaf {
          value = extract;
          description = "extract : ResidualForm → Val. Direct attrset construction targeting the VDescCon/VBootInl|VBootInr/VPair encoding produced by `eval` on the canonical mkResumeAt / mkAbortAt / fst_ / snd_ / sumElim spines. Per-constructor conv tests under `_self.tests` discharge emitter-side soundness.";
        };
        sumDescValOf = api.leaf {
          value = sumDescValOf;
          description = "sumDescValOf leftSigHoas rightSigHoas — recovers the VDescCon `.D` slot for a `H.sum leftSig rightSig` instantiation by evaluating a canonical `H.inl` skeleton and reading its `.D`. Caller-side helper for building `Resume`/`Abort` metadata Vals once per `atType` instance.";
        };
      };
    };
  };
}
