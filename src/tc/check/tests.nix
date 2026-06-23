# Inline tests for the type-checking kernel: context ops, bidirectional
# dispatch, motive checking, primitive literals, Desc/Mu, generated data,
# universe levels, and trampoline stress.
{ self, fx, lib, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  Q = fx.tc.quote;
  H = fx.tc.hoas;
  HI = fx.tc.hoas._internal._indexed;
  E = fx.tc.eval;

  inherit (self)
    checkType checkTypeLevel
    emptyCtx extend lookupType
    runCheck checkTm inferTm;

  inherit (V) vPi vSigma vUnit vBootSum vBootEq vU mkClosure vTt
    vString vInt vFloat vAttrs vPath vFunction vAny
    vMu;

  ctx0 = emptyCtx;
  ctx1 = extend ctx0 "x" vUnit;

  lvlToInt = v:
    let
      spine = fx.tc.conv.normLevel v;
      head = builtins.head spine;
    in
    if spine == [ ] then 0
    else if builtins.length spine == 1 && head.base.kind == "zero"
    then head.shift
    else throw "check/tests: non-concrete level (${toString (builtins.length spine)} summands)";
  typeLvl = r: lvlToInt r.type.level;
  ctlLvl = r: lvlToInt r.level;

  natTyTm = H.elab H.nat;
  zeroTm = H.elab H.zero;
  succZeroTm = H.elab (H.succ H.zero);
  listNatTm = H.elab (H.listOf H.nat);
  nilNatTm = H.elab (HI.nilAtExplicit H.nat);
  consZeroNilTm = H.elab (HI.consAtExplicit H.nat H.zero (HI.nilAtExplicit H.nat));
  natTyVal = E.eval [ ] natTyTm;
  listNatVal = E.eval [ ] listNatTm;

  bigNatTm = H.elab (H.natLit 5000);
  bigListTm = H.elab (builtins.foldl'
    (acc: _: HI.consAtExplicit H.nat H.zero acc)
    (HI.nilAtExplicit H.nat)
    (builtins.genList (x: x) 5000));

  unitFn = S: H.ann (H.lam "_" S (_: H.tt)) (H.forall "_" S (_: H.unit));
  encRet = H.elab (H.retI H.unit 0 H.tt);
  encArg = H.elab (H.descArg H.unit 0 H.unit (_: H.retI H.unit 0 H.tt));
  encArg1 = H.elab (H.descArg H.unit 1 (H.u 0) (_: H.retI H.unit 1 H.tt));
  encRec = H.elab (HI.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
  encPi = H.elab (HI.piI H.unit 0 H.unit (unitFn H.unit) (H.retI H.unit 0 H.tt));
  encPi1 = H.elab (HI.piI H.unit 1 (H.u 0) (unitFn (H.u 0)) (H.retI H.unit 1 H.tt));
  encRetD = T.mkAnn encRet (T.mkDesc T.mkLevelZero T.mkUnit);
  encArgD = T.mkAnn encArg (T.mkDesc T.mkLevelZero T.mkUnit);
  encRecD = T.mkAnn encRec (T.mkDesc T.mkLevelZero T.mkUnit);
  encPiD = T.mkAnn encPi (T.mkDesc T.mkLevelZero T.mkUnit);
  encPlus = H.elab (H.plus (H.retI H.unit 0 H.tt) (H.retI H.unit 0 H.tt));
  encPlusD = T.mkAnn encPlus (T.mkDesc T.mkLevelZero T.mkUnit);
  encNonLinear = H.elab (H.plus H.descRet (H.descRec (H.descRec H.descRet)));
  encNonLinearD = T.mkAnn encNonLinear (T.mkDesc T.mkLevelZero T.mkUnit);
in
{
  scope = { };
  tests = {
    "ctx-empty-depth" = { expr = ctx0.depth; expected = 0; };
    "ctx-extend-depth" = { expr = ctx1.depth; expected = 1; };
    "ctx-lookup" = { expr = (lookupType ctx1 0).tag; expected = "VUnit"; };

    "check-id" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkUnit (T.mkVar 0))
        (vPi "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
      expected = "lam";
    };
    "check-tt" = {
      expr = (checkTm ctx0 T.mkTt vUnit).tag;
      expected = "tt";
    };
    "check-refl" = {
      expr = (checkTm ctx0 T.mkBootRefl (vBootEq vUnit vTt vTt)).tag;
      expected = "boot-refl";
    };
    "check-pair" = {
      expr = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
        (vSigma "x" vUnit (mkClosure [ ] T.mkUnit))).tag;
      expected = "pair";
    };
    "check-boot-inl" = {
      expr = (checkTm ctx0 (T.mkBootInl T.mkUnit T.mkString T.mkTt)
        (vBootSum vUnit vString)).tag;
      expected = "boot-inl";
    };
    "check-boot-inr" = {
      expr = (checkTm ctx0 (T.mkBootInr T.mkUnit T.mkString (T.mkStringLit "x"))
        (vBootSum vUnit vString)).tag;
      expected = "boot-inr";
    };

    "check-generated-zero" = {
      expr = (checkTm ctx0 zeroTm natTyVal).tag;
      expected = "desc-con";
    };
    "check-generated-succ" = {
      expr = (checkTm ctx0 succZeroTm natTyVal).tag;
      expected = "desc-con";
    };
    "check-generated-nil" = {
      expr = (checkTm ctx0 nilNatTm listNatVal).tag;
      expected = "desc-con";
    };
    "check-generated-cons" = {
      expr = (checkTm ctx0 consZeroNilTm listNatVal).tag;
      expected = "desc-con";
    };
    "check-generated-nat-5000" = {
      expr = (checkTm ctx0 bigNatTm natTyVal).tag;
      expected = "desc-con";
    };
    "check-generated-list-5000" = {
      expr = (checkTm ctx0 bigListTm listNatVal).tag;
      expected = "desc-con";
    };

    "infer-var" = {
      expr = (inferTm ctx1 (T.mkVar 0)).type.tag;
      expected = "VUnit";
    };
    "infer-ann" = {
      expr = (inferTm ctx0 (T.mkAnn T.mkTt T.mkUnit)).type.tag;
      expected = "VUnit";
    };
    "infer-U0" = {
      expr = typeLvl (inferTm ctx0 (T.mkU T.mkLevelZero));
      expected = 1;
    };
    "infer-U1" = {
      expr = typeLvl (inferTm ctx0 (T.mkU (T.mkLevelSuc T.mkLevelZero)));
      expected = 2;
    };
    "infer-pi-level-universe-U" = {
      expr = (inferTm ctx0
        (T.mkPi "k" T.mkLevel (T.mkU (T.mkVar 0)))).type.tag;
      expected = "VU";
    };
    "infer-generated-nat-type" = {
      expr = typeLvl (inferTm ctx0 natTyTm);
      expected = 0;
    };
    "infer-generated-list-type" = {
      expr = typeLvl (inferTm ctx0 listNatTm);
      expected = 0;
    };
    "infer-pi-type" = {
      expr = typeLvl (inferTm ctx0 (T.mkPi "x" T.mkUnit T.mkUnit));
      expected = 0;
    };
    "infer-app" = {
      expr =
        let
          idFn = T.mkAnn (T.mkLam "x" T.mkUnit (T.mkVar 0))
            (T.mkPi "x" T.mkUnit T.mkUnit);
        in
        (inferTm ctx0 (T.mkApp idFn T.mkTt)).type.tag;
      expected = "VUnit";
    };
    "infer-fst" = {
      expr =
        let
          p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x"))
            (T.mkSigma "x" T.mkUnit T.mkString);
        in
        (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VUnit";
    };
    "infer-snd" = {
      expr =
        let
          p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x"))
            (T.mkSigma "x" T.mkUnit T.mkString);
        in
        (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VString";
    };
    "infer-pair-via-ann" = {
      expr =
        let
          sigTy = T.mkSigma "x" T.mkUnit T.mkString;
          p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x")) sigTy;
        in
        (inferTm ctx0 p).type.tag;
      expected = "VSigma";
    };
    "reject-pair-infer-bare" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)) ? error;
      expected = true;
    };
    "reject-pair-infer-bare-msg" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)).msg;
      expected = "no inference rule for term shape pair";
    };
    "check-let" = {
      expr = (checkTm ctx0 (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0)) vUnit).tag;
      expected = "let";
    };
    "check-poly-id" = {
      expr =
        let
          ty = vPi "A" (vU V.vLevelZero)
            (mkClosure [ ] (T.mkPi "x" (T.mkVar 0) (T.mkVar 1)));
          tm = T.mkLam "A" (T.mkU T.mkLevelZero)
            (T.mkLam "x" (T.mkVar 0) (T.mkVar 0));
        in
        (checkTm ctx0 tm ty).tag;
      expected = "lam";
    };

    "infer-sum-elim" = {
      expr = (inferTm ctx0 (T.mkBootSumElim T.mkUnit T.mkString
        (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkString) T.mkUnit)
        (T.mkLam "x" T.mkUnit T.mkTt)
        (T.mkLam "s" T.mkString T.mkTt)
        (T.mkBootInl T.mkUnit T.mkString T.mkTt))).type.tag;
      expected = "VUnit";
    };
    "infer-j" = {
      expr = (inferTm ctx0 (T.mkBootJ T.mkUnit T.mkTt
        (T.mkLam "y" T.mkUnit
          (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 1)) T.mkUnit))
        T.mkTt
        T.mkTt
        T.mkBootRefl)).type.tag;
      expected = "VUnit";
    };
    "large-elim-sum" = {
      expr = (inferTm ctx0 (T.mkBootSumElim T.mkUnit T.mkString
        (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkString) (T.mkU T.mkLevelZero))
        (T.mkLam "x" T.mkUnit T.mkUnit)
        (T.mkLam "s" T.mkString T.mkString)
        (T.mkBootInl T.mkUnit T.mkString T.mkTt))).type.tag;
      expected = "VU";
    };
    "large-elim-j" = {
      expr = (inferTm ctx0 (T.mkBootJ T.mkUnit T.mkTt
        (T.mkLam "y" T.mkUnit
          (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 1)) (T.mkU T.mkLevelZero)))
        T.mkUnit
        T.mkTt
        T.mkBootRefl)).type.tag;
      expected = "VU";
    };

    "reject-tt-as-string" = {
      expr = (checkTm ctx0 T.mkTt vString) ? error;
      expected = true;
    };
    "reject-U0-U0" = {
      expr = (checkTm ctx0 (T.mkU T.mkLevelZero) (vU V.vLevelZero)) ? error;
      expected = true;
    };
    "reject-refl-unequal" = {
      expr = (checkTm ctx0 T.mkBootRefl
        (vBootEq vString (V.vStringLit "a") (V.vStringLit "b"))) ? error;
      expected = true;
    };
    "reject-app-non-fn" = {
      expr = (inferTm ctx0 (T.mkApp (T.mkAnn T.mkTt T.mkUnit) T.mkTt)) ? error;
      expected = true;
    };
    "reject-fst-non-pair" = {
      expr = (inferTm ctx0 (T.mkFst (T.mkAnn T.mkTt T.mkUnit))) ? error;
      expected = true;
    };
    "reject-unbound-var" = {
      expr = (builtins.tryEval (builtins.deepSeq (inferTm ctx0 (T.mkVar 0)) true)).success;
      expected = false;
    };
    "reject-pair-snd-mismatch" = {
      expr = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
        (vSigma "x" vUnit (mkClosure [ ] T.mkString))) ? error;
      expected = true;
    };
    "reject-pair-snd-mismatch-msg" = {
      expr = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
        (vSigma "x" vUnit (mkClosure [ ] T.mkString))).msg;
      expected = "no inference rule for term shape tt";
    };
    "catchall-leaf-carries-term-tag" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)).error.detail.term.tag;
      expected = "pair";
    };
    "catchall-leaf-carries-frame-depth-zero" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)).error.detail.frame.depth;
      expected = 0;
    };
    "catchall-leaf-frame-depth-tracks-context" = {
      expr =
        let
          ctx5 = builtins.foldl' (c: n: extend c "v${toString n}" vUnit)
            ctx0 [ 0 1 2 3 4 ];
        in
        (inferTm ctx5 (T.mkPair T.mkTt T.mkTt)).error.detail.frame.depth;
      expected = 5;
    };
    "catchall-leaf-frame-names-tracks-extends" = {
      expr =
        let
          ctx3 = extend (extend (extend ctx0 "a" vUnit) "b" vUnit) "c" vUnit;
        in
        (inferTm ctx3 (T.mkPair T.mkTt T.mkTt)).error.detail.frame.names;
      expected = [ "c" "b" "a" ];
    };
    "catchall-leaf-carries-quoted-term" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)).error.detail.term.quoted.tag;
      expected = "pair";
    };
    "trace-records-rule-name-via-bindPR" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          rules = map (e: e.rule) err.detail.trace;
        in
        builtins.elem "check" rules;
      expected = true;
    };

    # -- End-to-end resolver: the catch-all leaf from a real kernel
    # path must surface a shape-category Hint via fx.diag.hints.resolve.
    # Drives the full check→sub→infer→catch-all flow.
    "catchall-resolves-shape-hint" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          hint = fx.diag.hints.resolve err;
        in
        if hint == null then null else hint.category;
      expected = "shape";
    };
    "catchall-resolves-unhandled-tt" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          hint = fx.diag.hints.resolve err;
        in
        hint == fx.diag.hints.hints."::unhandled-tt";
      expected = true;
    };

    # -- End-to-end renderer: multiLine on a real catch-all error
    # contains the Kernel layer marker, the term tag, the frame depth,
    # the trace stack header, and the resolved hint text.
    "catchall-render-includes-kernel-layer" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          rendered = fx.diag.pretty.multiLine err;
        in
        lib.strings.hasInfix "[Kernel]" rendered;
      expected = true;
    };
    "catchall-render-includes-term-tag-line" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          rendered = fx.diag.pretty.multiLine err;
        in
        lib.strings.hasInfix "term: tt" rendered;
      expected = true;
    };
    "catchall-render-includes-frame-depth-line" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          rendered = fx.diag.pretty.multiLine err;
        in
        lib.strings.hasInfix "frame.depth: 0" rendered;
      expected = true;
    };
    "catchall-render-includes-trace-header" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          rendered = fx.diag.pretty.multiLine err;
        in
        lib.strings.hasInfix "trace:" rendered;
      expected = true;
    };
    # Resolver and renderer are decoupled: the resolver returns the
    # Hint, the renderer reads `err.hint`. The end-to-end pipeline is
    # resolve → setLeafHint → render. This test pins the whole chain.
    "catchall-resolve-attach-render-pipeline" = {
      expr =
        let
          err = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
            (vSigma "x" vUnit (mkClosure [ ] T.mkString))).error;
          hint = fx.diag.hints.resolve err;
          annotated = fx.diag.error.setLeafHint hint err;
          rendered = fx.diag.pretty.multiLine annotated;
        in
        hint != null
        && lib.strings.hasInfix hint.text rendered;
      expected = true;
    };
    "reject-j-motive-wrong-inner-domain" = {
      expr = (inferTm ctx0 (T.mkBootJ T.mkUnit T.mkTt
        (T.mkAnn
          (T.mkLam "y" T.mkUnit
            (T.mkLam "e" T.mkUnit (T.mkU T.mkLevelZero)))
          (T.mkPi "y" T.mkUnit
            (T.mkPi "e" T.mkUnit (T.mkU (T.mkLevelSuc T.mkLevelZero)))))
        T.mkUnit
        T.mkTt
        T.mkBootRefl)) ? error;
      expected = true;
    };
    "reject-lam-against-non-pi" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkUnit (T.mkVar 0)) vUnit) ? error;
      expected = true;
    };
    "reject-U1-in-U0" = {
      expr = (checkTm ctx0
        (T.mkU (T.mkLevelSuc T.mkLevelZero))
        (vU V.vLevelZero)) ? error;
      expected = true;
    };
    "reject-sum-elim-unit-scrut" = {
      expr = (inferTm ctx0 (T.mkBootSumElim T.mkUnit T.mkString
        (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkString) T.mkUnit)
        (T.mkLam "x" T.mkUnit T.mkTt)
        (T.mkLam "s" T.mkString T.mkTt)
        T.mkTt)) ? error;
      expected = true;
    };

    "infer-eq-type" = {
      expr = (inferTm ctx0 (T.mkBootEq T.mkUnit T.mkTt T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-sigma-type" = {
      expr = (inferTm ctx0 (T.mkSigma "x" T.mkUnit T.mkUnit)).type.tag;
      expected = "VU";
    };
    "infer-sum-type" = {
      expr = (inferTm ctx0 (T.mkBootSum T.mkUnit T.mkString)).type.tag;
      expected = "VU";
    };
    "infer-lift-elim-accepts-composed-nested-lift" = {
      expr =
        let
          l0 = T.mkLevelZero;
          l1 = T.mkLevelSuc l0;
          l2 = T.mkLevelSuc l1;
          innerTy = T.mkLift l0 l1 T.mkBootRefl T.mkUnit;
          composedIntro = T.mkLiftIntro l0 l2 T.mkBootRefl T.mkUnit T.mkTt;
          lowered = T.mkLiftElim l1 l2 T.mkBootRefl innerTy composedIntro;
        in
        (inferTm ctx0 lowered).type.tag;
      expected = "VLift";
    };
    "checktype-generated-nat" = {
      expr = (runCheck (checkType ctx0 natTyTm)).tag;
      expected = "mu";
    };
    "checktype-pi" = {
      expr = (runCheck (checkType ctx0 (T.mkPi "x" T.mkUnit T.mkUnit))).tag;
      expected = "pi";
    };
    "checktype-sigma" = {
      expr = (runCheck (checkType ctx0 (T.mkSigma "x" T.mkUnit T.mkUnit))).tag;
      expected = "sigma";
    };
    "checktype-fallback" = {
      expr = (runCheck (checkType ctx0 (T.mkAnn T.mkUnit (T.mkU T.mkLevelZero)))).tag;
      expected = "ann";
    };
    "reject-checktype-non-universe" = {
      expr = (runCheck (checkTypeLevel ctx0 (T.mkAnn T.mkTt T.mkUnit))) ? error;
      expected = true;
    };

    "stress-nested-let-100" = {
      expr =
        let
          nested = builtins.foldl'
            (body: _:
              T.mkLet "x" T.mkUnit T.mkTt body
            )
            T.mkTt
            (builtins.genList (x: x) 100);
        in
        (checkTm ctx0 nested vUnit).tag;
      expected = "let";
    };
    "stress-nested-pi" = {
      expr =
        let
          nested = builtins.foldl' (acc: _: T.mkPi "x" T.mkUnit acc)
            T.mkUnit
            (builtins.genList (x: x) 500);
        in
        typeLvl (inferTm ctx0 nested);
      expected = 0;
    };

    # Depth-flatness regression for the bidirectional checker on deep right-
    # nested telescopes at N=10000 (the default max-call-depth). checkType's pi
    # arm and checkTm's lam/let arms each descend one binder per level; a
    # checker that consumes Nix call-depth per binder overflows max-call-depth
    # well before N=10000. A flat checker reads all three in O(1) libnix frames
    # at default ulimit -s 8192. lam checks against the evaluated deep Pi (the
    # bindPR-wrapped handle path); let nests directly under Unit.
    "stress-checktype-pi-10000-flat" = {
      expr =
        let
          deepPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
            T.mkUnit
            (builtins.genList (x: x) 10000);
        in
        (runCheck (checkType ctx0 deepPi)).tag;
      expected = "pi";
    };
    "stress-checktm-lam-10000-flat" = {
      expr =
        let
          deepPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
            T.mkUnit
            (builtins.genList (x: x) 10000);
          deepLam = builtins.foldl' (body: _: T.mkLam "x" T.mkUnit body)
            T.mkTt
            (builtins.genList (x: x) 10000);
        in
        (checkTm ctx0 deepLam (E.eval [ ] deepPi)).tag;
      expected = "lam";
    };
    "stress-checktm-let-10000-flat" = {
      expr =
        let
          deepLet = builtins.foldl' (body: _: T.mkLet "x" T.mkUnit T.mkTt body)
            T.mkTt
            (builtins.genList (x: x) 10000);
        in
        (checkTm ctx0 deepLet vUnit).tag;
      expected = "let";
    };
    # Context-counter depth-flatness. `extend` caches `depth = ctx.depth + 1`
    # (and `eb`); without forcing the counter at each extension, N chained
    # extends leave an N-deep `+1` thunk chain. Forcing it (any check reading
    # `ctx.depth`, e.g. `lookupType`'s bound check) recurses N-deep on the
    # native C-stack and overflows a small thread stack — a nix-unit worker
    # crosses over below N=4000 — while max-call-depth stays untouched.
    # extend forces the counter eagerly, so a 10000-deep context reads its
    # depth and looks up a binding in O(1) host frames.
    "stress-extend-deep-depth-flat-10000" = {
      expr =
        let
          deepCtx = builtins.foldl' (acc: _: extend acc "x" vUnit) ctx0
            (builtins.genList (x: x) 10000);
        in
        { depth = deepCtx.depth; tag = (lookupType deepCtx 0).tag; };
      expected = { depth = 10000; tag = "VUnit"; };
    };
    # Homogeneous-ctor-chain flatness under the strided head-yield: layers
    # between stride multiples return Pure and must be applied iteratively
    # from the trampoline queue, not by nesting host frames — a regression
    # here overflows max-call-depth well before N=10000.
    "stress-checktm-nat-chain-10000-flat" = {
      expr = (checkTm ctx0 (H.elab (H.natLit 10000)) natTyVal).tag;
      expected = "desc-con";
    };
    # Wide-term flatness under the entry-yield budget: the budget divides
    # among children (Σ child budgets ≤ b − 1), so a full binary pair tree
    # admits ≤ entryBudget un-yielded entries per native segment. A
    # per-path depth counter instead admits arity^budget native frames —
    # this term overflows the host stack under that design.
    "stress-checktm-pair-bushy-flat" = {
      expr =
        let
          pairTree = d:
            if d == 0 then T.mkTt
            else let s = pairTree (d - 1); in T.mkPair s s;
          sigTree = d:
            if d == 0 then T.mkUnit
            else let s = sigTree (d - 1); in T.mkSigma "_" s s;
        in
        (checkTm ctx0 (pairTree 14) (E.eval [ ] (sigTree 14))).tag;
      expected = "pair";
    };
    # app divides the entry budget by 2 per level (infer fn + check arg),
    # so a deep spine re-yields every ~log2(entryBudget) entries and must
    # stay host-stack-flat at N=10000.
    "stress-infertm-app-spine-10000-flat" = {
      expr =
        let
          deepPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
            T.mkUnit
            (builtins.genList (x: x) 10000);
          ctxF = extend ctx0 "f" (E.eval [ ] deepPi);
          spine = builtins.foldl' (f: _: T.mkApp f T.mkTt)
            (T.mkVar 0)
            (builtins.genList (x: x) 10000);
        in
        (inferTm ctxF spine).type.tag;
      expected = "VUnit";
    };
    # Transit-economy pin for the entry-yield budget on a fanout-1 lam
    # tower (windows of 64 entries). A 256-tower has 4 window boundaries:
    # the top-level yield plus one fused push chain per interior window;
    # entries inside windows above a deeper boundary still bracket (one
    # pop each), while the terminal window is fully Pure — zero transits.
    # A 64-tower is a single terminal window: the head yield only.
    "check-entry-budget-transit-economy" = {
      expr =
        let
          countTransits = n:
            let
              deepPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
                T.mkUnit
                (builtins.genList (x: x) n);
              deepLam = builtins.foldl' (body: _: T.mkLam "x" T.mkUnit body)
                T.mkTt
                (builtins.genList (x: x) n);
              r = fx.trampoline.handle
                {
                  state = { pushes = 0; pops = 0; yields = 0; };
                  handlers = {
                    tcBlamePush = { state, ... }: {
                      resume = null;
                      state = state // { pushes = state.pushes + 1; };
                    };
                    tcBlamePop = { state, ... }: {
                      resume = null;
                      state = state // { pops = state.pops + 1; };
                    };
                    tcYield = { state, ... }: {
                      resume = null;
                      state = state // { yields = state.yields + 1; };
                    };
                  };
                }
                (self.check ctx0 deepLam (E.eval [ ] deepPi));
            in
            { inherit (r.state) pushes pops yields; };
        in
        { tower256 = countTransits 256; tower64 = countTransits 64; };
      expected = {
        tower256 = { pushes = 3; pops = 192; yields = 1; };
        tower64 = { pushes = 0; pops = 0; yields = 1; };
      };
    };
    # An error deep inside a bypassed window must surface with the same
    # blame structure as the always-yield discipline: the typeError makes
    # every enclosing bind Impure, so the brackets fire identically.
    # Expected values pinned from the pre-budget checker.
    "check-entry-budget-error-blame-identical" = {
      expr =
        let
          deepPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
            T.mkString
            (builtins.genList (x: x) 8);
          deepLam = builtins.foldl' (body: _: T.mkLam "x" T.mkUnit body)
            T.mkTt
            (builtins.genList (x: x) 8);
          r = checkTm ctx0 deepLam (E.eval [ ] deepPi);
          childPath = err:
            if builtins.length (err.children or [ ]) > 0
            then
              let c = builtins.elemAt err.children 0; in
              [ c.position.tag ] ++ childPath c.error
            else [ ];
        in
        {
          msg = r.msg;
          trace = map (e: e.position.tag) r.error.detail.trace;
          childPath = childPath r.error;
        };
      expected = {
        msg = "no inference rule for term shape tt";
        trace = [ "Sub" ] ++ builtins.genList (_: "LamBody") 8;
        childPath = builtins.genList (_: "LamBody") 8 ++ [ "Sub" ];
      };
    };
    # Bushy type-former flatness under checkTypeLevel's entry budget: a
    # full binary sigma tree (2^14 entries) divides the budget by 2 per
    # level, so un-yielded entries per native segment stay ≤ entryBudget.
    # A per-path counter admits arity^budget native frames here.
    "stress-checktypelevel-sigma-bushy-flat" = {
      expr =
        let
          sigTree = d:
            if d == 0 then T.mkUnit
            else let s = sigTree (d - 1); in T.mkSigma "_" s s;
        in
        (runCheck (checkType ctx0 (sigTree 14))).tag;
      expected = "sigma";
    };
    # Transit-economy pin for the budgeted checkTypeLevel on a fanout-1
    # squash tower (windows of 64 entries). The former arms recurse via
    # plain `bind` (no blame positions), so windows produce no brackets;
    # each window boundary survives as exactly one yield transit: a
    # 64-tower is one terminal window (the head yield only), a 256-tower
    # has four boundaries. `funext`/`level-zero` are leaves: fully Pure,
    # zero transits.
    "checktypelevel-entry-budget-transit-economy" = {
      expr =
        let
          countTransits = comp:
            let
              r = fx.trampoline.handle
                {
                  state = { pushes = 0; pops = 0; yields = 0; };
                  handlers = {
                    tcBlamePush = { state, ... }: {
                      resume = null;
                      state = state // { pushes = state.pushes + 1; };
                    };
                    tcBlamePop = { state, ... }: {
                      resume = null;
                      state = state // { pops = state.pops + 1; };
                    };
                    tcYield = { state, ... }: {
                      resume = null;
                      state = state // { yields = state.yields + 1; };
                    };
                  };
                }
                comp;
            in
            { inherit (r.state) pushes pops yields; };
          squashTower = n:
            builtins.foldl' (acc: _: T.mkSquash acc) T.mkUnit
              (builtins.genList (x: x) n);
        in
        {
          sq64 = countTransits (checkTypeLevel ctx0 (squashTower 64));
          sq256 = countTransits (checkTypeLevel ctx0 (squashTower 256));
          funext = countTransits (self.infer ctx0 T.mkFunext);
          lvlZero = countTransits (self.infer ctx0 T.mkLevelZero);
        };
      expected = {
        sq64 = { pushes = 0; pops = 0; yields = 1; };
        sq256 = { pushes = 0; pops = 0; yields = 4; };
        funext = { pushes = 0; pops = 0; yields = 0; };
        lvlZero = { pushes = 0; pops = 0; yields = 0; };
      };
    };
    # Errors inside budgeted helper windows must surface with the same
    # blame structure as the always-yield discipline. Expected values
    # pinned from the pre-budget checker: a pi tower whose innermost
    # codomain is not a type (former arms carry no blame positions), and
    # a boot-sum-elim motive whose lam body is not a type (the Motive
    # bracket fires identically through the budgeted checkMotive).
    "checktypelevel-entry-budget-error-blame-identical" = {
      expr =
        let
          childPath = err:
            if builtins.length (err.children or [ ]) > 0
            then
              let c = builtins.elemAt err.children 0; in
              [ c.position.tag ] ++ childPath c.error
            else [ ];
          badPi = builtins.foldl' (cod: _: T.mkPi "x" T.mkUnit cod)
            T.mkTt
            (builtins.genList (x: x) 8);
          r = runCheck (checkTypeLevel ctx0 badPi);
          badElim = T.mkBootSumElim T.mkUnit T.mkUnit
            (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkTt)
            (T.mkLam "a" T.mkUnit T.mkTt)
            (T.mkLam "b" T.mkUnit T.mkTt)
            (T.mkBootInl T.mkTt);
          rm = inferTm ctx0 badElim;
        in
        {
          pi = {
            msg = r.msg;
            trace = map (e: e.position.tag) r.error.detail.trace;
            childPath = childPath r.error;
          };
          motive = {
            msg = rm.msg;
            trace = map (e: e.position.tag) rm.error.detail.trace;
            childPath = childPath rm.error;
          };
        };
      expected = {
        pi = {
          msg = "no inference rule for term shape tt";
          trace = [ ];
          childPath = [ ];
        };
        motive = {
          msg = "no inference rule for term shape tt";
          trace = [ "Motive" ];
          childPath = [ "Motive" ];
        };
      };
    };

    "roundtrip-tt" = {
      expr = Q.nf [ ] (Q.nf [ ] T.mkTt) == Q.nf [ ] T.mkTt;
      expected = true;
    };
    "roundtrip-generated-zero" = {
      expr = Q.nf [ ] (Q.nf [ ] zeroTm) == Q.nf [ ] zeroTm;
      expected = true;
    };
    "roundtrip-generated-list" = {
      expr = Q.nf [ ] (Q.nf [ ] consZeroNilTm) == Q.nf [ ] consZeroNilTm;
      expected = true;
    };
    "roundtrip-pair" = {
      expr = Q.nf [ ] (Q.nf [ ] (T.mkPair T.mkTt T.mkTt))
        == Q.nf [ ] (T.mkPair T.mkTt T.mkTt);
      expected = true;
    };
    "roundtrip-app-beta" = {
      expr =
        let
          tm = T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt;
        in
        Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-let" = {
      expr =
        let tm = T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0);
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-pi" = {
      expr =
        let tm = T.mkPi "x" T.mkUnit T.mkUnit;
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-lam" = {
      expr =
        let tm = T.mkLam "x" T.mkUnit (T.mkVar 0);
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-sigma" = {
      expr =
        let tm = T.mkSigma "x" T.mkUnit T.mkUnit;
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-sum" = {
      expr =
        let tm = T.mkBootSum T.mkUnit T.mkString;
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-inl" = {
      expr =
        let tm = T.mkBootInl T.mkUnit T.mkString T.mkTt;
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-inr" = {
      expr =
        let tm = T.mkBootInr T.mkUnit T.mkString (T.mkStringLit "x");
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-eq" = {
      expr =
        let tm = T.mkBootEq T.mkUnit T.mkTt T.mkTt;
        in Q.nf [ ] (Q.nf [ ] tm) == Q.nf [ ] tm;
      expected = true;
    };
    "roundtrip-refl" = {
      expr = Q.nf [ ] (Q.nf [ ] T.mkBootRefl) == Q.nf [ ] T.mkBootRefl;
      expected = true;
    };
    "roundtrip-U" = {
      expr = Q.nf [ ] (Q.nf [ ] (T.mkU T.mkLevelZero)) == Q.nf [ ] (T.mkU T.mkLevelZero);
      expected = true;
    };
    "roundtrip-under-binder-var" = {
      expr =
        let env1 = [ (V.freshVar 0) ];
        in Q.nf env1 (Q.nf env1 (T.mkVar 0)) == Q.nf env1 (T.mkVar 0);
      expected = true;
    };
    "roundtrip-under-binder-pi" = {
      expr =
        let
          env1 = [ (V.freshVar 0) ];
          tm = T.mkPi "y" T.mkUnit (T.mkVar 1);
        in
        Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };
    "roundtrip-under-binder-lam" = {
      expr =
        let
          env1 = [ (V.freshVar 0) ];
          tm = T.mkLam "y" T.mkUnit (T.mkVar 1);
        in
        Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };

    "level-pi-with-type-var" = {
      expr =
        let
          ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
        in
        typeLvl (inferTm ctxB (T.mkPi "x" T.mkUnit (T.mkVar 1)));
      expected = 1;
    };
    "level-sigma-with-type-var" = {
      expr =
        let
          ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
        in
        typeLvl (inferTm ctxB (T.mkSigma "x" T.mkUnit (T.mkVar 1)));
      expected = 1;
    };
    "level-nested-pi" = {
      expr =
        let
          ctxA = extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)));
        in
        typeLvl (inferTm ctxA (T.mkPi "x" T.mkUnit (T.mkPi "y" T.mkUnit (T.mkVar 2))));
      expected = 2;
    };
    "level-app-returning-universe" = {
      expr =
        let
          fTy = vPi "x" vUnit (mkClosure [ ] (T.mkU (T.mkLevelSuc T.mkLevelZero)));
          ctxF = extend ctx0 "F" fTy;
        in
        typeLvl (inferTm ctxF (T.mkPi "y" (T.mkApp (T.mkVar 0) T.mkTt) T.mkUnit));
      expected = 1;
    };
    "level-sigma-mixed-vars" = {
      expr =
        let
          ctxAB = extend
            (extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero))))
            "B"
            (vU (V.vLevelSuc V.vLevelZero));
        in
        typeLvl (inferTm ctxAB (T.mkSigma "x" (T.mkVar 1) (T.mkVar 1)));
      expected = 2;
    };

    "checkTypeLevel-string" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkString));
      expected = 0;
    };
    "checkTypeLevel-int" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkInt));
      expected = 0;
    };
    "checkTypeLevel-float" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkFloat));
      expected = 0;
    };
    "checkTypeLevel-attrs" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkAttrs));
      expected = 0;
    };
    "checkTypeLevel-path" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkPath));
      expected = 0;
    };
    "checkTypeLevel-function" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkFunction));
      expected = 0;
    };
    "checkTypeLevel-any" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 T.mkAny));
      expected = 0;
    };
    "checkTypeLevel-eq" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 (T.mkBootEq T.mkUnit T.mkTt T.mkTt)));
      expected = 0;
    };

    "check-string-lit" = {
      expr = (checkTm ctx0 (T.mkStringLit "hello") vString).tag;
      expected = "string-lit";
    };
    "check-int-lit" = {
      expr = (checkTm ctx0 (T.mkIntLit 42) vInt).tag;
      expected = "int-lit";
    };
    "check-float-lit" = {
      expr = (checkTm ctx0 (T.mkFloatLit 3.14) vFloat).tag;
      expected = "float-lit";
    };
    "check-attrs-lit" = {
      expr = (checkTm ctx0 T.mkAttrsLit vAttrs).tag;
      expected = "attrs-lit";
    };
    "check-path-lit" = {
      expr = (checkTm ctx0 T.mkPathLit vPath).tag;
      expected = "path-lit";
    };
    "check-fn-lit" = {
      expr = (checkTm ctx0 T.mkFnLit vFunction).tag;
      expected = "fn-lit";
    };
    "check-any-lit" = {
      expr = (checkTm ctx0 T.mkAnyLit vAny).tag;
      expected = "any-lit";
    };
    "infer-string-lit" = {
      expr = (inferTm ctx0 (T.mkStringLit "hi")).type.tag;
      expected = "VString";
    };
    "infer-int-lit" = {
      expr = (inferTm ctx0 (T.mkIntLit 7)).type.tag;
      expected = "VInt";
    };
    "infer-float-lit" = {
      expr = (inferTm ctx0 (T.mkFloatLit 2.0)).type.tag;
      expected = "VFloat";
    };
    "infer-attrs-lit" = {
      expr = (inferTm ctx0 T.mkAttrsLit).type.tag;
      expected = "VAttrs";
    };
    "infer-path-lit" = {
      expr = (inferTm ctx0 T.mkPathLit).type.tag;
      expected = "VPath";
    };
    "infer-fn-lit" = {
      expr = (inferTm ctx0 T.mkFnLit).type.tag;
      expected = "VFunction";
    };
    "infer-any-lit" = {
      expr = (inferTm ctx0 T.mkAnyLit).type.tag;
      expected = "VAny";
    };
    "reject-string-lit-as-int" = {
      expr = (checkTm ctx0 (T.mkStringLit "hi") vInt) ? error;
      expected = true;
    };
    "reject-int-lit-as-string" = {
      expr = (checkTm ctx0 (T.mkIntLit 42) vString) ? error;
      expected = true;
    };
    "reject-float-lit-as-unit" = {
      expr = (checkTm ctx0 (T.mkFloatLit 1.0) vUnit) ? error;
      expected = true;
    };
    "reject-attrs-lit-as-unit" = {
      expr = (checkTm ctx0 T.mkAttrsLit vUnit) ? error;
      expected = true;
    };
    "reject-string-lit-as-unit" = {
      expr = (checkTm ctx0 (T.mkStringLit "x") vUnit) ? error;
      expected = true;
    };

    "infer-desc-ret" = {
      expr = (inferTm ctx0 encRet).type.tag;
      expected = "VMu";
    };
    "infer-desc-desc-app-type-tag" = {
      expr = (inferTm ctx0
        (T.mkDescDescApp T.mkUnit T.mkLevelZero)).type.tag;
      expected = "VDesc";
    };
    "infer-desc-desc-app-level" = {
      expr = typeLvl (inferTm ctx0
        (T.mkDescDescApp T.mkUnit T.mkLevelZero));
      expected = 1;
    };
    "infer-desc-arg" = {
      expr = (inferTm ctx0 encArg).type.tag;
      expected = "VMu";
    };
    "infer-desc-arg-level-one" = {
      expr = (inferTm ctx0 encArg1).type.tag;
      expected = "VMu";
    };
    "check-desc-arg-level-one" = {
      expr =
        let
          checked = checkTm ctx0
            encArg1
            (V.vDesc (V.vLevelSuc V.vLevelZero) vUnit);
        in
        (E.eval [ ] checked).tag;
      expected = "VDescCon";
    };
    "infer-desc-rec" = {
      expr = (inferTm ctx0 encRec).type.tag;
      expected = "VMu";
    };
    "infer-desc-pi" = {
      expr = (inferTm ctx0 encPi).type.tag;
      expected = "VMu";
    };
    "infer-desc-pi-level-one" = {
      expr = (inferTm ctx0 encPi1).type.tag;
      expected = "VMu";
    };
    "infer-mu" = {
      expr = typeLvl (inferTm ctx0
        (T.mkMu T.mkUnit
          encRet
          T.mkTt));
      expected = 0;
    };
    "checktype-desc" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 (T.mkDesc T.mkLevelZero T.mkUnit)));
      expected = 1;
    };
    "checktype-mu" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0
        (T.mkMu T.mkUnit
          encRet
          T.mkTt)));
      expected = 0;
    };
    "infer-desc-con" = {
      expr = (inferTm ctx0
        (T.mkDescCon
          encRetD
          T.mkTt
          T.mkBootRefl)).type.tag;
      expected = "VMu";
    };
    "check-desc-con" = {
      expr =
        let
          encRetVal = E.eval [ ] (inferTm ctx0 encRetD).term;
        in
        (checkTm ctx0
          (T.mkDescCon encRetD T.mkTt T.mkBootRefl)
          (vMu vUnit encRetVal vTt)).tag;
      expected = "desc-con";
    };
    "check-desc-con-nonlinear-plus-left" = {
      expr =
        let
          DVal = E.eval [ ] (inferTm ctx0 encNonLinearD).term;
          payload = T.mkBootInl T.mkUnit T.mkUnit T.mkBootRefl;
        in
        (checkTm ctx0
          (T.mkDescCon encNonLinearD T.mkTt payload)
          (vMu vUnit DVal vTt)).tag;
      expected = "desc-con";
    };
    "reject-desc-con-bad-payload" = {
      expr = (inferTm ctx0
        (T.mkDescCon
          encRetD
          T.mkTt
          T.mkTt)) ? error;
      expected = true;
    };
    "infer-desc-ind-ret" = {
      expr =
        let
          D = encRetD;
        in
        (inferTm ctx0 (T.mkDescInd D
          (T.mkLam "i" T.mkUnit
            (T.mkLam "_" (T.mkMu T.mkUnit D (T.mkVar 0)) T.mkUnit))
          (T.mkLam "i" T.mkUnit
            (T.mkLam "d" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0))
              (T.mkLam "_" T.mkUnit T.mkTt)))
          T.mkTt
          (T.mkDescCon D T.mkTt T.mkBootRefl))).type.tag;
      expected = "VUnit";
    };

    "infer-funext-type-tag" = {
      expr = (inferTm ctx0 T.mkFunext).type.tag;
      expected = "VPi";
    };
    "infer-funext-type-roundtrips-to-funextTypeTm" = {
      expr =
        let
          r = inferTm ctx0 T.mkFunext;
        in
        Q.quote 0 r.type == T.funextTypeTm;
      expected = true;
    };
    "infer-funext-type-binds-level-j" = {
      expr =
        let
          r = inferTm ctx0 T.mkFunext;
          tyTm = Q.quote 0 r.type;
        in
        tyTm.name;
      expected = "j";
    };
    "infer-funext-type-binds-level-k" = {
      expr =
        let
          r = inferTm ctx0 T.mkFunext;
          tyTm = Q.quote 0 r.type;
        in
        tyTm.codomain.name;
      expected = "k";
    };
    "check-funext-against-its-type" = {
      expr =
        let
          funextTy = E.eval [ ] T.funextTypeTm;
        in
        (checkTm ctx0 T.mkFunext funextTy).tag;
      expected = "funext";
    };
    "check-funext-reflexive-application" = {
      expr =
        let
          A = T.mkUnit;
          Bty = T.mkPi "_" A (T.mkU T.mkLevelZero);
          B = T.mkAnn (T.mkLam "_" A A) Bty;
          fTy = T.mkPi "a" A A;
          f = T.mkAnn (T.mkLam "_" A T.mkTt) fTy;
          ptTy = T.mkPi "a" A (T.mkBootEq A T.mkTt T.mkTt);
          pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
          term = T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        T.mkFunext
                        (T.mkLevelLit 0))
                      (T.mkLevelLit 0))
                    A)
                  B)
                f)
              f)
            pointwise;
          expectedTy = V.vBootEq
            (V.vPi "a" V.vUnit (V.mkClosure [ ] A))
            (E.eval [ ] f)
            (E.eval [ ] f);
        in
        (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-at-level-one" = {
      expr =
        let
          A = T.mkU T.mkLevelZero;
          Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
          B = T.mkAnn (T.mkLam "_" A A) Bty;
          fTy = T.mkPi "_" A A;
          f = T.mkAnn (T.mkLam "_" A T.mkUnit) fTy;
          ptTy = T.mkPi "_" A (T.mkBootEq A T.mkUnit T.mkUnit);
          pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
          term = T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        T.mkFunext
                        (T.mkLevelLit 1))
                      (T.mkLevelLit 1))
                    A)
                  B)
                f)
              f)
            pointwise;
          fVal = E.eval [ ] (inferTm ctx0 f).term;
          expectedTy = V.vBootEq
            (V.vPi "_" (V.vU V.vLevelZero) (V.mkClosure [ ] A))
            fVal
            fVal;
        in
        (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-heterogeneous-j0-k1" = {
      expr =
        let
          A = T.mkUnit;
          descTy = T.mkDesc T.mkLevelZero T.mkUnit;
          Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
          B = T.mkAnn (T.mkLam "_" A descTy) Bty;
          fTy = T.mkPi "_" A descTy;
          f = T.mkAnn (T.mkLam "_" A encRet) fTy;
          ptTy = T.mkPi "_" A (T.mkBootEq descTy encRet encRet);
          pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
          term = T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        T.mkFunext
                        (T.mkLevelLit 0))
                      (T.mkLevelLit 1))
                    A)
                  B)
                f)
              f)
            pointwise;
          fVal = E.eval [ ] (inferTm ctx0 f).term;
          expectedTy = V.vBootEq
            (V.vPi "_" V.vUnit (V.mkClosure [ ] descTy))
            fVal
            fVal;
        in
        (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };

    "infer-interp-d-ret" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encRetD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-ret-level" = {
      expr = typeLvl (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encRetD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt));
      expected = 0;
    };
    "infer-interp-d-rec" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encRecD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-wrong-X-rejected" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encRetD
        (T.mkLam "_" T.mkUnit T.mkTt)
        T.mkTt)) ? error;
      expected = true;
    };
    "infer-all-d-ret" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encRetD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        T.mkBootRefl)).type.tag;
      expected = "VU";
    };
    "infer-all-d-K-level" = {
      expr = typeLvl (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encRetD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        T.mkBootRefl));
      expected = 0;
    };
    "infer-everywhere-d-ret" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encRetD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit T.mkTt))
        T.mkTt
        T.mkBootRefl)).type.tag;
      expected = "VUnit";
    };

    # interpD on the non-`ret` summands. `interpD ℓ I D X i` always
    # synthesises to `U(ℓ)` regardless of D's outer constructor, so
    # `.type.tag == "VU"` is the acceptance bar. Rejection variants
    # mirror `infer-interp-d-wrong-X-rejected` with a mistyped `X`.
    "infer-interp-d-arg" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encArgD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-arg-wrong-X-rejected" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encArgD
        (T.mkLam "_" T.mkUnit T.mkTt)
        T.mkTt)) ? error;
      expected = true;
    };
    "infer-interp-d-pi" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encPiD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-pi-wrong-X-rejected" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encPiD
        (T.mkLam "_" T.mkUnit T.mkTt)
        T.mkTt)) ? error;
      expected = true;
    };
    "infer-interp-d-plus" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encPlusD
        (T.mkLam "_" T.mkUnit T.mkUnit)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-plus-wrong-X-rejected" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        encPlusD
        (T.mkLam "_" T.mkUnit T.mkTt)
        T.mkTt)) ? error;
      expected = true;
    };

    # allD on the non-`ret` summands. `allD ℓ I D K X M i d` always
    # synthesises to `U(K)` regardless of D's shape, so `.type.tag ==
    # "VU"` is the acceptance bar.
    #
    # Payloads (computed via the kernel reduction rules in `term.nix`):
    #   encArg (Σ s:Unit. Eq Unit tt tt)       → `pair tt refl`
    #   encRec (Σ _:Unit. Eq Unit tt tt)       → `pair tt refl`
    #   encPi  (Σ _:(Π s:Unit.Unit). Eq …)     → `pair (λ_:Unit. tt) refl`
    #   encPlus (Eq … ⊎ Eq …)                  → `inl refl`
    "infer-all-d-arg" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encArgD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        (T.mkPair T.mkTt T.mkBootRefl))).type.tag;
      expected = "VU";
    };
    "infer-all-d-rec" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encRecD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        (T.mkPair T.mkTt T.mkBootRefl))).type.tag;
      expected = "VU";
    };
    "infer-all-d-pi" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encPiD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        (T.mkPair (T.mkLam "_" T.mkUnit T.mkTt) T.mkBootRefl))).type.tag;
      expected = "VU";
    };
    "infer-all-d-plus" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        encPlusD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        T.mkTt
        (T.mkBootInl
          (T.mkBootEq T.mkUnit T.mkTt T.mkTt)
          (T.mkBootEq T.mkUnit T.mkTt T.mkTt)
          T.mkBootRefl))).type.tag;
      expected = "VU";
    };

    # everywhereD acceptance on the non-`ret` summands. The result
    # type is `allD ℓ I D K X M i d`, which itself is `U(K)` after
    # reduction; the exact reduced form depends on D's shape, so the
    # acceptance bar here is structural: the synthesis produces a
    # `.type` field (no `.error`).
    "infer-everywhere-d-arg" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encArgD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit T.mkTt))
        T.mkTt
        (T.mkPair T.mkTt T.mkBootRefl))) ? type;
      expected = true;
    };
    "infer-everywhere-d-rec" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encRecD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit T.mkTt))
        T.mkTt
        (T.mkPair T.mkTt T.mkBootRefl))) ? type;
      expected = true;
    };
    "infer-everywhere-d-pi" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encPiD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit T.mkTt))
        T.mkTt
        (T.mkPair (T.mkLam "_" T.mkUnit T.mkTt) T.mkBootRefl))) ? type;
      expected = true;
    };
    "infer-everywhere-d-plus" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        encPlusD
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkUnit)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkUnit T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit T.mkTt))
        T.mkTt
        (T.mkBootInl
          (T.mkBootEq T.mkUnit T.mkTt T.mkTt)
          (T.mkBootEq T.mkUnit T.mkTt T.mkTt)
          T.mkBootRefl))) ? type;
      expected = true;
    };
  };
}
