# Inline tests for the type-checking kernel: context ops, bidirectional
# dispatch, motive checking, primitive literals, Desc/Mu, generated data,
# universe levels, and trampoline stress.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  Q = fx.tc.quote;
  H = fx.tc.hoas;
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
  nilNatTm = H.elab (H.nil H.nat);
  consZeroNilTm = H.elab (H.cons H.nat H.zero (H.nil H.nat));
  natTyVal = E.eval [] natTyTm;
  listNatVal = E.eval [] listNatTm;

  bigNatTm = H.elab (H.natLit 5000);
  bigListTm = H.elab (builtins.foldl'
    (acc: _: H.cons H.nat H.zero acc)
    (H.nil H.nat)
    (builtins.genList (x: x) 5000));

  unitFn = S: H.ann (H.lam "_" S (_: H.tt)) (H.forall "_" S (_: H.unit));
  encRet = H.elab (H.retI H.unit 0 H.tt);
  encArg = H.elab (H.descArg H.unit 0 H.unit (_: H.retI H.unit 0 H.tt));
  encArg1 = H.elab (H.descArg H.unit 1 (H.u 0) (_: H.retI H.unit 1 H.tt));
  encRec = H.elab (H.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
  encPi = H.elab (H.piI H.unit 0 H.unit (unitFn H.unit) (H.retI H.unit 0 H.tt));
  encPi1 = H.elab (H.piI H.unit 1 (H.u 0) (unitFn (H.u 0)) (H.retI H.unit 1 H.tt));
  encRetD = T.mkAnn encRet (T.mkDesc T.mkLevelZero T.mkUnit);
  encArgD = T.mkAnn encArg (T.mkDesc T.mkLevelZero T.mkUnit);
  encRecD = T.mkAnn encRec (T.mkDesc T.mkLevelZero T.mkUnit);
in {
  scope = {};
  tests = {
    "ctx-empty-depth" = { expr = ctx0.depth; expected = 0; };
    "ctx-extend-depth" = { expr = ctx1.depth; expected = 1; };
    "ctx-lookup" = { expr = (lookupType ctx1 0).tag; expected = "VUnit"; };

    "check-id" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkUnit (T.mkVar 0))
        (vPi "x" vUnit (mkClosure [] T.mkUnit))).tag;
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
        (vSigma "x" vUnit (mkClosure [] T.mkUnit))).tag;
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
      expr = let
        idFn = T.mkAnn (T.mkLam "x" T.mkUnit (T.mkVar 0))
          (T.mkPi "x" T.mkUnit T.mkUnit);
      in (inferTm ctx0 (T.mkApp idFn T.mkTt)).type.tag;
      expected = "VUnit";
    };
    "infer-fst" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x"))
          (T.mkSigma "x" T.mkUnit T.mkString);
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VUnit";
    };
    "infer-snd" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x"))
          (T.mkSigma "x" T.mkUnit T.mkString);
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VString";
    };
    "infer-pair-via-ann" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkUnit T.mkString;
        p = T.mkAnn (T.mkPair T.mkTt (T.mkStringLit "x")) sigTy;
      in (inferTm ctx0 p).type.tag;
      expected = "VSigma";
    };
    "reject-pair-infer-bare" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)) ? error;
      expected = true;
    };
    "reject-pair-infer-bare-msg" = {
      expr = (inferTm ctx0 (T.mkPair T.mkTt T.mkTt)).msg;
      expected = "cannot infer type";
    };
    "check-let" = {
      expr = (checkTm ctx0 (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0)) vUnit).tag;
      expected = "let";
    };
    "check-poly-id" = {
      expr = let
        ty = vPi "A" (vU V.vLevelZero)
          (mkClosure [] (T.mkPi "x" (T.mkVar 0) (T.mkVar 1)));
        tm = T.mkLam "A" (T.mkU T.mkLevelZero)
          (T.mkLam "x" (T.mkVar 0) (T.mkVar 0));
      in (checkTm ctx0 tm ty).tag;
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
        (vSigma "x" vUnit (mkClosure [] T.mkString))) ? error;
      expected = true;
    };
    "reject-pair-snd-mismatch-msg" = {
      expr = (checkTm ctx0 (T.mkPair T.mkTt T.mkTt)
        (vSigma "x" vUnit (mkClosure [] T.mkString))).msg;
      expected = "cannot infer type";
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
        (T.mkU (T.mkLevelSuc T.mkLevelZero)) (vU V.vLevelZero)) ? error;
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
      expr = let
        nested = builtins.foldl' (body: _:
          T.mkLet "x" T.mkUnit T.mkTt body
        ) T.mkTt (builtins.genList (x: x) 100);
      in (checkTm ctx0 nested vUnit).tag;
      expected = "let";
    };
    "stress-nested-pi" = {
      expr = let
        nested = builtins.foldl' (acc: _: T.mkPi "x" T.mkUnit acc)
          T.mkUnit (builtins.genList (x: x) 500);
      in typeLvl (inferTm ctx0 nested);
      expected = 0;
    };

    "roundtrip-tt" = {
      expr = Q.nf [] (Q.nf [] T.mkTt) == Q.nf [] T.mkTt;
      expected = true;
    };
    "roundtrip-generated-zero" = {
      expr = Q.nf [] (Q.nf [] zeroTm) == Q.nf [] zeroTm;
      expected = true;
    };
    "roundtrip-generated-list" = {
      expr = Q.nf [] (Q.nf [] consZeroNilTm) == Q.nf [] consZeroNilTm;
      expected = true;
    };
    "roundtrip-pair" = {
      expr = Q.nf [] (Q.nf [] (T.mkPair T.mkTt T.mkTt))
        == Q.nf [] (T.mkPair T.mkTt T.mkTt);
      expected = true;
    };
    "roundtrip-app-beta" = {
      expr = let
        tm = T.mkApp (T.mkLam "x" T.mkUnit (T.mkVar 0)) T.mkTt;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-let" = {
      expr = let tm = T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-pi" = {
      expr = let tm = T.mkPi "x" T.mkUnit T.mkUnit;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-lam" = {
      expr = let tm = T.mkLam "x" T.mkUnit (T.mkVar 0);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-sigma" = {
      expr = let tm = T.mkSigma "x" T.mkUnit T.mkUnit;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-sum" = {
      expr = let tm = T.mkBootSum T.mkUnit T.mkString;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inl" = {
      expr = let tm = T.mkBootInl T.mkUnit T.mkString T.mkTt;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inr" = {
      expr = let tm = T.mkBootInr T.mkUnit T.mkString (T.mkStringLit "x");
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-eq" = {
      expr = let tm = T.mkBootEq T.mkUnit T.mkTt T.mkTt;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-refl" = {
      expr = Q.nf [] (Q.nf [] T.mkBootRefl) == Q.nf [] T.mkBootRefl;
      expected = true;
    };
    "roundtrip-U" = {
      expr = Q.nf [] (Q.nf [] (T.mkU T.mkLevelZero)) == Q.nf [] (T.mkU T.mkLevelZero);
      expected = true;
    };
    "roundtrip-under-binder-var" = {
      expr = let env1 = [ (V.freshVar 0) ];
      in Q.nf env1 (Q.nf env1 (T.mkVar 0)) == Q.nf env1 (T.mkVar 0);
      expected = true;
    };
    "roundtrip-under-binder-pi" = {
      expr = let
        env1 = [ (V.freshVar 0) ];
        tm = T.mkPi "y" T.mkUnit (T.mkVar 1);
      in Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };
    "roundtrip-under-binder-lam" = {
      expr = let
        env1 = [ (V.freshVar 0) ];
        tm = T.mkLam "y" T.mkUnit (T.mkVar 1);
      in Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };

    "level-pi-with-type-var" = {
      expr = let
        ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
      in typeLvl (inferTm ctxB (T.mkPi "x" T.mkUnit (T.mkVar 1)));
      expected = 1;
    };
    "level-sigma-with-type-var" = {
      expr = let
        ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
      in typeLvl (inferTm ctxB (T.mkSigma "x" T.mkUnit (T.mkVar 1)));
      expected = 1;
    };
    "level-nested-pi" = {
      expr = let
        ctxA = extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)));
      in typeLvl (inferTm ctxA (T.mkPi "x" T.mkUnit (T.mkPi "y" T.mkUnit (T.mkVar 2))));
      expected = 2;
    };
    "level-app-returning-universe" = {
      expr = let
        fTy = vPi "x" vUnit (mkClosure [] (T.mkU (T.mkLevelSuc T.mkLevelZero)));
        ctxF = extend ctx0 "F" fTy;
      in typeLvl (inferTm ctxF (T.mkPi "y" (T.mkApp (T.mkVar 0) T.mkTt) T.mkUnit));
      expected = 1;
    };
    "level-sigma-mixed-vars" = {
      expr = let
        ctxAB = extend
          (extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero))))
          "B"
          (vU (V.vLevelSuc V.vLevelZero));
      in typeLvl (inferTm ctxAB (T.mkSigma "x" (T.mkVar 1) (T.mkVar 1)));
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
        in (E.eval [] checked).tag;
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
          T.mkTt T.mkBootRefl)).type.tag;
      expected = "VMu";
    };
    "check-desc-con" = {
      expr =
        let
          encRetVal = E.eval [] (inferTm ctx0 encRetD).term;
        in (checkTm ctx0
              (T.mkDescCon encRetD T.mkTt T.mkBootRefl)
              (vMu vUnit encRetVal vTt)).tag;
      expected = "desc-con";
    };
    "reject-desc-con-bad-payload" = {
      expr = (inferTm ctx0
        (T.mkDescCon
          encRetD
          T.mkTt T.mkTt)) ? error;
      expected = true;
    };
    "infer-desc-ind-ret" = {
      expr = let
        D = encRetD;
      in (inferTm ctx0 (T.mkDescInd D
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
      expr = let
        r = inferTm ctx0 T.mkFunext;
      in Q.quote 0 r.type == T.funextTypeTm;
      expected = true;
    };
    "infer-funext-type-binds-level-j" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.name;
      expected = "j";
    };
    "infer-funext-type-binds-level-k" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.codomain.name;
      expected = "k";
    };
    "check-funext-against-its-type" = {
      expr = let
        funextTy = E.eval [] T.funextTypeTm;
      in (checkTm ctx0 T.mkFunext funextTy).tag;
      expected = "funext";
    };
    "check-funext-reflexive-application" = {
      expr = let
        A = T.mkUnit;
        Bty = T.mkPi "_" A (T.mkU T.mkLevelZero);
        B = T.mkAnn (T.mkLam "_" A A) Bty;
        fTy = T.mkPi "a" A A;
        f = T.mkAnn (T.mkLam "_" A T.mkTt) fTy;
        ptTy = T.mkPi "a" A (T.mkBootEq A T.mkTt T.mkTt);
        pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 0)) (T.mkLevelLit 0)) A) B) f) f) pointwise;
        expectedTy = V.vBootEq
          (V.vPi "a" V.vUnit (V.mkClosure [] A))
          (E.eval [] f)
          (E.eval [] f);
      in (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-at-level-one" = {
      expr = let
        A = T.mkU T.mkLevelZero;
        Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
        B = T.mkAnn (T.mkLam "_" A A) Bty;
        fTy = T.mkPi "_" A A;
        f = T.mkAnn (T.mkLam "_" A T.mkUnit) fTy;
        ptTy = T.mkPi "_" A (T.mkBootEq A T.mkUnit T.mkUnit);
        pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 1)) (T.mkLevelLit 1)) A) B) f) f) pointwise;
        fVal = E.eval [] (inferTm ctx0 f).term;
        expectedTy = V.vBootEq
          (V.vPi "_" (V.vU V.vLevelZero) (V.mkClosure [] A))
          fVal
          fVal;
      in (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-heterogeneous-j0-k1" = {
      expr = let
        A = T.mkUnit;
        descTy = T.mkDesc T.mkLevelZero T.mkUnit;
        Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
        B = T.mkAnn (T.mkLam "_" A descTy) Bty;
        fTy = T.mkPi "_" A descTy;
        f = T.mkAnn (T.mkLam "_" A encRet) fTy;
        ptTy = T.mkPi "_" A (T.mkBootEq descTy encRet encRet);
        pointwise = T.mkAnn (T.mkLam "_" A T.mkBootRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 0)) (T.mkLevelLit 1)) A) B) f) f) pointwise;
        fVal = E.eval [] (inferTm ctx0 f).term;
        expectedTy = V.vBootEq
          (V.vPi "_" V.vUnit (V.mkClosure [] descTy))
          fVal
          fVal;
      in (checkTm ctx0 term expectedTy).tag;
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
  };
}
