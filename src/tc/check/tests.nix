# Inline tests for the type-checking kernel: context ops, bidirectional
# dispatch (check and infer), motive checking, eliminator typing,
# cumulativity, type-formation levels, primitive literals, Desc/Mu, and
# trampoline stress. Also carries eval∘quote∘eval roundtrip checks for
# every term shape touched by the checker.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  Q = fx.tc.quote;

  inherit (self)
    checkType checkTypeLevel
    emptyCtx extend lookupType
    runCheck checkTm inferTm;

  inherit (V) vNat vZero vSucc vBool vPi vSigma
    vList vUnit vVoid vSum vEq vU mkClosure vTt
    vString vInt vFloat vAttrs vPath vFunction vAny
    vDescRet vMu;

  ctx0 = emptyCtx;
  ctx1 = extend ctx0 "x" vNat;
  ctxV = extend ctx0 "v" vVoid;
in {
  scope = {};
  tests = {
    "ctx-empty-depth" = { expr = ctx0.depth; expected = 0; };
    "ctx-extend-depth" = { expr = ctx1.depth; expected = 1; };
    "ctx-lookup" = { expr = (lookupType ctx1 0).tag; expected = "VNat"; };

    "check-id" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkNat (T.mkVar 0))
        (vPi "x" vNat (mkClosure [] T.mkNat))).tag;
      expected = "lam";
    };

    "check-zero" = {
      expr = (checkTm ctx0 T.mkZero vNat).tag;
      expected = "zero";
    };

    "check-succ" = {
      expr = (checkTm ctx0 (T.mkSucc T.mkZero) vNat).tag;
      expected = "succ";
    };

    "check-true" = {
      expr = (checkTm ctx0 T.mkTrue vBool).tag;
      expected = "true";
    };

    "check-refl" = {
      expr = (checkTm ctx0 T.mkRefl (vEq vNat vZero vZero)).tag;
      expected = "refl";
    };

    "check-pair" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkTrue)
        (vSigma "x" vNat (mkClosure [] T.mkBool))).tag;
      expected = "pair";
    };

    "check-nil" = {
      expr = (checkTm ctx0 (T.mkNil T.mkNat) (vList vNat)).tag;
      expected = "nil";
    };

    "check-cons" = {
      expr = (checkTm ctx0
        (T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat)) (vList vNat)).tag;
      expected = "cons";
    };

    "check-tt" = {
      expr = (checkTm ctx0 T.mkTt vUnit).tag;
      expected = "tt";
    };

    "check-inl" = {
      expr = (checkTm ctx0 (T.mkInl T.mkNat T.mkBool T.mkZero) (vSum vNat vBool)).tag;
      expected = "inl";
    };

    "check-inr" = {
      expr = (checkTm ctx0 (T.mkInr T.mkNat T.mkBool T.mkTrue) (vSum vNat vBool)).tag;
      expected = "inr";
    };

    "infer-var" = {
      expr = (inferTm ctx1 (T.mkVar 0)).type.tag;
      expected = "VNat";
    };

    "infer-ann" = {
      expr = (inferTm ctx0 (T.mkAnn T.mkZero T.mkNat)).type.tag;
      expected = "VNat";
    };

    "infer-U0" = {
      expr = (inferTm ctx0 (T.mkU 0)).type.level;
      expected = 1;
    };

    "infer-U1" = {
      expr = (inferTm ctx0 (T.mkU 1)).type.level;
      expected = 2;
    };

    "infer-nat-type" = {
      expr = (inferTm ctx0 T.mkNat).type.level;
      expected = 0;
    };

    "infer-pi-type" = {
      expr = (inferTm ctx0 (T.mkPi "x" T.mkNat T.mkNat)).type.level;
      expected = 0;
    };

    "infer-app" = {
      expr = let
        idFn = T.mkAnn (T.mkLam "x" T.mkNat (T.mkVar 0)) (T.mkPi "x" T.mkNat T.mkNat);
      in (inferTm ctx0 (T.mkApp idFn T.mkZero)).type.tag;
      expected = "VNat";
    };

    "infer-fst" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue)
          (T.mkSigma "x" T.mkNat T.mkBool);
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VNat";
    };

    "infer-snd" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue)
          (T.mkSigma "x" T.mkNat T.mkBool);
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VBool";
    };

    # Dependent Snd: Σ(b:Bool). if b then Nat else Bool.
    "infer-snd-dependent" = {
      expr = let
        motive = T.mkLam "b" T.mkBool (T.mkU 0);
        sndBody = T.mkBoolElim motive T.mkNat T.mkBool (T.mkVar 0);
        sigTy = T.mkSigma "b" T.mkBool sndBody;
        pair = T.mkAnn (T.mkPair T.mkTrue T.mkZero) sigTy;
      in (inferTm ctx0 (T.mkSnd pair)).type.tag;
      expected = "VNat";
    };

    "infer-pair-via-ann" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkBool;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue) sigTy;
      in (inferTm ctx0 p).type.tag;
      expected = "VSigma";
    };

    "infer-fst-ann-pair" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkBool;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue) sigTy;
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VNat";
    };
    "infer-snd-ann-pair" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkBool;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue) sigTy;
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VBool";
    };

    "infer-pair-dependent" = {
      expr = let
        motive = T.mkLam "b" T.mkBool (T.mkU 0);
        sndBody = T.mkBoolElim motive T.mkNat T.mkBool (T.mkVar 0);
        sigTy = T.mkSigma "b" T.mkBool sndBody;
        p = T.mkAnn (T.mkPair T.mkTrue T.mkZero) sigTy;
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VNat";
    };

    # Bare pairs cannot be inferred (introduction forms check, not synthesize).
    "reject-pair-infer-bare" = {
      expr = (inferTm ctx0 (T.mkPair T.mkZero T.mkTrue)) ? error;
      expected = true;
    };
    "reject-pair-infer-bare-msg" = {
      expr = (inferTm ctx0 (T.mkPair T.mkZero T.mkTrue)).msg;
      expected = "cannot infer type";
    };

    "check-let" = {
      expr = (checkTm ctx0 (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0)) vNat).tag;
      expected = "let";
    };

    # Dependent function: Lam(A, U(0), Lam(x, Var(0), Var(0)))
    "check-poly-id" = {
      expr = let
        ty = vPi "A" (vU 0) (mkClosure [] (T.mkPi "x" (T.mkVar 0) (T.mkVar 1)));
        tm = T.mkLam "A" (T.mkU 0) (T.mkLam "x" (T.mkVar 0) (T.mkVar 0));
      in (checkTm ctx0 tm ty).tag;
      expected = "lam";
    };

    "infer-bool-elim" = {
      expr = (inferTm ctx0 (T.mkBoolElim
        (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkTrue)).type.tag;
      expected = "VNat";
    };

    # Non-lambda motive: exercises checkMotive infer path.
    "infer-bool-elim-nonlam-motive" = {
      expr = let
        motive = T.mkAnn
          (T.mkLam "b" T.mkBool T.mkNat)
          (T.mkPi "b" T.mkBool (T.mkU 0));
      in (inferTm ctx0 (T.mkBoolElim motive T.mkZero (T.mkSucc T.mkZero) T.mkTrue)).type.tag;
      expected = "VNat";
    };

    "infer-absurd" = {
      expr = (inferTm ctxV (T.mkAbsurd T.mkNat (T.mkVar 0))).type.tag;
      expected = "VNat";
    };

    "infer-list-elim" = {
      expr = (inferTm ctx0 (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
        T.mkZero
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
          (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
        (T.mkNil T.mkNat))).type.tag;
      expected = "VNat";
    };

    "infer-sum-elim" = {
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "b" T.mkBool T.mkZero)
        (T.mkInl T.mkNat T.mkBool T.mkZero))).type.tag;
      expected = "VNat";
    };

    "infer-j" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat
          (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 1)) T.mkNat))
        T.mkZero
        T.mkZero
        T.mkRefl)).type.tag;
      expected = "VNat";
    };

    "reject-zero-bool" = {
      expr = (checkTm ctx0 T.mkZero vBool) ? error;
      expected = true;
    };

    # Universe violation: U(0) : U(0) rejected.
    "reject-U0-U0" = {
      expr = (checkTm ctx0 (T.mkU 0) (vU 0)) ? error;
      expected = true;
    };

    "reject-refl-unequal" = {
      expr = (checkTm ctx0 T.mkRefl (vEq vNat vZero (vSucc vZero))) ? error;
      expected = true;
    };

    "reject-app-non-fn" = {
      expr = (inferTm ctx0 (T.mkApp (T.mkAnn T.mkZero T.mkNat) T.mkZero)) ? error;
      expected = true;
    };

    "reject-fst-non-pair" = {
      expr = (inferTm ctx0 (T.mkFst (T.mkAnn T.mkZero T.mkNat))) ? error;
      expected = true;
    };

    # Unbound var in empty context — force the type to trigger throw.
    "reject-unbound-var" = {
      expr = (builtins.tryEval (builtins.deepSeq (inferTm ctx0 (T.mkVar 0)) true)).success;
      expected = false;
    };

    "reject-nat-elim-bad-motive" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkTrue)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        T.mkZero)) ? error;
      expected = true;
    };

    "reject-pair-snd-mismatch" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkZero)
        (vSigma "x" vNat (mkClosure [] T.mkBool))) ? error;
      expected = true;
    };
    "reject-pair-snd-mismatch-msg" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkZero)
        (vSigma "x" vNat (mkClosure [] T.mkBool))).msg;
      expected = "cannot infer type";
    };

    # J motive with wrong inner domain.
    "reject-j-motive-wrong-inner-domain" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkAnn
          (T.mkLam "y" T.mkNat
            (T.mkLam "e" T.mkBool (T.mkU 0)))
          (T.mkPi "y" T.mkNat (T.mkPi "e" T.mkBool (T.mkU 1))))
        T.mkZero
        T.mkZero
        T.mkRefl)) ? error;
      expected = true;
    };
    "reject-j-motive-wrong-inner-domain-msg" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkAnn
          (T.mkLam "y" T.mkNat
            (T.mkLam "e" T.mkBool (T.mkU 0)))
          (T.mkPi "y" T.mkNat (T.mkPi "e" T.mkBool (T.mkU 1))))
        T.mkZero
        T.mkZero
        T.mkRefl)).msg;
      expected = "J motive inner domain must be Eq(A, a, y)";
    };

    "reject-lam-against-non-pi" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkNat (T.mkVar 0)) vNat) ? error;
      expected = true;
    };

    "check-cumulativity" = {
      expr = (checkTm ctx0 T.mkNat (vU 1)).tag;
      expected = "nat";
    };

    "check-U0-in-U1" = {
      expr = (checkTm ctx0 (T.mkU 0) (vU 1)).tag;
      expected = "U";
    };

    # Downward cumulativity rejected: U(1):U(2), not convertible to U(0).
    "reject-U1-in-U0" = {
      expr = (checkTm ctx0 (T.mkU 1) (vU 0)) ? error;
      expected = true;
    };

    "reject-nat-elim-bool-scrut" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        T.mkTrue)) ? error;
      expected = true;
    };

    "reject-bool-elim-nat-scrut" = {
      expr = (inferTm ctx0 (T.mkBoolElim
        (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero)
        T.mkZero)) ? error;
      expected = true;
    };

    "reject-list-elim-nat-scrut" = {
      expr = (inferTm ctx0 (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
        T.mkZero
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
          (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
        T.mkZero)) ? error;
      expected = true;
    };

    "reject-sum-elim-nat-scrut" = {
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "b" T.mkBool T.mkZero)
        T.mkZero)) ? error;
      expected = true;
    };

    "infer-eq-type" = {
      expr = (inferTm ctx0 (T.mkEq T.mkNat T.mkZero T.mkZero)).type.tag;
      expected = "VU";
    };

    "infer-sigma-type" = {
      expr = (inferTm ctx0 (T.mkSigma "x" T.mkNat T.mkBool)).type.tag;
      expected = "VU";
    };

    "infer-sum-type" = {
      expr = (inferTm ctx0 (T.mkSum T.mkNat T.mkBool)).type.tag;
      expected = "VU";
    };

    "infer-list-type" = {
      expr = (inferTm ctx0 (T.mkList T.mkNat)).type.tag;
      expected = "VU";
    };

    "checktype-pi" = {
      expr = (runCheck (checkType ctx0 (T.mkPi "x" T.mkNat T.mkBool))).tag;
      expected = "pi";
    };

    "checktype-sigma" = {
      expr = (runCheck (checkType ctx0 (T.mkSigma "x" T.mkNat T.mkBool))).tag;
      expected = "sigma";
    };

    "checktype-fallback" = {
      expr = (runCheck (checkType ctx0 (T.mkAnn T.mkNat (T.mkU 0)))).tag;
      expected = "ann";
    };

    "reject-checktype-non-universe" = {
      expr = (runCheck (checkTypeLevel ctx0 (T.mkAnn T.mkZero T.mkNat))) ? error;
      expected = true;
    };

    # 100-deep nested let — verify no stack overflow.
    "stress-nested-let-100" = {
      expr = let
        nested = builtins.foldl' (body: _:
          T.mkLet "x" T.mkNat T.mkZero body
        ) T.mkZero (builtins.genList (x: x) 100);
      in (checkTm ctx0 nested vNat).tag;
      expected = "let";
    };

    "reject-j-non-function-motive" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkAnn T.mkZero T.mkNat)
        T.mkZero T.mkZero T.mkRefl)) ? error;
      expected = true;
    };

    "reject-j-motive-wrong-outer-domain" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkBool
          (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 1)) (T.mkU 0)))
        T.mkZero T.mkZero T.mkRefl)) ? error;
      expected = true;
    };

    # 0+0=0 by computation.
    "theorem-0-plus-0" = {
      expr = let
        addZeroTm = T.mkNatElim
          (T.mkLam "n" T.mkNat T.mkNat)
          T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          T.mkZero;
        eqTy = T.mkEq T.mkNat addZeroTm T.mkZero;
      in (inferTm ctx0 (T.mkAnn T.mkRefl eqTy)).type.tag;
      expected = "VEq";
    };

    "theorem-bool-elim" = {
      expr = let
        tm = T.mkBoolElim
          (T.mkLam "b" T.mkBool T.mkNat)
          T.mkZero (T.mkSucc T.mkZero) T.mkTrue;
      in (inferTm ctx0 (T.mkAnn tm T.mkNat)).type.tag;
      expected = "VNat";
    };

    "theorem-nat-elim-infer" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        (T.mkSucc (T.mkSucc T.mkZero)))).type.tag;
      expected = "VNat";
    };

    "stress-large-nat" = {
      expr = let
        bigNat = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 10000);
      in (checkTm ctx0 bigNat vNat).tag;
      expected = "succ";
    };

    "stress-nat-elim-1000" = {
      expr = let
        nat1000 = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 1000);
      in (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        nat1000)).type.tag;
      expected = "VNat";
    };

    "stress-large-list" = {
      expr = let
        bigList = builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) 5000);
      in (checkTm ctx0 bigList (vList vNat)).tag;
      expected = "cons";
    };

    "stress-list-elim-1000" = {
      expr = let
        list1000 = builtins.foldl' (acc: _: T.mkCons T.mkNat T.mkZero acc)
          (T.mkNil T.mkNat) (builtins.genList (x: x) 1000);
      in (inferTm ctx0 (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) T.mkNat)
        T.mkZero
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
          (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0)))))
        list1000)).type.tag;
      expected = "VNat";
    };

    "stress-nested-pi" = {
      expr = let
        nested = builtins.foldl' (acc: _: T.mkPi "x" T.mkNat acc)
          T.mkNat (builtins.genList (x: x) 500);
      in (inferTm ctx0 nested).type.level;
      expected = 0;
    };

    "roundtrip-zero" = {
      expr = Q.nf [] (Q.nf [] T.mkZero) == Q.nf [] T.mkZero;
      expected = true;
    };
    "roundtrip-succ" = {
      expr = Q.nf [] (Q.nf [] (T.mkSucc T.mkZero)) == Q.nf [] (T.mkSucc T.mkZero);
      expected = true;
    };
    "roundtrip-true" = {
      expr = Q.nf [] (Q.nf [] T.mkTrue) == Q.nf [] T.mkTrue;
      expected = true;
    };
    "roundtrip-pair" = {
      expr = Q.nf [] (Q.nf [] (T.mkPair T.mkZero T.mkTrue))
        == Q.nf [] (T.mkPair T.mkZero T.mkTrue);
      expected = true;
    };
    "roundtrip-nil" = {
      expr = Q.nf [] (Q.nf [] (T.mkNil T.mkNat)) == Q.nf [] (T.mkNil T.mkNat);
      expected = true;
    };
    "roundtrip-app-beta" = {
      expr = let
        tm = T.mkApp (T.mkLam "x" T.mkNat (T.mkVar 0)) T.mkZero;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-let" = {
      expr = let tm = T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-nat-elim" = {
      expr = let
        tm = T.mkNatElim (T.mkLam "n" T.mkNat T.mkNat) T.mkZero
          (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
          (T.mkSucc (T.mkSucc T.mkZero));
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-pi" = {
      expr = let tm = T.mkPi "x" T.mkNat T.mkNat;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-lam" = {
      expr = let tm = T.mkLam "x" T.mkNat (T.mkVar 0);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-sigma" = {
      expr = let tm = T.mkSigma "x" T.mkNat T.mkBool;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-cons" = {
      expr = let tm = T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-sum" = {
      expr = let tm = T.mkSum T.mkNat T.mkBool;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inl" = {
      expr = let tm = T.mkInl T.mkNat T.mkBool T.mkZero;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inr" = {
      expr = let tm = T.mkInr T.mkNat T.mkBool T.mkTrue;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-eq" = {
      expr = let tm = T.mkEq T.mkNat T.mkZero T.mkZero;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-refl" = {
      expr = Q.nf [] (Q.nf [] T.mkRefl) == Q.nf [] T.mkRefl;
      expected = true;
    };
    "roundtrip-U" = {
      expr = Q.nf [] (Q.nf [] (T.mkU 0)) == Q.nf [] (T.mkU 0);
      expected = true;
    };
    "roundtrip-bool-elim" = {
      expr = let tm = T.mkBoolElim (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkFalse;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };

    # Large elim: motive returns higher universe.
    "large-elim-nat" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat (T.mkU 0))
        T.mkNat
        (T.mkLam "k" T.mkNat (T.mkLam "ih" (T.mkU 0) (T.mkVar 0)))
        T.mkZero)).type.tag;
      expected = "VU";
    };

    "large-elim-bool" = {
      expr = (inferTm ctx0 (T.mkBoolElim
        (T.mkLam "b" T.mkBool (T.mkU 0))
        T.mkNat T.mkBool T.mkTrue)).type.tag;
      expected = "VU";
    };

    "large-elim-list" = {
      expr = (inferTm ctx0 (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) (T.mkU 0))
        T.mkNat
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
          (T.mkLam "ih" (T.mkU 0) (T.mkVar 0))))
        (T.mkNil T.mkNat))).type.tag;
      expected = "VU";
    };

    "large-elim-sum" = {
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkBool
        (T.mkLam "s" (T.mkSum T.mkNat T.mkBool) (T.mkU 0))
        (T.mkLam "x" T.mkNat T.mkNat)
        (T.mkLam "b" T.mkBool T.mkBool)
        (T.mkInl T.mkNat T.mkBool T.mkZero))).type.tag;
      expected = "VU";
    };

    "large-elim-j" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat
          (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 1)) (T.mkU 0)))
        T.mkNat
        T.mkZero
        T.mkRefl)).type.tag;
      expected = "VU";
    };

    "large-elim-bool-U2" = {
      expr = (inferTm ctx0 (T.mkBoolElim
        (T.mkLam "b" T.mkBool (T.mkU 1))
        (T.mkU 0) T.mkNat T.mkFalse)).type.tag;
      expected = "VU";
    };

    # Under-binder roundtrips (non-empty environment).
    "roundtrip-under-binder-var" = {
      expr = let env1 = [ (V.freshVar 0) ];
      in Q.nf env1 (Q.nf env1 (T.mkVar 0)) == Q.nf env1 (T.mkVar 0);
      expected = true;
    };

    "roundtrip-under-binder-pi" = {
      expr = let
        env1 = [ (V.freshVar 0) ];
        tm = T.mkPi "y" T.mkNat (T.mkVar 1);
      in Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };

    "roundtrip-under-binder-lam" = {
      expr = let
        env1 = [ (V.freshVar 0) ];
        tm = T.mkLam "y" T.mkNat (T.mkSucc (T.mkVar 1));
      in Q.nf env1 (Q.nf env1 tm) == Q.nf env1 tm;
      expected = true;
    };

    # Universe level soundness: derivations, not post-hoc inspection.
    "level-pi-with-type-var" = {
      expr = let
        ctxB = extend ctx0 "B" (vU 1);
      in (inferTm ctxB (T.mkPi "x" T.mkNat (T.mkVar 1))).type.level;
      expected = 1;
    };

    "level-sigma-with-type-var" = {
      expr = let
        ctxB = extend ctx0 "B" (vU 1);
      in (inferTm ctxB (T.mkSigma "x" T.mkNat (T.mkVar 1))).type.level;
      expected = 1;
    };

    "level-nested-pi" = {
      expr = let
        ctxA = extend ctx0 "A" (vU 2);
      in (inferTm ctxA (T.mkPi "x" T.mkNat (T.mkPi "y" T.mkNat (T.mkVar 2)))).type.level;
      expected = 2;
    };

    "level-app-returning-universe" = {
      expr = let
        fTy = vPi "x" vNat (mkClosure [] (T.mkU 1));
        ctxF = extend ctx0 "F" fTy;
      in (inferTm ctxF (T.mkPi "y" (T.mkApp (T.mkVar 0) T.mkZero) T.mkNat)).type.level;
      expected = 1;
    };

    "level-sigma-mixed-vars" = {
      expr = let
        ctxAB = extend (extend ctx0 "A" (vU 2)) "B" (vU 1);
      in (inferTm ctxAB (T.mkSigma "x" (T.mkVar 1) (T.mkVar 1))).type.level;
      expected = 2;
    };

    "checkTypeLevel-string" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkString)).level;
      expected = 0;
    };
    "checkTypeLevel-int" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkInt)).level;
      expected = 0;
    };
    "checkTypeLevel-float" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkFloat)).level;
      expected = 0;
    };
    "checkTypeLevel-attrs" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkAttrs)).level;
      expected = 0;
    };
    "checkTypeLevel-path" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkPath)).level;
      expected = 0;
    };
    "checkTypeLevel-function" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkFunction)).level;
      expected = 0;
    };
    "checkTypeLevel-any" = {
      expr = (runCheck (checkTypeLevel ctx0 T.mkAny)).level;
      expected = 0;
    };
    "checkTypeLevel-eq" = {
      expr = (runCheck (checkTypeLevel ctx0 (T.mkEq T.mkNat T.mkZero T.mkZero))).level;
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

    "infer-string-type" = {
      expr = (inferTm ctx0 T.mkString).type.level;
      expected = 0;
    };
    "infer-int-type" = {
      expr = (inferTm ctx0 T.mkInt).type.level;
      expected = 0;
    };
    "infer-float-type" = {
      expr = (inferTm ctx0 T.mkFloat).type.level;
      expected = 0;
    };
    "infer-attrs-type" = {
      expr = (inferTm ctx0 T.mkAttrs).type.level;
      expected = 0;
    };
    "infer-path-type" = {
      expr = (inferTm ctx0 T.mkPath).type.level;
      expected = 0;
    };
    "infer-function-type" = {
      expr = (inferTm ctx0 T.mkFunction).type.level;
      expected = 0;
    };
    "infer-any-type" = {
      expr = (inferTm ctx0 T.mkAny).type.level;
      expected = 0;
    };

    "reject-string-lit-as-int" = {
      expr = (checkTm ctx0 (T.mkStringLit "hi") vInt) ? error;
      expected = true;
    };
    "reject-int-lit-as-string" = {
      expr = (checkTm ctx0 (T.mkIntLit 42) vString) ? error;
      expected = true;
    };
    "reject-float-lit-as-nat" = {
      expr = (checkTm ctx0 (T.mkFloatLit 1.0) vNat) ? error;
      expected = true;
    };
    "reject-attrs-lit-as-bool" = {
      expr = (checkTm ctx0 T.mkAttrsLit vBool) ? error;
      expected = true;
    };
    "reject-string-lit-as-nat" = {
      expr = (checkTm ctx0 (T.mkStringLit "x") vNat) ? error;
      expected = true;
    };

    "roundtrip-string-type" = {
      expr = Q.nf [] (Q.nf [] T.mkString) == Q.nf [] T.mkString;
      expected = true;
    };
    "roundtrip-int-type" = {
      expr = Q.nf [] (Q.nf [] T.mkInt) == Q.nf [] T.mkInt;
      expected = true;
    };
    "roundtrip-float-type" = {
      expr = Q.nf [] (Q.nf [] T.mkFloat) == Q.nf [] T.mkFloat;
      expected = true;
    };
    "roundtrip-string-lit" = {
      expr = Q.nf [] (Q.nf [] (T.mkStringLit "abc")) == Q.nf [] (T.mkStringLit "abc");
      expected = true;
    };
    "roundtrip-int-lit" = {
      expr = Q.nf [] (Q.nf [] (T.mkIntLit 99)) == Q.nf [] (T.mkIntLit 99);
      expected = true;
    };
    "roundtrip-float-lit" = {
      expr = Q.nf [] (Q.nf [] (T.mkFloatLit 1.5)) == Q.nf [] (T.mkFloatLit 1.5);
      expected = true;
    };
    "roundtrip-attrs-lit" = {
      expr = Q.nf [] (Q.nf [] T.mkAttrsLit) == Q.nf [] T.mkAttrsLit;
      expected = true;
    };
    "roundtrip-path-lit" = {
      expr = Q.nf [] (Q.nf [] T.mkPathLit) == Q.nf [] T.mkPathLit;
      expected = true;
    };
    "roundtrip-fn-lit" = {
      expr = Q.nf [] (Q.nf [] T.mkFnLit) == Q.nf [] T.mkFnLit;
      expected = true;
    };
    "roundtrip-any-lit" = {
      expr = Q.nf [] (Q.nf [] T.mkAnyLit) == Q.nf [] T.mkAnyLit;
      expected = true;
    };

    # Bare canonical forms (tt/zero/refl) have no infer rule — bidirectional
    # discipline requires annotation at synthesis positions. Every test below
    # that embeds a bare `tt` at a j/i index position wraps its enclosing
    # description in `T.mkAnn _ (T.mkDesc T.mkUnit)` so synthesis recovers I=Unit,
    # and checking cascades through the CHECK rules (which accept bare tt via
    # the tt-check rule at check.nix:123).
    "infer-desc-ret" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-desc-arg" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescArg T.mkBool (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-desc-rec" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-desc-pi" = {
      # f : Bool → Unit; all synthesis positions fold through the ann's check mode.
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescPi T.mkBool
                   (T.mkLam "_" T.mkBool T.mkTt)
                   (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-mu" = {
      # infer on mu routes through checkTypeLevel, which infers tm.D;
      # ann-wrap D so I=Unit is recoverable.
      expr = (inferTm ctx0
        (T.mkMu T.mkUnit
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit))
          T.mkTt)).type.level;
      expected = 0;
    };

    "checktype-desc" = {
      expr = (runCheck (checkTypeLevel ctx0 (T.mkDesc T.mkUnit))).level;
      expected = 1;
    };

    "checktype-mu" = {
      # checkTypeLevel's mu branch infers tm.D; ann-wrap D to carry I=Unit.
      expr = (runCheck (checkTypeLevel ctx0
        (T.mkMu T.mkUnit
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit))
          T.mkTt))).level;
      expected = 0;
    };

    "infer-desc-con" = {
      # Ret-leaf payload is mkRefl (witnesses Eq I j i; here Eq Unit tt tt by Unit-η).
      expr = (inferTm ctx0
        (T.mkDescCon
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit))
          T.mkTt T.mkRefl)).type.tag;
      expected = "VMu";
    };

    "check-desc-con" = {
      expr = (checkTm ctx0
        (T.mkDescCon (T.mkDescRet T.mkTt) T.mkTt T.mkRefl)
        (vMu vUnit (vDescRet vTt) vTt)).tag;
      expected = "desc-con";
    };

    "infer-desc-elim-ret" = {
      # Indexed on-cases: onRet (1 binder j:I), onArg (3: S T ih), onRec (3: j D ih),
      # onPi (4: S f D ih), onPlus (4: A B ihA ihB). Each body returns a
      # U-typed term for large elim. scrut is ann-wrapped so I is recoverable
      # in infer mode.
      expr = (inferTm ctx0 (T.mkDescElim
        (T.mkLam "_" (T.mkDesc T.mkUnit) (T.mkU 0))
        (T.mkLam "j" T.mkUnit T.mkUnit)
        (T.mkLam "S" (T.mkU 0) (T.mkLam "T"
          (T.mkPi "_" (T.mkVar 0) (T.mkDesc T.mkUnit))
          (T.mkLam "ih" (T.mkPi "s" (T.mkVar 1) (T.mkU 0)) T.mkUnit)))
        (T.mkLam "j" T.mkUnit (T.mkLam "D" (T.mkDesc T.mkUnit)
          (T.mkLam "ih" (T.mkU 0) T.mkUnit)))
        (T.mkLam "S" (T.mkU 0) (T.mkLam "f"
          (T.mkPi "_" (T.mkVar 0) T.mkUnit)
          (T.mkLam "D" (T.mkDesc T.mkUnit)
            (T.mkLam "ih" (T.mkU 0) T.mkUnit))))
        (T.mkLam "A" (T.mkDesc T.mkUnit) (T.mkLam "B" (T.mkDesc T.mkUnit)
          (T.mkLam "ihA" (T.mkU 0) (T.mkLam "ihB" (T.mkU 0) T.mkUnit))))
        (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit)))).type.tag;
      expected = "VU";
    };

    "reject-desc-con-bad-payload" = {
      # Ret-leaf payload type is Eq Unit tt tt; mkZero : Nat fails to inhabit it.
      expr = (inferTm ctx0
        (T.mkDescCon
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit))
          T.mkTt T.mkZero)) ? error;
      expected = true;
    };

    "reject-desc-arg-bad-S" = {
      # mkZero is not a type; check S : U(0) fails before reaching the body.
      expr = (inferTm ctx0
        (T.mkDescArg T.mkZero (T.mkDescRet T.mkTt))) ? error;
      expected = true;
    };

    "infer-desc-ind-ret" = {
      # Motive: (i:I) → μD i → U. Step: Π(i:I). Π(d:Eq Unit tt i). Π(_:Unit). Nat.
      # desc-ind infers tm.D; ann-wrap D so I=Unit is recoverable.
      expr = let
        D = T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkUnit);
      in (inferTm ctx0 (T.mkDescInd D
        (T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D (T.mkVar 0)) T.mkNat))
        (T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkEq T.mkUnit T.mkTt (T.mkVar 0))
            (T.mkLam "_" T.mkUnit T.mkZero)))
        T.mkTt
        (T.mkDescCon D T.mkTt T.mkRefl))).type.tag;
      expected = "VNat";
    };

    "infer-desc-ind-arg" = {
      # D = arg Bool (ret tt) — body is body-Tm under implicit s:Bool, not a lambda.
      # interp at i = Σ(s:Bool). Eq Unit tt i (Var 1 = i from inside the Sigma snd).
      # All = Unit (allOnRet collapses to Unit at ret-leaf for I=⊤).
      expr = let
        D = T.mkAnn (T.mkDescArg T.mkBool (T.mkDescRet T.mkTt))
                    (T.mkDesc T.mkUnit);
      in (inferTm ctx0 (T.mkDescInd D
        (T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D (T.mkVar 0)) T.mkNat))
        (T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkSigma "s" T.mkBool
            (T.mkEq T.mkUnit T.mkTt (T.mkVar 1)))
            (T.mkLam "_" T.mkUnit T.mkZero)))
        T.mkTt
        (T.mkDescCon D T.mkTt
          (T.mkPair T.mkFalse T.mkRefl)))).type.tag;
      expected = "VNat";
    };
  };
}
