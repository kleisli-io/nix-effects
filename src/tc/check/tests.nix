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

  inherit (V) vNat vZero vSucc vPi vSigma
    vList vUnit vSum vEq vU mkClosure vTt
    vString vInt vFloat vAttrs vPath vFunction vAny
    vDescRet vMu;

  ctx0 = emptyCtx;
  ctx1 = extend ctx0 "x" vNat;

  # Universe level as Nix integer. `checkTypeLevel`/infer can return
  # a `VLevelMax` whose concrete value only reduces after the Level
  # normaliser runs, so these helpers normalise first before peeling
  # the unique `VLevelSuc^n VLevelZero` summand. Every test below
  # uses concrete levels, so the peel is total.
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

    "check-refl" = {
      expr = (checkTm ctx0 T.mkRefl (vEq vNat vZero vZero)).tag;
      expected = "refl";
    };

    "squash-formation" = {
      expr = (inferTm ctx0 (T.mkSquash T.mkUnit)).type.tag;
      expected = "VU";
    };
    "squash-formation-level-zero" = {
      expr = typeLvl (inferTm ctx0 (T.mkSquash T.mkUnit));
      expected = 0;
    };
    "squash-intro-check" = {
      expr = (checkTm ctx0 (T.mkSquashIntro T.mkTt)
        (V.vSquash vUnit)).tag;
      expected = "squash-intro";
    };
    "squash-elim-infer" = {
      # recTrunc Unit Unit (λ_:Unit. squashIntro tt) (squashIntro tt)
      # infers as Squash Unit.
      expr = let
        f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
        e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkSquashIntro T.mkTt);
      in (inferTm ctx0 e).type.tag;
      expected = "VSquash";
    };
    "squash-elim-motive-rejected" = {
      # `f : Unit → Unit` is not `Unit → Squash Unit` — INFER must reject.
      expr = let
        f = T.mkLam "_" T.mkUnit T.mkTt;
        e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkSquashIntro T.mkTt);
      in (inferTm ctx0 e) ? error;
      expected = true;
    };

    "check-pair" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkTt)
        (vSigma "x" vNat (mkClosure [] T.mkUnit))).tag;
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
      expr = (checkTm ctx0 (T.mkInl T.mkNat T.mkUnit T.mkZero) (vSum vNat vUnit)).tag;
      expected = "inl";
    };

    "check-inr" = {
      expr = (checkTm ctx0 (T.mkInr T.mkNat T.mkUnit T.mkTt) (vSum vNat vUnit)).tag;
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
      expr = typeLvl (inferTm ctx0 (T.mkU T.mkLevelZero));
      expected = 1;
    };

    "infer-U1" = {
      expr = typeLvl (inferTm ctx0 (T.mkU (T.mkLevelSuc T.mkLevelZero)));
      expected = 2;
    };

    # Level-polymorphic universe: `Π (k : Level). U(k)` is well-formed
    # and inhabits a universe. The type's level is `max 0 (suc k)` for
    # a bound `k : Level`; at the outermost Pi this resolves to
    # `suc k`, which is not a concrete natural, so we check the tag.
    "infer-pi-level-universe-U" = {
      expr = (inferTm ctx0
        (T.mkPi "k" T.mkLevel (T.mkU (T.mkVar 0)))).type.tag;
      expected = "VU";
    };

    # `U(max 0 0)` conv-equates with `U(0)` — the Level normaliser
    # absorbs zeros so the check succeeds.
    "check-U-max-zero-vs-U0" = {
      expr = (checkTm ctx0
        (T.mkU (T.mkLevelMax T.mkLevelZero T.mkLevelZero))
        (vU (V.vLevelSuc V.vLevelZero))).tag;
      expected = "U";
    };

    # `U(suc zero)` and `U(1)` elaborate to conv-equal kernel terms.
    "check-U-suc-zero-vs-U1" = {
      expr = (checkTm ctx0
        (T.mkU (T.mkLevelSuc T.mkLevelZero))
        (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)))).tag;
      expected = "U";
    };

    "infer-nat-type" = {
      expr = typeLvl (inferTm ctx0 T.mkNat);
      expected = 0;
    };

    "infer-pi-type" = {
      expr = typeLvl (inferTm ctx0 (T.mkPi "x" T.mkNat T.mkNat));
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
        p = T.mkAnn (T.mkPair T.mkZero T.mkTt)
          (T.mkSigma "x" T.mkNat T.mkUnit);
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VNat";
    };

    "infer-snd" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkZero T.mkTt)
          (T.mkSigma "x" T.mkNat T.mkUnit);
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VUnit";
    };

    "infer-pair-via-ann" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkUnit;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTt) sigTy;
      in (inferTm ctx0 p).type.tag;
      expected = "VSigma";
    };

    "infer-fst-ann-pair" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkUnit;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTt) sigTy;
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VNat";
    };
    "infer-snd-ann-pair" = {
      expr = let
        sigTy = T.mkSigma "x" T.mkNat T.mkUnit;
        p = T.mkAnn (T.mkPair T.mkZero T.mkTt) sigTy;
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VUnit";
    };

    # Bare pairs cannot be inferred (introduction forms check, not synthesize).
    "reject-pair-infer-bare" = {
      expr = (inferTm ctx0 (T.mkPair T.mkZero T.mkTt)) ? error;
      expected = true;
    };
    "reject-pair-infer-bare-msg" = {
      expr = (inferTm ctx0 (T.mkPair T.mkZero T.mkTt)).msg;
      expected = "cannot infer type";
    };

    "check-let" = {
      expr = (checkTm ctx0 (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0)) vNat).tag;
      expected = "let";
    };

    # Dependent function: Lam(A, U(0), Lam(x, Var(0), Var(0)))
    "check-poly-id" = {
      expr = let
        ty = vPi "A" (vU V.vLevelZero) (mkClosure [] (T.mkPi "x" (T.mkVar 0) (T.mkVar 1)));
        tm = T.mkLam "A" (T.mkU T.mkLevelZero) (T.mkLam "x" (T.mkVar 0) (T.mkVar 0));
      in (checkTm ctx0 tm ty).tag;
      expected = "lam";
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
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkUnit
        (T.mkLam "s" (T.mkSum T.mkNat T.mkUnit) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "b" T.mkUnit T.mkZero)
        (T.mkInl T.mkNat T.mkUnit T.mkZero))).type.tag;
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

    "reject-zero-unit" = {
      expr = (checkTm ctx0 T.mkZero vUnit) ? error;
      expected = true;
    };

    # Universe violation: U(0) : U(0) rejected.
    "reject-U0-U0" = {
      expr = (checkTm ctx0 (T.mkU T.mkLevelZero) (vU V.vLevelZero)) ? error;
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
      # Motive body must be a type, not a term; T.mkTt : Unit fails the type check.
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkTt)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        T.mkZero)) ? error;
      expected = true;
    };

    "reject-pair-snd-mismatch" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkZero)
        (vSigma "x" vNat (mkClosure [] T.mkUnit))) ? error;
      expected = true;
    };
    "reject-pair-snd-mismatch-msg" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkZero)
        (vSigma "x" vNat (mkClosure [] T.mkUnit))).msg;
      expected = "cannot infer type";
    };

    # J motive with wrong inner domain.
    "reject-j-motive-wrong-inner-domain" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkAnn
          (T.mkLam "y" T.mkNat
            (T.mkLam "e" T.mkNat (T.mkU T.mkLevelZero)))
          (T.mkPi "y" T.mkNat (T.mkPi "e" T.mkNat (T.mkU (T.mkLevelSuc T.mkLevelZero)))))
        T.mkZero
        T.mkZero
        T.mkRefl)) ? error;
      expected = true;
    };
    "reject-j-motive-wrong-inner-domain-msg" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkAnn
          (T.mkLam "y" T.mkNat
            (T.mkLam "e" T.mkNat (T.mkU T.mkLevelZero)))
          (T.mkPi "y" T.mkNat (T.mkPi "e" T.mkNat (T.mkU (T.mkLevelSuc T.mkLevelZero)))))
        T.mkZero
        T.mkZero
        T.mkRefl)).msg;
      expected = "J motive inner domain must be Eq(A, a, y)";
    };

    "reject-lam-against-non-pi" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkNat (T.mkVar 0)) vNat) ? error;
      expected = true;
    };

    "check-U0-in-U1" = {
      expr = (checkTm ctx0 (T.mkU T.mkLevelZero) (vU (V.vLevelSuc V.vLevelZero))).tag;
      expected = "U";
    };

    # Downward cumulativity rejected: U(1):U(2), not convertible to U(0).
    "reject-U1-in-U0" = {
      expr = (checkTm ctx0 (T.mkU (T.mkLevelSuc T.mkLevelZero)) (vU V.vLevelZero)) ? error;
      expected = true;
    };

    "reject-nat-elim-unit-scrut" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        T.mkTt)) ? error;
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
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkUnit
        (T.mkLam "s" (T.mkSum T.mkNat T.mkUnit) T.mkNat)
        (T.mkLam "x" T.mkNat (T.mkVar 0))
        (T.mkLam "b" T.mkUnit T.mkZero)
        T.mkZero)) ? error;
      expected = true;
    };

    "infer-eq-type" = {
      expr = (inferTm ctx0 (T.mkEq T.mkNat T.mkZero T.mkZero)).type.tag;
      expected = "VU";
    };

    "infer-sigma-type" = {
      expr = (inferTm ctx0 (T.mkSigma "x" T.mkNat T.mkNat)).type.tag;
      expected = "VU";
    };

    "infer-sum-type" = {
      expr = (inferTm ctx0 (T.mkSum T.mkNat T.mkNat)).type.tag;
      expected = "VU";
    };

    "infer-list-type" = {
      expr = (inferTm ctx0 (T.mkList T.mkNat)).type.tag;
      expected = "VU";
    };

    "checktype-pi" = {
      expr = (runCheck (checkType ctx0 (T.mkPi "x" T.mkNat T.mkNat))).tag;
      expected = "pi";
    };

    "checktype-sigma" = {
      expr = (runCheck (checkType ctx0 (T.mkSigma "x" T.mkNat T.mkNat))).tag;
      expected = "sigma";
    };

    "checktype-fallback" = {
      expr = (runCheck (checkType ctx0 (T.mkAnn T.mkNat (T.mkU T.mkLevelZero)))).tag;
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
        (T.mkLam "y" T.mkUnit
          (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 1)) (T.mkU T.mkLevelZero)))
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
      in typeLvl (inferTm ctx0 nested);
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
    "roundtrip-pair" = {
      expr = Q.nf [] (Q.nf [] (T.mkPair T.mkZero T.mkTt))
        == Q.nf [] (T.mkPair T.mkZero T.mkTt);
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
      expr = let tm = T.mkSigma "x" T.mkNat T.mkNat;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-cons" = {
      expr = let tm = T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat);
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-sum" = {
      expr = let tm = T.mkSum T.mkNat T.mkUnit;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inl" = {
      expr = let tm = T.mkInl T.mkNat T.mkUnit T.mkZero;
      in Q.nf [] (Q.nf [] tm) == Q.nf [] tm;
      expected = true;
    };
    "roundtrip-inr" = {
      expr = let tm = T.mkInr T.mkNat T.mkUnit T.mkTt;
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
      expr = Q.nf [] (Q.nf [] (T.mkU T.mkLevelZero)) == Q.nf [] (T.mkU T.mkLevelZero);
      expected = true;
    };
    # Large elim: motive returns higher universe.
    "large-elim-nat" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat (T.mkU T.mkLevelZero))
        T.mkNat
        (T.mkLam "k" T.mkNat (T.mkLam "ih" (T.mkU T.mkLevelZero) (T.mkVar 0)))
        T.mkZero)).type.tag;
      expected = "VU";
    };

    "large-elim-list" = {
      expr = (inferTm ctx0 (T.mkListElim T.mkNat
        (T.mkLam "l" (T.mkList T.mkNat) (T.mkU T.mkLevelZero))
        T.mkNat
        (T.mkLam "h" T.mkNat (T.mkLam "t" (T.mkList T.mkNat)
          (T.mkLam "ih" (T.mkU T.mkLevelZero) (T.mkVar 0))))
        (T.mkNil T.mkNat))).type.tag;
      expected = "VU";
    };

    "large-elim-sum" = {
      expr = (inferTm ctx0 (T.mkSumElim T.mkNat T.mkUnit
        (T.mkLam "s" (T.mkSum T.mkNat T.mkUnit) (T.mkU T.mkLevelZero))
        (T.mkLam "x" T.mkNat T.mkNat)
        (T.mkLam "b" T.mkUnit T.mkUnit)
        (T.mkInl T.mkNat T.mkUnit T.mkZero))).type.tag;
      expected = "VU";
    };

    "large-elim-j" = {
      expr = (inferTm ctx0 (T.mkJ T.mkNat T.mkZero
        (T.mkLam "y" T.mkNat
          (T.mkLam "e" (T.mkEq T.mkNat T.mkZero (T.mkVar 1)) (T.mkU T.mkLevelZero)))
        T.mkNat
        T.mkZero
        T.mkRefl)).type.tag;
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
        ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
      in typeLvl (inferTm ctxB (T.mkPi "x" T.mkNat (T.mkVar 1)));
      expected = 1;
    };

    "level-sigma-with-type-var" = {
      expr = let
        ctxB = extend ctx0 "B" (vU (V.vLevelSuc V.vLevelZero));
      in typeLvl (inferTm ctxB (T.mkSigma "x" T.mkNat (T.mkVar 1)));
      expected = 1;
    };

    "level-nested-pi" = {
      expr = let
        ctxA = extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)));
      in typeLvl (inferTm ctxA (T.mkPi "x" T.mkNat (T.mkPi "y" T.mkNat (T.mkVar 2))));
      expected = 2;
    };

    "level-app-returning-universe" = {
      expr = let
        fTy = vPi "x" vNat (mkClosure [] (T.mkU (T.mkLevelSuc T.mkLevelZero)));
        ctxF = extend ctx0 "F" fTy;
      in typeLvl (inferTm ctxF (T.mkPi "y" (T.mkApp (T.mkVar 0) T.mkZero) T.mkNat));
      expected = 1;
    };

    "level-sigma-mixed-vars" = {
      expr = let
        ctxAB = extend (extend ctx0 "A" (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)))) "B" (vU (V.vLevelSuc V.vLevelZero));
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
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 (T.mkEq T.mkNat T.mkZero T.mkZero)));
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
      expr = typeLvl (inferTm ctx0 T.mkString);
      expected = 0;
    };
    "infer-int-type" = {
      expr = typeLvl (inferTm ctx0 T.mkInt);
      expected = 0;
    };
    "infer-float-type" = {
      expr = typeLvl (inferTm ctx0 T.mkFloat);
      expected = 0;
    };
    "infer-attrs-type" = {
      expr = typeLvl (inferTm ctx0 T.mkAttrs);
      expected = 0;
    };
    "infer-path-type" = {
      expr = typeLvl (inferTm ctx0 T.mkPath);
      expected = 0;
    };
    "infer-function-type" = {
      expr = typeLvl (inferTm ctx0 T.mkFunction);
      expected = 0;
    };
    "infer-any-type" = {
      expr = typeLvl (inferTm ctx0 T.mkAny);
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
    "reject-attrs-lit-as-nat" = {
      expr = (checkTm ctx0 T.mkAttrsLit vNat) ? error;
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
    # description in `T.mkAnn _ (T.mkDesc T.mkLevelZero T.mkUnit)` so synthesis recovers I=Unit,
    # and checking cascades through the CHECK rules (which accept bare tt via
    # the tt-check rule at check.nix:123).
    "infer-desc-ret" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-desc-arg" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkLevelZero T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    # Universe-polymorphic `arg` — `descArg 1 (u 0) (λ_. ret tt)` has
    # `S = u 0 : U(1)`, the level slot drives the S sort check to
    # `U(1)`. Acceptance criterion for Phase 11 Step 3.
    "infer-desc-arg-level-one" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescArg (T.mkLevelSuc T.mkLevelZero) (T.mkLevelSuc T.mkLevelZero) (T.mkU T.mkLevelZero) T.mkRefl (T.mkDescRet T.mkTt))
                 (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit))).type.tag;
      expected = "VDesc";
    };
    # The desc-arg CHECK rule routes through the encoded
    # `mkApp ... encodeDescArgAtTm ...` chain; eval must land in
    # `VDescCon` (the levitated constructor). Asserts the encoding
    # invariant at the value layer, independent of elaboration Tm shape.
    "check-desc-arg-level-one" = {
      expr =
        let
          E = fx.tc.eval;
          checked = checkTm ctx0
            (T.mkDescArg (T.mkLevelSuc T.mkLevelZero) (T.mkLevelSuc T.mkLevelZero) (T.mkU T.mkLevelZero) T.mkRefl (T.mkDescRet T.mkTt))
            (V.vDesc (V.vLevelSuc V.vLevelZero) vUnit);
        in (E.eval [] checked).tag;
      expected = "VDescCon";
    };

    "infer-desc-rec" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkLevelZero T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-desc-pi" = {
      # f : Nat → Unit; all synthesis positions fold through the ann's check mode.
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
                   (T.mkLam "_" T.mkNat T.mkTt)
                   (T.mkDescRet T.mkTt))
                 (T.mkDesc T.mkLevelZero T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    # Universe-polymorphic `pi` — `descPi 1 (u 0) f (ret tt)`.
    "infer-desc-pi-level-one" = {
      expr = (inferTm ctx0
        (T.mkAnn (T.mkDescPi (T.mkLevelSuc T.mkLevelZero) (T.mkLevelSuc T.mkLevelZero) (T.mkU T.mkLevelZero) T.mkRefl
                   (T.mkLam "_" (T.mkU T.mkLevelZero) T.mkTt)
                   (T.mkDescRet T.mkTt))
                 (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit))).type.tag;
      expected = "VDesc";
    };

    "infer-mu" = {
      # infer on mu routes through checkTypeLevel, which infers tm.D;
      # ann-wrap D so I=Unit is recoverable.
      expr = typeLvl (inferTm ctx0
        (T.mkMu T.mkUnit
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit))
          T.mkTt));
      expected = 0;
    };

    "checktype-desc" = {
      expr = ctlLvl (runCheck (checkTypeLevel ctx0 (T.mkDesc T.mkLevelZero T.mkUnit)));
      expected = 1;
    };

    "checktype-mu" = {
      # checkTypeLevel's mu branch infers tm.D; ann-wrap D to carry I=Unit.
      expr = ctlLvl (runCheck (checkTypeLevel ctx0
        (T.mkMu T.mkUnit
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit))
          T.mkTt)));
      expected = 0;
    };

    "infer-desc-con" = {
      # Ret-leaf payload is mkRefl (witnesses Eq I j i; here Eq Unit tt tt by Unit-η).
      expr = (inferTm ctx0
        (T.mkDescCon
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit))
          T.mkTt T.mkRefl)).type.tag;
      expected = "VMu";
    };

    "check-desc-con" = {
      expr =
        let
          E = fx.tc.eval;
          H = fx.tc.hoas;
          encRetVal = E.eval [] (T.mkApp
            (T.mkApp
              (T.mkApp H.encodeDescRetTm T.mkUnit)
              T.mkLevelZero)
            T.mkTt);
        in (checkTm ctx0
              (T.mkDescCon (T.mkDescRet T.mkTt) T.mkTt T.mkRefl)
              (vMu vUnit encRetVal vTt)).tag;
      expected = "desc-con";
    };

    "infer-desc-elim-ret" = {
      # Indexed on-cases: onRet (1 binder j:I), onArg (3: S T ih), onRec (3: j D ih),
      # onPi (4: S f D ih), onPlus (4: A B ihA ihB). Each body returns a
      # U-typed term for large elim. scrut is ann-wrapped so I is recoverable
      # in infer mode. Leading `0` pins the descElim's `k` slot to level zero,
      # so onArg / onPi bind their sort `S` at `U(0)`.
      expr = (inferTm ctx0 (T.mkDescElim T.mkLevelZero
        (T.mkLam "_" (T.mkDesc T.mkLevelZero T.mkUnit) (T.mkU T.mkLevelZero))
        (T.mkLam "j" T.mkUnit T.mkUnit)
        (T.mkLam "S" (T.mkU T.mkLevelZero) (T.mkLam "T"
          (T.mkPi "_" (T.mkVar 0) (T.mkDesc T.mkLevelZero T.mkUnit))
          (T.mkLam "ih" (T.mkPi "s" (T.mkVar 1) (T.mkU T.mkLevelZero)) T.mkUnit)))
        (T.mkLam "j" T.mkUnit (T.mkLam "D" (T.mkDesc T.mkLevelZero T.mkUnit)
          (T.mkLam "ih" (T.mkU T.mkLevelZero) T.mkUnit)))
        (T.mkLam "S" (T.mkU T.mkLevelZero) (T.mkLam "f"
          (T.mkPi "_" (T.mkVar 0) T.mkUnit)
          (T.mkLam "D" (T.mkDesc T.mkLevelZero T.mkUnit)
            (T.mkLam "ih" (T.mkU T.mkLevelZero) T.mkUnit))))
        (T.mkLam "A" (T.mkDesc T.mkLevelZero T.mkUnit) (T.mkLam "B" (T.mkDesc T.mkLevelZero T.mkUnit)
          (T.mkLam "ihA" (T.mkU T.mkLevelZero) (T.mkLam "ihB" (T.mkU T.mkLevelZero) T.mkUnit))))
        (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit)))).type.tag;
      expected = "VU";
    };

    # `descElim 1 …` accepts arg / pi cases whose sort `S` lives at
    # `U(1)` and a scrutinee at `Desc^1 ⊤`. The K slot must match the
    # scrutinee's description level (`convLevel K sTy.level`), so
    # `motive`, `onRec`, `onPi`, `onPlus`, and the recursive
    # description annotations all use `Desc^1 ⊤`. The `descRet`
    # leaf carries no level slot, so it inhabits `Desc^1 ⊤` directly.
    "infer-desc-elim-at-level-one" = {
      expr = (inferTm ctx0 (T.mkDescElim (T.mkLevelSuc T.mkLevelZero)
        (T.mkLam "_" (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit) (T.mkU T.mkLevelZero))
        (T.mkLam "j" T.mkUnit T.mkNat)
        (T.mkLam "S" (T.mkU (T.mkLevelSuc T.mkLevelZero)) (T.mkLam "T"
          (T.mkPi "_" (T.mkVar 0) (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit))
          (T.mkLam "ih" (T.mkPi "s" (T.mkVar 1) T.mkNat) T.mkNat)))
        (T.mkLam "j" T.mkUnit (T.mkLam "D" (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit)
          (T.mkLam "ih" T.mkNat T.mkNat)))
        (T.mkLam "S" (T.mkU (T.mkLevelSuc T.mkLevelZero)) (T.mkLam "f"
          (T.mkPi "_" (T.mkVar 0) T.mkUnit)
          (T.mkLam "D" (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit)
            (T.mkLam "ih" T.mkNat T.mkNat))))
        (T.mkLam "A" (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit) (T.mkLam "B" (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit)
          (T.mkLam "ihA" T.mkNat (T.mkLam "ihB" T.mkNat T.mkNat))))
        (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc (T.mkLevelSuc T.mkLevelZero) T.mkUnit)))).type.tag;
      expected = "VU";
    };

    # At `descElim 1 …` the `onArg` case must bind its sort `S` at
    # `U(1)` to satisfy `paTy : Π(S:U(1)). …`. A user `onArg` whose lam
    # body uses `S` at the wrong universe — emitting `S` itself as a
    # value of type `U(0)` — fails the motive-application return type
    # check (motive yields `U(0)` but the body ascribes `S : U(0)`,
    # which doesn't conv against `U(0)`'s shape after substitution).
    # Probe: an `onArg` body that returns `S` directly (treating S as
    # a U(0) value) at K=1 is rejected; at K=0 the same body succeeds
    # because S then *is* a U(0) value. Both K instances use a
    # scrutinee at `Desc^K ⊤` so the K-vs-sTy.level conformance check
    # accepts and the rejection isolates the body's universe error.
    "desc-elim-at-level-one-onArg-wrong-universe-rejected" = {
      expr =
        let
          mkElim = K:
            T.mkDescElim K
              (T.mkLam "_" (T.mkDesc K T.mkUnit) (T.mkU T.mkLevelZero))
              (T.mkLam "j" T.mkUnit T.mkUnit)
              (T.mkLam "S" (T.mkU K) (T.mkLam "T"
                (T.mkPi "_" (T.mkVar 0) (T.mkDesc K T.mkUnit))
                (T.mkLam "ih"
                  (T.mkPi "s" (T.mkVar 1) (T.mkU T.mkLevelZero))
                  (T.mkVar 2))))
              (T.mkLam "j" T.mkUnit (T.mkLam "D" (T.mkDesc K T.mkUnit)
                (T.mkLam "ih" (T.mkU T.mkLevelZero) T.mkUnit)))
              (T.mkLam "S" (T.mkU K) (T.mkLam "f"
                (T.mkPi "_" (T.mkVar 0) T.mkUnit)
                (T.mkLam "D" (T.mkDesc K T.mkUnit)
                  (T.mkLam "ih" (T.mkU T.mkLevelZero) T.mkUnit))))
              (T.mkLam "A" (T.mkDesc K T.mkUnit) (T.mkLam "B" (T.mkDesc K T.mkUnit)
                (T.mkLam "ihA" (T.mkU T.mkLevelZero) (T.mkLam "ihB" (T.mkU T.mkLevelZero) T.mkUnit))))
              (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc K T.mkUnit));
          atZero = inferTm ctx0 (mkElim T.mkLevelZero);
          atOne  = inferTm ctx0 (mkElim (T.mkLevelSuc T.mkLevelZero));
        in {
          zeroOk = !(atZero ? error);
          oneRejected = atOne ? error;
        };
      expected = { zeroOk = true; oneRejected = true; };
    };


    "reject-desc-con-bad-payload" = {
      # Ret-leaf payload type is Eq Unit tt tt; mkZero : Nat fails to inhabit it.
      expr = (inferTm ctx0
        (T.mkDescCon
          (T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit))
          T.mkTt T.mkZero)) ? error;
      expected = true;
    };

    "reject-desc-arg-bad-S" = {
      # mkZero is not a type; check S : U(0) fails before reaching the body.
      expr = (inferTm ctx0
        (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkZero T.mkRefl (T.mkDescRet T.mkTt))) ? error;
      expected = true;
    };

    # Blame-path precision: the infer `desc-arg` rule wraps its sort
    # sub-delegation with `bindP P.DArgSort`, so the structural descent
    # coordinate is DArgSort even though the actual failure originates
    # in the generic sub-rule catch-all's "type mismatch".
    "reject-desc-arg-bad-S-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkZero T.mkRefl (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DArgSort";
    };

    # Terminal body-shape mismatch: var 0 in the extended context
    # infers to VNat, which is not VDesc. The rule emits
    # `diag.mkKernelError` with `position = P.DArgBody`, so the root
    # child edge carries DArgBody and the leaf carries `rule = "desc-arg"`.
    "reject-desc-arg-bad-body-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkVar 0));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DArgBody";
    };
    "reject-desc-arg-bad-body-rule" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkVar 0));
        in r.error.detail.rule;
      expected = "desc-arg";
    };

    # CHECK-mode desc-arg dispatch exercises the same positional
    # wrappers as INFER: a bad sort surfaces under DArgSort.
    "reject-desc-arg-check-bad-S-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkZero T.mkRefl (T.mkDescRet T.mkTt))
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DArgSort";
    };

    # Bad level: `descArg mkZero S T` feeds a Nat into the level slot.
    # The infer rule routes through `bindP P.DArgLevel` on the non-
    # fast-path branch, so the blame lives at `arg.k`.
    "reject-desc-arg-bad-k-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescArg (T.mkLevelSuc T.mkLevelZero) (T.mkLevelSuc T.mkLevelZero) T.mkZero T.mkRefl (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DArgSort";
    };

    # INFER-mode desc-ret: a non-synthesising index (mkTt has no
    # INFER rule) fails via the "cannot infer type" catch-all, but
    # `bindP P.DRetIndex` at the caller supplies the descent
    # coordinate so the error surfaces at `ret.j`.
    "reject-desc-ret-infer-bad-j-position" = {
      expr =
        let r = inferTm ctx0 (T.mkDescRet T.mkTt);
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRetIndex";
    };

    # CHECK-mode desc-ret against Desc Unit: mkZero does not check
    # against VUnit, so the sub-rule fall-through raises "type
    # mismatch"; `bindP P.DRetIndex` tags it at the index position.
    "reject-desc-ret-check-bad-j-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescRet T.mkZero)
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRetIndex";
    };

    # INFER-mode desc-rec with a non-synthesising index (mkTt has no
    # INFER rule) fails at the `j` sub-delegation; `bindP P.DRecIndex`
    # supplies the `rec.j` coordinate.
    "reject-desc-rec-infer-bad-j-position" = {
      expr =
        let r = inferTm ctx0 (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRecIndex";
    };

    # INFER-mode desc-rec with a good index and a malformed tail:
    # infer j=var 0 in ctx with "_" : Nat yields iVal=VNat; the tail
    # D=mkZero fails to check against `Desc Nat` via the sub-rule
    # fall-through. `bindP P.DRecTail` tags the tail position.
    "reject-desc-rec-infer-bad-D-position" = {
      expr =
        let ctx' = extend ctx0 "_" vNat;
            r = inferTm ctx' (T.mkDescRec (T.mkVar 0) T.mkZero);
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRecTail";
    };

    # CHECK-mode desc-rec against Desc Unit: a non-Unit index fails
    # the `j` sub-check; `bindP P.DRecIndex` tags it.
    "reject-desc-rec-check-bad-j-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescRec T.mkZero (T.mkDescRet T.mkTt))
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRecIndex";
    };

    # CHECK-mode desc-rec with a good j=mkTt : VUnit but a malformed
    # tail D=mkZero: `bindP P.DRecTail` tags the tail position.
    "reject-desc-rec-check-bad-D-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescRec T.mkTt T.mkZero)
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DRecTail";
    };

    # INFER-mode desc-pi with a non-type sort: S=mkZero fails the
    # `U(0)` check via sub-rule fall-through; `bindP P.DPiSort` tags it.
    "reject-desc-pi-infer-bad-S-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkZero T.mkRefl
            (T.mkLam "_" T.mkNat T.mkTt)
            (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiSort";
    };

    # INFER-mode desc-pi where f is not inferable: mkTt has no INFER
    # rule, the catch-all fires; `bindP P.DPiFn` tags the fn position.
    "reject-desc-pi-infer-bad-f-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl T.mkTt (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiFn";
    };

    # INFER-mode desc-pi where f infers to a non-Pi type: mkVar 0 in
    # ctx extended by Nat infers to Nat, which is not a VPi. The rule
    # emits `mkKernelError { position = DPiFn; rule = "desc-pi"; }`.
    "reject-desc-pi-infer-f-not-pi-position" = {
      expr =
        let ctx' = extend ctx0 "_" vNat;
            r = inferTm ctx' (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkVar 0) (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiFn";
    };
    "reject-desc-pi-infer-f-not-pi-rule" = {
      expr =
        let ctx' = extend ctx0 "_" vNat;
            r = inferTm ctx' (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkVar 0) (T.mkDescRet T.mkTt));
        in r.error.detail.rule;
      expected = "desc-pi";
    };

    # INFER-mode desc-pi where f is Pi but domain ≠ S. S=Nat, f=λx:Unit.tt
    # (domain=Unit). The rule emits `mkKernelError { position = DPiFn; }`.
    "reject-desc-pi-infer-f-domain-mismatch-position" = {
      expr =
        let r = inferTm ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl
            (T.mkAnn (T.mkLam "_" T.mkUnit T.mkTt)
                     (T.mkPi "_" T.mkUnit T.mkUnit))
            (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiFn";
    };

    # CHECK-mode desc-pi against Desc Unit: bad sort → DPiSort.
    "reject-desc-pi-check-bad-S-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkZero T.mkRefl
            (T.mkLam "_" T.mkNat T.mkTt)
            (T.mkDescRet T.mkTt))
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiSort";
    };

    # CHECK-mode desc-pi: good S=Unit, bad f (zero does not check
    # against Pi Unit Unit). `bindP P.DPiFn` tags it.
    "reject-desc-pi-check-bad-f-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkUnit T.mkRefl T.mkZero (T.mkDescRet T.mkTt))
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiFn";
    };

    # CHECK-mode desc-pi: good S and f, bad tail D=mkZero.
    "reject-desc-pi-check-bad-D-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescPi T.mkLevelZero T.mkLevelZero T.mkUnit T.mkRefl (T.mkLam "_" T.mkUnit T.mkTt) T.mkZero)
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPiBody";
    };

    # INFER-mode desc-plus where A is not synthesising (mkTt has no
    # INFER rule): `bindP P.DPlusL` tags the left summand.
    "reject-desc-plus-infer-bad-A-position" = {
      expr =
        let r = inferTm ctx0 (T.mkDescPlus T.mkTt (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPlusL";
    };

    # INFER-mode desc-plus where A infers but to a non-VDesc: var 0
    # in ctx extended by Nat infers as Nat. The rule emits
    # `mkKernelError { position = DPlusL; rule = "desc-plus"; }`.
    "reject-desc-plus-infer-A-not-desc-position" = {
      expr =
        let ctx' = extend ctx0 "_" vNat;
            r = inferTm ctx' (T.mkDescPlus (T.mkVar 0) (T.mkDescRet T.mkTt));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPlusL";
    };
    "reject-desc-plus-infer-A-not-desc-rule" = {
      expr =
        let ctx' = extend ctx0 "_" vNat;
            r = inferTm ctx' (T.mkDescPlus (T.mkVar 0) (T.mkDescRet T.mkTt));
        in r.error.detail.rule;
      expected = "desc-plus";
    };

    # INFER-mode desc-plus: A is ann-wrapped as Desc Unit (infers OK),
    # B is malformed (mkZero). `bindP P.DPlusR` tags the right summand.
    "reject-desc-plus-infer-bad-B-position" = {
      expr =
        let A = T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit);
            r = inferTm ctx0 (T.mkDescPlus A T.mkZero);
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPlusR";
    };

    # CHECK-mode desc-plus against Desc Unit: bad A → DPlusL.
    "reject-desc-plus-check-bad-A-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescPlus T.mkZero (T.mkDescRet T.mkTt))
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPlusL";
    };

    # CHECK-mode desc-plus: good A, bad B → DPlusR.
    "reject-desc-plus-check-bad-B-position" = {
      expr =
        let r = runCheck (self.check ctx0
          (T.mkDescPlus (T.mkDescRet T.mkTt) T.mkZero)
          (V.vDesc V.vLevelZero vUnit));
        in (builtins.elemAt r.error.children 0).position.tag;
      expected = "DPlusR";
    };

    "infer-desc-ind-ret" = {
      # Motive: (i:I) → μD i → U. Step: Π(i:I). Π(d:Eq Unit tt i). Π(_:Unit). Nat.
      # desc-ind infers tm.D; ann-wrap D so I=Unit is recoverable.
      expr = let
        D = T.mkAnn (T.mkDescRet T.mkTt) (T.mkDesc T.mkLevelZero T.mkUnit);
      in (inferTm ctx0 (T.mkDescInd D
        (T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D (T.mkVar 0)) T.mkNat))
        (T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkEq T.mkUnit T.mkTt (T.mkVar 0))
            (T.mkLam "_" T.mkUnit T.mkZero)))
        T.mkTt
        (T.mkDescCon D T.mkTt T.mkRefl))).type.tag;
      expected = "VNat";
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
    # `funext`'s type is `Π(j:Level). Π(k:Level). T(j,k)`; its universe-
    # level expression mentions the bound levels, so `typeLvl` cannot
    # peel it to a concrete int. Witness heterogeneous universe-
    # polymorphism through the outer binders' names and domain tags
    # instead.
    "infer-funext-type-binds-level-j" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.name;
      expected = "j";
    };
    "infer-funext-type-outer-domain-is-level" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.domain.tag;
      expected = "level";
    };
    "infer-funext-type-binds-level-k" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.codomain.name;
      expected = "k";
    };
    "infer-funext-type-second-domain-is-level" = {
      expr = let
        r = inferTm ctx0 T.mkFunext;
        tyTm = Q.quote 0 r.type;
      in tyTm.codomain.domain.tag;
      expected = "level";
    };
    "check-funext-against-its-type" = {
      expr = let
        funextTy = fx.tc.eval.eval [] T.funextTypeTm;
      in (checkTm ctx0 T.mkFunext funextTy).tag;
      expected = "funext";
    };
    "check-funext-reflexive-application" = {
      # Apply at j=0, k=0 to specialise the heterogeneous Π chain to
      # the homogeneous-at-U(0) shape; the remaining 5-arg spine
      # inhabits the resulting `Eq (Π(a:Nat). Nat) f f` reflexively
      # (pointwise = λ_. refl).
      expr = let
        A = T.mkNat;
        Bty = T.mkPi "_" A (T.mkU T.mkLevelZero);
        B = T.mkAnn (T.mkLam "_" A A) Bty;
        fTy = T.mkPi "a" A A;
        f = T.mkAnn (T.mkLam "_" A T.mkZero) fTy;
        ptTy = T.mkPi "a" A (T.mkEq A T.mkZero T.mkZero);
        pointwise = T.mkAnn (T.mkLam "_" A T.mkRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 0)) (T.mkLevelLit 0)) A) B) f) f) pointwise;
        expectedTy = V.vEq
          (V.vPi "a" V.vNat (V.mkClosure [] A))
          (fx.tc.eval.eval [] f)
          (fx.tc.eval.eval [] f);
      in (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-at-level-one" = {
      # Homogeneous specialisation at j=k=1: A = U(0), B = λ_. A (so B
      # has type A → U(1) and `B a = U(0)`), f = g = λ_. Nat (the
      # constant function picking out a type in U(0)), pointwise = λ_.
      # refl. Exercises the j- and k-binder substitution paths inside
      # the cached `funextTypeVal`.
      expr = let
        A = T.mkU T.mkLevelZero;
        Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
        B = T.mkAnn (T.mkLam "_" A A) Bty;
        fTy = T.mkPi "_" A A;
        f = T.mkAnn (T.mkLam "_" A T.mkNat) fTy;
        ptTy = T.mkPi "_" A (T.mkEq A T.mkNat T.mkNat);
        pointwise = T.mkAnn (T.mkLam "_" A T.mkRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 1)) (T.mkLevelLit 1)) A) B) f) f) pointwise;
        fVal = fx.tc.eval.eval [] f;
        expectedTy = V.vEq
          (V.vPi "_" (V.vU V.vLevelZero) (V.mkClosure [] A))
          fVal
          fVal;
      in (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };
    "check-funext-application-heterogeneous-j0-k1" = {
      # Heterogeneous specialisation at j=0, k=1: A = Nat (at U(0)), B
      # = λ_. desc(⊤) (so B has type Nat → U(1) and `B a = desc ⊤`), f
      # = g = λ_. descRet(tt) (a constant function picking out a
      # description), pointwise = λ_. refl. The codomain B sits at a
      # STRICTLY HIGHER universe than A — exercises the decoupled
      # j ≠ k substitution path through the cached `funextTypeVal`.
      expr = let
        A = T.mkNat;
        descTy = T.mkDesc T.mkLevelZero T.mkUnit;
        Bty = T.mkPi "_" A (T.mkU (T.mkLevelSuc T.mkLevelZero));
        B = T.mkAnn (T.mkLam "_" A descTy) Bty;
        fTy = T.mkPi "_" A descTy;
        f = T.mkAnn (T.mkLam "_" A (T.mkDescRet T.mkTt)) fTy;
        ptTy = T.mkPi "_" A
          (T.mkEq descTy (T.mkDescRet T.mkTt) (T.mkDescRet T.mkTt));
        pointwise = T.mkAnn (T.mkLam "_" A T.mkRefl) ptTy;
        term = T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp (T.mkApp
          T.mkFunext (T.mkLevelLit 0)) (T.mkLevelLit 1)) A) B) f) f) pointwise;
        fVal = fx.tc.eval.eval [] f;
        expectedTy = V.vEq
          (V.vPi "_" V.vNat (V.mkClosure [] descTy))
          fVal
          fVal;
      in (checkTm ctx0 term expectedTy).tag;
      expected = "app";
    };

    "infer-desc-ind-arg" = {
      # D = arg 0 Nat (ret tt) — body is body-Tm under implicit s:Nat, not a lambda.
      # interp at i = Σ(s:Nat). Eq Unit tt i (Var 1 = i from inside the Sigma snd).
      # All = Unit (allOnRet collapses to Unit at ret-leaf for I=⊤).
      expr = let
        D = T.mkAnn (T.mkDescArg T.mkLevelZero T.mkLevelZero T.mkNat T.mkRefl (T.mkDescRet T.mkTt))
                    (T.mkDesc T.mkLevelZero T.mkUnit);
      in (inferTm ctx0 (T.mkDescInd D
        (T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D (T.mkVar 0)) T.mkNat))
        (T.mkLam "i" T.mkUnit
          (T.mkLam "d" (T.mkSigma "s" T.mkNat
            (T.mkEq T.mkUnit T.mkTt (T.mkVar 1)))
            (T.mkLam "_" T.mkUnit T.mkZero)))
        T.mkTt
        (T.mkDescCon D T.mkTt
          (T.mkPair T.mkZero T.mkRefl)))).type.tag;
      expected = "VNat";
    };

    # interp-d / all-d / everywhere-d INFER rules (kernel-primitive
    # interpretation, All-witness, and recursor over Desc).
    # `interpD ℓ I D X i : U(ℓ)` — synthesises `U(ℓ)`.
    "infer-interp-d-ret" = {
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        (T.mkLam "_" T.mkUnit T.mkNat)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-ret-level" = {
      expr = typeLvl (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        (T.mkLam "_" T.mkUnit T.mkNat)
        T.mkTt));
      expected = 0;
    };
    "infer-interp-d-rec" = {
      # interpD 0 ⊤ (rec tt (ret tt)) (λ_:⊤. ℕ) tt : U(0).
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkDescRec T.mkTt (T.mkDescRet T.mkTt))
        (T.mkLam "_" T.mkUnit T.mkNat)
        T.mkTt)).type.tag;
      expected = "VU";
    };
    "infer-interp-d-wrong-X-rejected" = {
      # X must have type `I → U(ℓ)`. Passing X : I → ℕ should reject.
      expr = (inferTm ctx0 (T.mkInterpD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        (T.mkLam "_" T.mkUnit T.mkZero)
        T.mkTt)) ? error;
      expected = true;
    };

    # `allD ℓ I D K X M i d : U(K)` — verify result level rides K.
    # At D=ret tt, ℓ=0: d-binder type is `Eq ⊤ tt tt` (idempotent
    # collapse of `Lift 0 0 _ (Eq ⊤ tt tt)`), inhabited by `refl`.
    "infer-all-d-ret" = {
      expr = (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkNat)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkNat T.mkUnit))
        T.mkTt
        T.mkRefl)).type.tag;
      expected = "VU";
    };
    "infer-all-d-K-level" = {
      # Result lives at U(K), independent of ℓ. Setting K=0 with the
      # ret-leaf D yields a U(0) result.
      expr = typeLvl (inferTm ctx0 (T.mkAllD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkNat)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkNat T.mkUnit))
        T.mkTt
        T.mkRefl));
      expected = 0;
    };

    # `everywhereD ℓ I D K X M ih i d : allD ℓ I D K X M i d`. At
    # D=ret tt and K=0, allD reduces to `Lift 0 0 _ ⊤` ≡ ⊤ (idempotent
    # collapse).
    "infer-everywhere-d-ret" = {
      expr = (inferTm ctx0 (T.mkEverywhereD T.mkLevelZero T.mkUnit
        (T.mkDescRet T.mkTt)
        T.mkLevelZero
        (T.mkLam "_" T.mkUnit T.mkNat)
        (T.mkLam "i" T.mkUnit (T.mkLam "x" T.mkNat T.mkUnit))
        (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkNat T.mkTt))
        T.mkTt
        T.mkRefl)).type.tag;
      expected = "VUnit";
    };
  };
}
