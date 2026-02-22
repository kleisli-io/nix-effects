# Type-checking kernel: Bidirectional type checker (check/infer)
#
# check : Ctx -> Tm -> Val -> Computation Tm     (checking mode)
# infer : Ctx -> Tm -> Computation { term; type; } (synthesis mode)
# checkType : Ctx -> Tm -> Computation Tm         (type formation)
# inferLevel : Val -> Nat                          (universe level)
#
# Semi-trusted (Layer 1): uses TCB (eval/quote/conv) and sends typeError
# effects for error reporting. Bugs here may produce wrong errors but
# cannot cause unsoundness.
#
# Spec reference: kernel-spec.md §7-9
{ fx, api, ... }:

let
  inherit (api) mk;
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  C = fx.tc.conv;

  K = fx.kernel;
  TR = fx.trampoline;

  pure = K.pure;
  send = K.send;
  bind = K.bind;

  # -- Context operations (§7.1) --

  emptyCtx = { env = []; types = []; depth = 0; };

  # Prepend: index 0 = most recent binding (matches eval's convention)
  extend = ctx: name: ty: {
    env = [ (V.freshVar ctx.depth) ] ++ ctx.env;
    types = [ ty ] ++ ctx.types;
    depth = ctx.depth + 1;
  };

  lookupType = ctx: i:
    if i >= builtins.length ctx.types
    then throw "tc: unbound variable index ${toString i} in context of depth ${toString ctx.depth}"
    else builtins.elemAt ctx.types i;

  # -- Type error effect --
  typeError = msg: expected: got: term:
    send "typeError" { inherit msg expected got term; };

  # -- Universe level computation (§8.2) --
  inferLevel = v:
    let t = v.tag; in
    if t == "VNat" || t == "VBool" || t == "VUnit" || t == "VVoid" then 0
    else if t == "VU" then v.level + 1
    else if t == "VList" then inferLevel v.elem
    else if t == "VSum" then
      let a = inferLevel v.left; b = inferLevel v.right;
      in if a >= b then a else b
    else if t == "VPi" then
      let a = inferLevel v.domain;
          b = inferLevel (E.instantiate v.closure (V.freshVar 0));
      in if a >= b then a else b
    else if t == "VSigma" then
      let a = inferLevel v.fst;
          b = inferLevel (E.instantiate v.closure (V.freshVar 0));
      in if a >= b then a else b
    else if t == "VEq" then inferLevel v.type
    else 0;

  # -- Bidirectional type checker --

  # check : Ctx -> Tm -> Val -> Computation Tm  (§7.4)
  check = ctx: tm: ty:
    let t = tm.tag; in

    # Lam checked against Pi
    if t == "lam" && ty.tag == "VPi" then
      let
        dom = ty.domain;
        cod = E.instantiate ty.closure (V.freshVar ctx.depth);
        ctx' = extend ctx tm.name dom;
      in bind (check ctx' tm.body cod) (body':
        pure (T.mkLam tm.name (Q.quote ctx.depth dom) body'))

    # Pair checked against Sigma
    else if t == "pair" && ty.tag == "VSigma" then
      let fstTy = ty.fst; in
      bind (check ctx tm.fst fstTy) (a':
        let bTy = E.instantiate ty.closure (E.eval ctx.env a'); in
        bind (check ctx tm.snd bTy) (b':
          pure (T.mkPair a' b' (Q.quote ctx.depth ty))))

    # Zero checked against Nat
    else if t == "zero" && ty.tag == "VNat" then pure T.mkZero

    # Succ checked against Nat
    else if t == "succ" && ty.tag == "VNat" then
      bind (check ctx tm.pred V.vNat) (p': pure (T.mkSucc p'))

    # True/False checked against Bool
    else if t == "true" && ty.tag == "VBool" then pure T.mkTrue
    else if t == "false" && ty.tag == "VBool" then pure T.mkFalse

    # Nil checked against List
    else if t == "nil" && ty.tag == "VList" then
      pure (T.mkNil (Q.quote ctx.depth ty.elem))

    # Cons checked against List
    else if t == "cons" && ty.tag == "VList" then
      let elemTy = ty.elem; in
      bind (check ctx tm.head elemTy) (h':
        bind (check ctx tm.tail ty) (t':
          pure (T.mkCons (Q.quote ctx.depth elemTy) h' t')))

    # Tt checked against Unit
    else if t == "tt" && ty.tag == "VUnit" then pure T.mkTt

    # Inl checked against Sum
    else if t == "inl" && ty.tag == "VSum" then
      bind (check ctx tm.term ty.left) (v':
        pure (T.mkInl (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

    # Inr checked against Sum
    else if t == "inr" && ty.tag == "VSum" then
      bind (check ctx tm.term ty.right) (v':
        pure (T.mkInr (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

    # Refl checked against Eq — must verify lhs ≡ rhs
    else if t == "refl" && ty.tag == "VEq" then
      if C.conv ctx.depth ty.lhs ty.rhs
      then pure T.mkRefl
      else typeError "refl requires equal sides"
        (Q.quote ctx.depth ty.lhs) (Q.quote ctx.depth ty.rhs) tm

    # Let in checking mode
    else if t == "let" then
      bind (checkType ctx tm.type) (aTm:
        let aVal = E.eval ctx.env aTm; in
        bind (check ctx tm.val aVal) (tTm:
          let
            tVal = E.eval ctx.env tTm;
            ctx' = {
              env = [ tVal ] ++ ctx.env;
              types = [ aVal ] ++ ctx.types;
              depth = ctx.depth + 1;
            };
          in bind (check ctx' tm.body ty) (uTm:
            pure (T.mkLet tm.name aTm tTm uTm))))

    # Sub rule: fall through to synthesis (§7.4 Sub)
    else
      bind (infer ctx tm) (result:
        let inferredTy = result.type; in
        # Cumulativity: VU(i) ≤ VU(j) when i ≤ j (§8.3)
        if inferredTy.tag == "VU" && ty.tag == "VU" && inferredTy.level <= ty.level
        then pure result.term
        else if C.conv ctx.depth inferredTy ty
        then pure result.term
        else typeError "type mismatch"
          (Q.quote ctx.depth ty) (Q.quote ctx.depth inferredTy) tm);

  # infer : Ctx -> Tm -> Computation { term; type; }  (§7.3)
  infer = ctx: tm:
    let t = tm.tag; in

    # Var
    if t == "var" then
      pure { term = tm; type = lookupType ctx tm.idx; }

    # Ann
    else if t == "ann" then
      bind (checkType ctx tm.type) (aTm:
        let aVal = E.eval ctx.env aTm; in
        bind (check ctx tm.term aVal) (tTm:
          pure { term = T.mkAnn tTm aTm; type = aVal; }))

    # App
    else if t == "app" then
      bind (infer ctx tm.fn) (fResult:
        let fTy = fResult.type; in
        if fTy.tag != "VPi"
        then typeError "expected function type" { tag = "pi"; } (Q.quote ctx.depth fTy) tm
        else
          bind (check ctx tm.arg fTy.domain) (uTm:
            let retTy = E.instantiate fTy.closure (E.eval ctx.env uTm); in
            pure { term = T.mkApp fResult.term uTm; type = retTy; }))

    # Fst
    else if t == "fst" then
      bind (infer ctx tm.pair) (pResult:
        let pTy = pResult.type; in
        if pTy.tag != "VSigma"
        then typeError "expected sigma type" { tag = "sigma"; } (Q.quote ctx.depth pTy) tm
        else pure { term = T.mkFst pResult.term; type = pTy.fst; })

    # Snd
    else if t == "snd" then
      bind (infer ctx tm.pair) (pResult:
        let pTy = pResult.type; in
        if pTy.tag != "VSigma"
        then typeError "expected sigma type" { tag = "sigma"; } (Q.quote ctx.depth pTy) tm
        else
          let bTy = E.instantiate pTy.closure (E.vFst (E.eval ctx.env pResult.term)); in
          pure { term = T.mkSnd pResult.term; type = bTy; })

    # NatElim (§7.3)
    else if t == "nat-elim" then
      let
        motiveChkTy = V.vPi "_" V.vNat (V.mkClosure [] (T.mkU 0));
      in bind (check ctx tm.motive motiveChkTy) (pTm:
        let pVal = E.eval ctx.env pTm; in
        bind (check ctx tm.base (E.vApp pVal V.vZero)) (zTm:
          let
            # s : Π(k:Nat). P(k) → P(S(k))
            stepTy = V.vPi "k" V.vNat (V.mkClosure ctx.env
              (T.mkPi "ih" (T.mkApp (Q.quote (ctx.depth + 1) pVal) (T.mkVar 0))
                (T.mkApp (Q.quote (ctx.depth + 2) pVal) (T.mkSucc (T.mkVar 1)))));
          in bind (check ctx tm.step stepTy) (sTm:
            bind (check ctx tm.scrut V.vNat) (nTm:
              let retTy = E.vApp pVal (E.eval ctx.env nTm); in
              pure { term = T.mkNatElim pTm zTm sTm nTm; type = retTy; }))))

    # BoolElim (§7.3)
    else if t == "bool-elim" then
      let
        motiveChkTy = V.vPi "_" V.vBool (V.mkClosure [] (T.mkU 0));
      in bind (check ctx tm.motive motiveChkTy) (pTm:
        let pVal = E.eval ctx.env pTm; in
        bind (check ctx tm.onTrue (E.vApp pVal V.vTrue)) (tTm:
          bind (check ctx tm.onFalse (E.vApp pVal V.vFalse)) (fTm:
            bind (check ctx tm.scrut V.vBool) (bTm:
              let retTy = E.vApp pVal (E.eval ctx.env bTm); in
              pure { term = T.mkBoolElim pTm tTm fTm bTm; type = retTy; }))))

    # ListElim (§7.3)
    else if t == "list-elim" then
      bind (checkType ctx tm.elem) (aRaw:
        let aVal = E.eval ctx.env aRaw;
            motiveChkTy = V.vPi "_" (V.vList aVal) (V.mkClosure [] (T.mkU 0));
        in bind (check ctx tm.motive motiveChkTy) (pTm:
          let pVal = E.eval ctx.env pTm; in
          bind (check ctx tm.nil (E.vApp pVal (V.vNil aVal))) (nTm:
            let
              # c : Π(h:A). Π(t:List A). P(t) → P(cons h t)
              consTy = V.vPi "h" aVal (V.mkClosure ctx.env
                (T.mkPi "t" (T.mkList (Q.quote (ctx.depth + 1) aVal))
                  (T.mkPi "ih" (T.mkApp (Q.quote (ctx.depth + 2) pVal) (T.mkVar 0))
                    (T.mkApp (Q.quote (ctx.depth + 3) pVal)
                      (T.mkCons (Q.quote (ctx.depth + 3) aVal) (T.mkVar 2) (T.mkVar 1))))));
            in bind (check ctx tm.cons consTy) (cTm:
              bind (check ctx tm.scrut (V.vList aVal)) (lTm:
                let retTy = E.vApp pVal (E.eval ctx.env lTm); in
                pure { term = T.mkListElim aRaw pTm nTm cTm lTm; type = retTy; })))))

    # Absurd (§7.3)
    else if t == "absurd" then
      bind (checkType ctx tm.type) (aTm:
        let aVal = E.eval ctx.env aTm; in
        bind (check ctx tm.term V.vVoid) (tTm:
          pure { term = T.mkAbsurd aTm tTm; type = aVal; }))

    # SumElim (§7.3)
    else if t == "sum-elim" then
      bind (checkType ctx tm.left) (aRaw:
        let aVal = E.eval ctx.env aRaw; in
        bind (checkType ctx tm.right) (bRaw:
          let bVal = E.eval ctx.env bRaw;
              motiveChkTy = V.vPi "_" (V.vSum aVal bVal) (V.mkClosure [] (T.mkU 0));
          in bind (check ctx tm.motive motiveChkTy) (pTm:
            let pVal = E.eval ctx.env pTm;
                # l : Π(x:A). P(inl x)
                lTy = V.vPi "x" aVal (V.mkClosure ctx.env
                  (T.mkApp (Q.quote (ctx.depth + 1) pVal)
                    (T.mkInl (Q.quote (ctx.depth + 1) aVal) (Q.quote (ctx.depth + 1) bVal) (T.mkVar 0))));
                # r : Π(y:B). P(inr y)
                rTy = V.vPi "y" bVal (V.mkClosure ctx.env
                  (T.mkApp (Q.quote (ctx.depth + 1) pVal)
                    (T.mkInr (Q.quote (ctx.depth + 1) aVal) (Q.quote (ctx.depth + 1) bVal) (T.mkVar 0))));
            in bind (check ctx tm.onLeft lTy) (lTm:
              bind (check ctx tm.onRight rTy) (rTm:
                bind (check ctx tm.scrut (V.vSum aVal bVal)) (sTm:
                  let retTy = E.vApp pVal (E.eval ctx.env sTm); in
                  pure { term = T.mkSumElim aRaw bRaw pTm lTm rTm sTm; type = retTy; }))))))

    # J (§7.3)
    else if t == "j" then
      bind (checkType ctx tm.type) (aRaw:
        let aVal = E.eval ctx.env aRaw; in
        bind (check ctx tm.lhs aVal) (aTm:
          let aValEvaled = E.eval ctx.env aTm;
              # P : Π(y:A). Π(e:Eq(A,a,y)). U
              pTy = V.vPi "y" aVal (V.mkClosure ctx.env
                (T.mkPi "e" (T.mkEq (Q.quote (ctx.depth + 1) aVal)
                              (Q.quote (ctx.depth + 1) aValEvaled) (T.mkVar 0))
                  (T.mkU 0)));
          in bind (check ctx tm.motive pTy) (pTm:
            let pVal = E.eval ctx.env pTm; in
            bind (check ctx tm.base (E.vApp (E.vApp pVal aValEvaled) V.vRefl)) (prTm:
              bind (check ctx tm.rhs aVal) (bTm:
                let bVal = E.eval ctx.env bTm; in
                bind (check ctx tm.eq (V.vEq aVal aValEvaled bVal)) (eqTm:
                  let retTy = E.vApp (E.vApp pVal bVal) (E.eval ctx.env eqTm); in
                  pure { term = T.mkJ aRaw aTm pTm prTm bTm eqTm; type = retTy; }))))))

    # U(i) infers as U(i+1) (§8.1)
    else if t == "U" then
      pure { term = tm; type = V.vU (tm.level + 1); }

    # Type formers infer via checkType + inferLevel
    else if t == "nat" then pure { term = T.mkNat; type = V.vU 0; }
    else if t == "bool" then pure { term = T.mkBool; type = V.vU 0; }
    else if t == "unit" then pure { term = T.mkUnit; type = V.vU 0; }
    else if t == "void" then pure { term = T.mkVoid; type = V.vU 0; }

    else if t == "pi" then
      bind (checkType ctx tm.domain) (domTm:
        let domVal = E.eval ctx.env domTm;
            ctx' = extend ctx tm.name domVal;
        in bind (checkType ctx' tm.codomain) (codTm:
          let codVal = E.eval ctx'.env codTm;
              lvl = let a = inferLevel domVal; b = inferLevel codVal;
                    in if a >= b then a else b;
          in pure { term = T.mkPi tm.name domTm codTm; type = V.vU lvl; }))

    else if t == "sigma" then
      bind (checkType ctx tm.fst) (fstTm:
        let fstVal = E.eval ctx.env fstTm;
            ctx' = extend ctx tm.name fstVal;
        in bind (checkType ctx' tm.snd) (sndTm:
          let sndVal = E.eval ctx'.env sndTm;
              lvl = let a = inferLevel fstVal; b = inferLevel sndVal;
                    in if a >= b then a else b;
          in pure { term = T.mkSigma tm.name fstTm sndTm; type = V.vU lvl; }))

    else if t == "list" then
      bind (checkType ctx tm.elem) (eTm:
        let eVal = E.eval ctx.env eTm; in
        pure { term = T.mkList eTm; type = V.vU (inferLevel eVal); })

    else if t == "sum" then
      bind (checkType ctx tm.left) (lTm:
        let lVal = E.eval ctx.env lTm; in
        bind (checkType ctx tm.right) (rTm:
          let rVal = E.eval ctx.env rTm;
              lvl = let a = inferLevel lVal; b = inferLevel rVal;
                    in if a >= b then a else b;
          in pure { term = T.mkSum lTm rTm; type = V.vU lvl; }))

    else if t == "eq" then
      bind (checkType ctx tm.type) (aTm:
        let aVal = E.eval ctx.env aTm; in
        bind (check ctx tm.lhs aVal) (lTm:
          bind (check ctx tm.rhs aVal) (rTm:
            pure { term = T.mkEq aTm lTm rTm; type = V.vU (inferLevel aVal); })))

    else typeError "cannot infer type" { tag = "unknown"; } (Q.quote ctx.depth (V.vU 0)) tm;

  # checkType : Ctx -> Tm -> Computation Tm  (§7.5)
  # Verify a term is a type (lives in some universe).
  checkType = ctx: tm:
    let t = tm.tag; in
    if t == "nat" then pure T.mkNat
    else if t == "bool" then pure T.mkBool
    else if t == "unit" then pure T.mkUnit
    else if t == "void" then pure T.mkVoid
    else if t == "U" then pure tm
    else if t == "list" then
      bind (checkType ctx tm.elem) (eTm: pure (T.mkList eTm))
    else if t == "sum" then
      bind (checkType ctx tm.left) (lTm:
        bind (checkType ctx tm.right) (rTm: pure (T.mkSum lTm rTm)))
    else if t == "pi" then
      bind (checkType ctx tm.domain) (domTm:
        let domVal = E.eval ctx.env domTm;
            ctx' = extend ctx tm.name domVal;
        in bind (checkType ctx' tm.codomain) (codTm:
          pure (T.mkPi tm.name domTm codTm)))
    else if t == "sigma" then
      bind (checkType ctx tm.fst) (fstTm:
        let fstVal = E.eval ctx.env fstTm;
            ctx' = extend ctx tm.name fstVal;
        in bind (checkType ctx' tm.snd) (sndTm:
          pure (T.mkSigma tm.name fstTm sndTm)))
    else if t == "eq" then
      bind (checkType ctx tm.type) (aTm:
        let aVal = E.eval ctx.env aTm; in
        bind (check ctx tm.lhs aVal) (lTm:
          bind (check ctx tm.rhs aVal) (rTm:
            pure (T.mkEq aTm lTm rTm))))
    # Fallback: infer and check it's a universe
    else
      bind (infer ctx tm) (result:
        if result.type.tag == "VU"
        then pure result.term
        else typeError "expected a type (universe)" { tag = "U"; }
          (Q.quote ctx.depth result.type) tm);

  # -- Test helpers --
  # Run a computation through handle, aborting on typeError
  runCheck = comp:
    let result = TR.handle {
      handlers.typeError = { param, state }: {
        abort = { error = true; msg = param.msg; expected = param.expected; got = param.got; };
        state = null;
      };
    } comp;
    in result.value;

  # Check a term and return the elaborated term (or error)
  checkTm = ctx: tm: ty: runCheck (check ctx tm ty);
  inferTm = ctx: tm: runCheck (infer ctx tm);

in mk {
  doc = ''
    Bidirectional type checker for the MLTT kernel.
    check/infer return Computation values (freer monad).
    Type errors reported via fx.send "typeError".
  '';
  value = {
    inherit check infer checkType inferLevel;
    inherit emptyCtx extend lookupType;
    inherit runCheck checkTm inferTm;
  };
  tests = let
    inherit (V) vNat vZero vSucc vBool vPi vSigma
      vList vUnit vVoid vSum vEq vU mkClosure;

    # Shorthand
    ctx0 = emptyCtx;

    # Context with one Nat variable
    ctx1 = extend ctx0 "x" vNat;

    # Context with one Void variable (for ex falso)
    ctxV = extend ctx0 "v" vVoid;

  in {
    # -- Context operations --
    "ctx-empty-depth" = { expr = ctx0.depth; expected = 0; };
    "ctx-extend-depth" = { expr = ctx1.depth; expected = 1; };
    "ctx-lookup" = { expr = (lookupType ctx1 0).tag; expected = "VNat"; };

    # -- inferLevel --
    "level-nat" = { expr = inferLevel vNat; expected = 0; };
    "level-bool" = { expr = inferLevel vBool; expected = 0; };
    "level-U0" = { expr = inferLevel (vU 0); expected = 1; };
    "level-U1" = { expr = inferLevel (vU 1); expected = 2; };
    "level-list-nat" = { expr = inferLevel (vList vNat); expected = 0; };
    "level-pi-nat-nat" = {
      expr = inferLevel (vPi "x" vNat (mkClosure [] T.mkNat));
      expected = 0;
    };

    # -- §11.1 Required positive tests --

    # Identity function: λ(x:Nat).x : Π(x:Nat).Nat
    "check-id" = {
      expr = (checkTm ctx0 (T.mkLam "x" T.mkNat (T.mkVar 0))
        (vPi "x" vNat (mkClosure [] T.mkNat))).tag;
      expected = "lam";
    };

    # Zero : Nat
    "check-zero" = {
      expr = (checkTm ctx0 T.mkZero vNat).tag;
      expected = "zero";
    };

    # Succ(Zero) : Nat
    "check-succ" = {
      expr = (checkTm ctx0 (T.mkSucc T.mkZero) vNat).tag;
      expected = "succ";
    };

    # True : Bool
    "check-true" = {
      expr = (checkTm ctx0 T.mkTrue vBool).tag;
      expected = "true";
    };

    # Refl : Eq(Nat, Zero, Zero)
    "check-refl" = {
      expr = (checkTm ctx0 T.mkRefl (vEq vNat vZero vZero)).tag;
      expected = "refl";
    };

    # Pair(Zero, True) : Σ(x:Nat).Bool
    "check-pair" = {
      expr = (checkTm ctx0 (T.mkPair T.mkZero T.mkTrue T.mkUnit)
        (vSigma "x" vNat (mkClosure [] T.mkBool))).tag;
      expected = "pair";
    };

    # Nil(Nat) : List(Nat)
    "check-nil" = {
      expr = (checkTm ctx0 (T.mkNil T.mkNat) (vList vNat)).tag;
      expected = "nil";
    };

    # Cons(Nat, Zero, Nil) : List(Nat)
    "check-cons" = {
      expr = (checkTm ctx0
        (T.mkCons T.mkNat T.mkZero (T.mkNil T.mkNat)) (vList vNat)).tag;
      expected = "cons";
    };

    # Tt : Unit
    "check-tt" = {
      expr = (checkTm ctx0 T.mkTt vUnit).tag;
      expected = "tt";
    };

    # Inl(Nat, Bool, Zero) : Sum(Nat, Bool)
    "check-inl" = {
      expr = (checkTm ctx0 (T.mkInl T.mkNat T.mkBool T.mkZero) (vSum vNat vBool)).tag;
      expected = "inl";
    };

    # Inr(Nat, Bool, True) : Sum(Nat, Bool)
    "check-inr" = {
      expr = (checkTm ctx0 (T.mkInr T.mkNat T.mkBool T.mkTrue) (vSum vNat vBool)).tag;
      expected = "inr";
    };

    # -- Infer tests --

    # Var(0) in context [Nat]
    "infer-var" = {
      expr = (inferTm ctx1 (T.mkVar 0)).type.tag;
      expected = "VNat";
    };

    # Ann(Zero, Nat) infers Nat
    "infer-ann" = {
      expr = (inferTm ctx0 (T.mkAnn T.mkZero T.mkNat)).type.tag;
      expected = "VNat";
    };

    # U(0) : U(1)
    "infer-U0" = {
      expr = (inferTm ctx0 (T.mkU 0)).type.level;
      expected = 1;
    };

    # U(1) : U(2)
    "infer-U1" = {
      expr = (inferTm ctx0 (T.mkU 1)).type.level;
      expected = 2;
    };

    # Nat : U(0)
    "infer-nat-type" = {
      expr = (inferTm ctx0 T.mkNat).type.level;
      expected = 0;
    };

    # Pi(x:Nat, Nat) : U(0)
    "infer-pi-type" = {
      expr = (inferTm ctx0 (T.mkPi "x" T.mkNat T.mkNat)).type.level;
      expected = 0;
    };

    # App: (λx.x) Zero  — via Ann to give lambda a type
    "infer-app" = {
      expr = let
        idFn = T.mkAnn (T.mkLam "x" T.mkNat (T.mkVar 0)) (T.mkPi "x" T.mkNat T.mkNat);
      in (inferTm ctx0 (T.mkApp idFn T.mkZero)).type.tag;
      expected = "VNat";
    };

    # Fst: fst (pair(0, true) : Σ(x:Nat).Bool)
    "infer-fst" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue T.mkUnit)
          (T.mkSigma "x" T.mkNat T.mkBool);
      in (inferTm ctx0 (T.mkFst p)).type.tag;
      expected = "VNat";
    };

    # Snd
    "infer-snd" = {
      expr = let
        p = T.mkAnn (T.mkPair T.mkZero T.mkTrue T.mkUnit)
          (T.mkSigma "x" T.mkNat T.mkBool);
      in (inferTm ctx0 (T.mkSnd p)).type.tag;
      expected = "VBool";
    };

    # Let binding: let x:Nat = 0 in x  checked against Nat
    "check-let" = {
      expr = (checkTm ctx0 (T.mkLet "x" T.mkNat T.mkZero (T.mkVar 0)) vNat).tag;
      expected = "let";
    };

    # -- §11.1 Dependent function: Lam(A, U(0), Lam(x, Var(0), Var(0)))
    "check-poly-id" = {
      expr = let
        ty = vPi "A" (vU 0) (mkClosure [] (T.mkPi "x" (T.mkVar 0) (T.mkVar 1)));
        tm = T.mkLam "A" (T.mkU 0) (T.mkLam "x" (T.mkVar 0) (T.mkVar 0));
      in (checkTm ctx0 tm ty).tag;
      expected = "lam";
    };

    # -- Eliminator inference tests --

    # BoolElim: if true then 0 else 1  infers Nat
    "infer-bool-elim" = {
      expr = (inferTm ctx0 (T.mkBoolElim
        (T.mkLam "b" T.mkBool T.mkNat)
        T.mkZero (T.mkSucc T.mkZero) T.mkTrue)).type.tag;
      expected = "VNat";
    };

    # Absurd: v:Void ⊢ absurd(Nat, v) : Nat
    "infer-absurd" = {
      expr = (inferTm ctxV (T.mkAbsurd T.mkNat (T.mkVar 0))).type.tag;
      expected = "VNat";
    };

    # -- §11.2 Required negative tests --

    # Zero : Bool  REJECT
    "reject-zero-bool" = {
      expr = (checkTm ctx0 T.mkZero vBool) ? error;
      expected = true;
    };

    # U(0) : U(0)  REJECT (universe violation)
    "reject-U0-U0" = {
      expr = (checkTm ctx0 (T.mkU 0) (vU 0)) ? error;
      expected = true;
    };

    # Refl : Eq(Nat, Zero, Succ(Zero))  REJECT
    "reject-refl-unequal" = {
      expr = (checkTm ctx0 T.mkRefl (vEq vNat vZero (vSucc vZero))) ? error;
      expected = true;
    };

    # App(Zero, Zero) REJECT (non-function)
    "reject-app-non-fn" = {
      expr = (inferTm ctx0 (T.mkApp (T.mkAnn T.mkZero T.mkNat) T.mkZero)) ? error;
      expected = true;
    };

    # Fst(Zero) REJECT (non-pair)
    "reject-fst-non-pair" = {
      expr = (inferTm ctx0 (T.mkFst (T.mkAnn T.mkZero T.mkNat))) ? error;
      expected = true;
    };

    # Var(0) in empty context REJECT (force the type to trigger throw)
    "reject-unbound-var" = {
      expr = (builtins.tryEval (builtins.deepSeq (inferTm ctx0 (T.mkVar 0)) true)).success;
      expected = false;
    };

    # Cumulativity: Nat : U(0) also accepted at U(1)
    "check-cumulativity" = {
      expr = (checkTm ctx0 T.mkNat (vU 1)).tag;
      expected = "nat";
    };

    # Cumulativity: U(0) : U(1) accepted
    "check-U0-in-U1" = {
      expr = (checkTm ctx0 (T.mkU 0) (vU 1)).tag;
      expected = "U";
    };

    # Eq type infers
    "infer-eq-type" = {
      expr = (inferTm ctx0 (T.mkEq T.mkNat T.mkZero T.mkZero)).type.tag;
      expected = "VU";
    };

    # Sigma type infers
    "infer-sigma-type" = {
      expr = (inferTm ctx0 (T.mkSigma "x" T.mkNat T.mkBool)).type.tag;
      expected = "VU";
    };

    # Sum type infers
    "infer-sum-type" = {
      expr = (inferTm ctx0 (T.mkSum T.mkNat T.mkBool)).type.tag;
      expected = "VU";
    };

    # List type infers
    "infer-list-type" = {
      expr = (inferTm ctx0 (T.mkList T.mkNat)).type.tag;
      expected = "VU";
    };

    # checkType for Pi
    "checktype-pi" = {
      expr = (runCheck (checkType ctx0 (T.mkPi "x" T.mkNat T.mkBool))).tag;
      expected = "pi";
    };

    # checkType for Sigma
    "checktype-sigma" = {
      expr = (runCheck (checkType ctx0 (T.mkSigma "x" T.mkNat T.mkBool))).tag;
      expected = "sigma";
    };

    # checkType fallback: Ann(Nat, U(0)) is a type — returns Ann wrapper
    "checktype-fallback" = {
      expr = (runCheck (checkType ctx0 (T.mkAnn T.mkNat (T.mkU 0)))).tag;
      expected = "ann";
    };

    # -- §11.1 Theorem tests --

    # 0+0=0 by computation: NatElim(_, 0, λk.λih.S(ih), 0) = 0
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

    # BoolElim typing: BoolElim(_, 0, 1, true) : Nat
    "theorem-bool-elim" = {
      expr = let
        tm = T.mkBoolElim
          (T.mkLam "b" T.mkBool T.mkNat)
          T.mkZero (T.mkSucc T.mkZero) T.mkTrue;
      in (inferTm ctx0 (T.mkAnn tm T.mkNat)).type.tag;
      expected = "VNat";
    };

    # NatElim infers return type: NatElim(λn.Nat, 0, λk.λih.S(ih), S(S(0)))
    "theorem-nat-elim-infer" = {
      expr = (inferTm ctx0 (T.mkNatElim
        (T.mkLam "n" T.mkNat T.mkNat)
        T.mkZero
        (T.mkLam "k" T.mkNat (T.mkLam "ih" T.mkNat (T.mkSucc (T.mkVar 0))))
        (T.mkSucc (T.mkSucc T.mkZero)))).type.tag;
      expected = "VNat";
    };

    # -- §11.3 Stress tests --

    # S^10000(0) : Nat  (spec §11.3 — trampoline stress)
    "stress-large-nat" = {
      expr = let
        bigNat = builtins.foldl' (acc: _: T.mkSucc acc)
          T.mkZero (builtins.genList (x: x) 10000);
      in (checkTm ctx0 bigNat vNat).tag;
      expected = "succ";
    };

    # NatElim on S^1000(0) — trampoline stress (spec §11.3)
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

    # Deeply nested Pi n=500 (spec §11.3)
    "stress-nested-pi" = {
      expr = let
        nested = builtins.foldl' (acc: _: T.mkPi "x" T.mkNat acc)
          T.mkNat (builtins.genList (x: x) 500);
      in (inferTm ctx0 nested).type.level;
      expected = 0;
    };

    # -- §11.4 Roundtrip tests (eval∘quote∘eval idempotency) --

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
      expr = Q.nf [] (Q.nf [] (T.mkPair T.mkZero T.mkTrue T.mkNat))
        == Q.nf [] (T.mkPair T.mkZero T.mkTrue T.mkNat);
      expected = true;
    };
    "roundtrip-nil" = {
      expr = Q.nf [] (Q.nf [] (T.mkNil T.mkNat)) == Q.nf [] (T.mkNil T.mkNat);
      expected = true;
    };
    "roundtrip-app-beta" = {
      # (λx.x) 0 normalizes to 0; re-normalizing 0 gives 0
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
      # NatElim(_, 0, λk.λih.S(ih), S(S(0))) = S(S(0))
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
  };
}
