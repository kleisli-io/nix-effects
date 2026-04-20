# Synthesis mode (§7.3).
#
# `infer : Ctx → Tm → Computation { term; type; }` produces an
# elaborated term together with the kernel value representing its type.
# Covers variables, annotations, application, projections, all
# eliminators (Nat/Bool/List/Sum/Eq via J, plus Desc/Mu), the universe
# hierarchy, every primitive type former, and the Desc constructors
# (`ret`/`arg`/`rec`/`pi`/`con`/`elim`/`ind`). Type formers that infer
# as `U(i)` delegate to `checkTypeLevel` and lift the level into a VU
# type.
#
# Eliminator rules are the most intricate dispatches: each constructs
# the expected motive/step types by quoting the motive at the
# appropriate de Bruijn depth, accounting for the fresh binders that
# each step lambda introduces.
{ self, fx, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  Q = fx.tc.quote;
  C = fx.tc.conv;

  K = fx.kernel;
  pure = K.pure;
  send = K.send;
  bind = K.bind;

  typeError = msg: expected: got: term:
    send "typeError" { inherit msg expected got term; };
in {
  scope = {
    infer = ctx: tm:
      let t = tm.tag; in

      if t == "var" then
        pure { term = tm; type = self.lookupType ctx tm.idx; }

      else if t == "ann" then
        bind (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
          bind (self.check ctx tm.term aVal) (tTm:
            pure { term = T.mkAnn tTm aTm; type = aVal; }))

      else if t == "app" then
        bind (self.infer ctx tm.fn) (fResult:
          let fTy = fResult.type; in
          if fTy.tag != "VPi"
          then typeError "expected function type" { tag = "pi"; } (Q.quote ctx.depth fTy) tm
          else
            bind (self.check ctx tm.arg fTy.domain) (uTm:
              let retTy = E.instantiate fTy.closure (E.eval ctx.env uTm); in
              pure { term = T.mkApp fResult.term uTm; type = retTy; }))

      else if t == "fst" then
        bind (self.infer ctx tm.pair) (pResult:
          let pTy = pResult.type; in
          if pTy.tag != "VSigma"
          then typeError "expected sigma type" { tag = "sigma"; } (Q.quote ctx.depth pTy) tm
          else pure { term = T.mkFst pResult.term; type = pTy.fst; })

      else if t == "snd" then
        bind (self.infer ctx tm.pair) (pResult:
          let pTy = pResult.type; in
          if pTy.tag != "VSigma"
          then typeError "expected sigma type" { tag = "sigma"; } (Q.quote ctx.depth pTy) tm
          else
            let bTy = E.instantiate pTy.closure (E.vFst (E.eval ctx.env pResult.term)); in
            pure { term = T.mkSnd pResult.term; type = bTy; })

      else if t == "nat-elim" then
        bind (self.checkMotive ctx tm.motive (self.singleton V.vNat)) (pTm:
          let pVal = E.eval ctx.env pTm; in
          bind (self.check ctx tm.base (E.vApp pVal V.vZero)) (zTm:
            let
              # s : Π(k:Nat). P(k) → P(S(k))
              # De Bruijn arithmetic: closure body is evaluated at depth+1
              # (binding k).
              #   depth+1: quote pVal relative to outer ctx extended by k
              #   Var(0) = k (most recent binding)
              # Inner Pi "ih" adds another binding at depth+2:
              #   depth+2: quote pVal relative to ctx extended by k and ih
              #   Var(0) = ih, Var(1) = k
              stepTy = V.vPi "k" V.vNat (V.mkClosure ctx.env
                (T.mkPi "ih" (T.mkApp (Q.quote (ctx.depth + 1) pVal) (T.mkVar 0))
                  (T.mkApp (Q.quote (ctx.depth + 2) pVal) (T.mkSucc (T.mkVar 1)))));
            in bind (self.check ctx tm.step stepTy) (sTm:
              bind (self.check ctx tm.scrut V.vNat) (nTm:
                let retTy = E.vApp pVal (E.eval ctx.env nTm); in
                pure { term = T.mkNatElim pTm zTm sTm nTm; type = retTy; }))))

      else if t == "bool-elim" then
        bind (self.checkMotive ctx tm.motive (self.singleton V.vBool)) (pTm:
          let pVal = E.eval ctx.env pTm; in
          bind (self.check ctx tm.onTrue (E.vApp pVal V.vTrue)) (tTm:
            bind (self.check ctx tm.onFalse (E.vApp pVal V.vFalse)) (fTm:
              bind (self.check ctx tm.scrut V.vBool) (bTm:
                let retTy = E.vApp pVal (E.eval ctx.env bTm); in
                pure { term = T.mkBoolElim pTm tTm fTm bTm; type = retTy; }))))

      else if t == "list-elim" then
        bind (self.checkType ctx tm.elem) (aRaw:
          let aVal = E.eval ctx.env aRaw;
          in bind (self.checkMotive ctx tm.motive (self.singleton (V.vList aVal))) (pTm:
            let pVal = E.eval ctx.env pTm; in
            bind (self.check ctx tm.nil (E.vApp pVal (V.vNil aVal))) (nTm:
              let
                # c : Π(h:A). Π(t:List A). P(t) → P(cons h t)
                # De Bruijn arithmetic:
                #   depth+1: h is Var(0)
                #   depth+2: t is Var(0), h is Var(1)
                #   depth+3: ih is Var(0), t is Var(1), h is Var(2)
                # P(cons h t) uses Var(2)=h, Var(1)=t at depth+3
                consTy = V.vPi "h" aVal (V.mkClosure ctx.env
                  (T.mkPi "t" (T.mkList (Q.quote (ctx.depth + 1) aVal))
                    (T.mkPi "ih" (T.mkApp (Q.quote (ctx.depth + 2) pVal) (T.mkVar 0))
                      (T.mkApp (Q.quote (ctx.depth + 3) pVal)
                        (T.mkCons (Q.quote (ctx.depth + 3) aVal) (T.mkVar 2) (T.mkVar 1))))));
              in bind (self.check ctx tm.cons consTy) (cTm:
                bind (self.check ctx tm.scrut (V.vList aVal)) (lTm:
                  let retTy = E.vApp pVal (E.eval ctx.env lTm); in
                  pure { term = T.mkListElim aRaw pTm nTm cTm lTm; type = retTy; })))))

      else if t == "absurd" then
        bind (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
          bind (self.check ctx tm.term V.vVoid) (tTm:
            pure { term = T.mkAbsurd aTm tTm; type = aVal; }))

      else if t == "sum-elim" then
        bind (self.checkType ctx tm.left) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bind (self.checkType ctx tm.right) (bRaw:
            let bVal = E.eval ctx.env bRaw;
            in bind (self.checkMotive ctx tm.motive (self.singleton (V.vSum aVal bVal))) (pTm:
              let pVal = E.eval ctx.env pTm;
                  # l : Π(x:A). P(inl x)
                  # De Bruijn: closure binds x at depth+1. Var(0) = x.
                  # All quotes at depth+1 to account for the x binding.
                  lTy = V.vPi "x" aVal (V.mkClosure ctx.env
                    (T.mkApp (Q.quote (ctx.depth + 1) pVal)
                      (T.mkInl (Q.quote (ctx.depth + 1) aVal) (Q.quote (ctx.depth + 1) bVal) (T.mkVar 0))));
                  # r : Π(y:B). P(inr y)
                  rTy = V.vPi "y" bVal (V.mkClosure ctx.env
                    (T.mkApp (Q.quote (ctx.depth + 1) pVal)
                      (T.mkInr (Q.quote (ctx.depth + 1) aVal) (Q.quote (ctx.depth + 1) bVal) (T.mkVar 0))));
              in bind (self.check ctx tm.onLeft lTy) (lTm:
                bind (self.check ctx tm.onRight rTy) (rTm:
                  bind (self.check ctx tm.scrut (V.vSum aVal bVal)) (sTm:
                    let retTy = E.vApp pVal (E.eval ctx.env sTm); in
                    pure { term = T.mkSumElim aRaw bRaw pTm lTm rTm sTm; type = retTy; }))))))

      else if t == "j" then
        bind (self.checkType ctx tm.type) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bind (self.check ctx tm.lhs aVal) (aTm:
            let aValEvaled = E.eval ctx.env aTm;
                # P : Π(y:A). Π(e:Eq(A,a,y)). U(k) for some k
                eqDomTy = depth: V.vEq aVal aValEvaled (V.freshVar depth);
                checkJMotive =
                  if tm.motive.tag == "lam" then
                    let ctx' = self.extend ctx tm.motive.name aVal;
                    in bind (self.checkMotive ctx' tm.motive.body (self.singleton (eqDomTy ctx.depth))) (innerTm:
                      pure (T.mkLam tm.motive.name (Q.quote ctx.depth aVal) innerTm))
                  else
                    bind (self.infer ctx tm.motive) (result:
                      let rTy = result.type; in
                      if rTy.tag != "VPi"
                      then typeError "J motive must be a function"
                        { tag = "pi"; } (Q.quote ctx.depth rTy) tm.motive
                      else if !(C.conv ctx.depth rTy.domain aVal)
                      then typeError "J motive domain mismatch"
                        (Q.quote ctx.depth aVal) (Q.quote ctx.depth rTy.domain) tm.motive
                      else
                        let innerTy = E.instantiate rTy.closure (V.freshVar ctx.depth); in
                        if innerTy.tag != "VPi"
                        then typeError "J motive must take two arguments"
                          { tag = "pi"; } (Q.quote (ctx.depth + 1) innerTy) tm.motive
                        else if !(C.conv (ctx.depth + 1) innerTy.domain (eqDomTy ctx.depth))
                        then typeError "J motive inner domain must be Eq(A, a, y)"
                          (Q.quote (ctx.depth + 1) (eqDomTy ctx.depth))
                          (Q.quote (ctx.depth + 1) innerTy.domain) tm.motive
                        else
                          let codVal = E.instantiate innerTy.closure (V.freshVar (ctx.depth + 1)); in
                          if codVal.tag != "VU"
                          then typeError "J motive must return a type"
                            { tag = "U"; } (Q.quote (ctx.depth + 2) codVal) tm.motive
                          else pure result.term);
            in bind checkJMotive (pTm:
              let pVal = E.eval ctx.env pTm; in
              bind (self.check ctx tm.base (E.vApp (E.vApp pVal aValEvaled) V.vRefl)) (prTm:
                bind (self.check ctx tm.rhs aVal) (bTm:
                  let bVal = E.eval ctx.env bTm; in
                  bind (self.check ctx tm.eq (V.vEq aVal aValEvaled bVal)) (eqTm:
                    let retTy = E.vApp (E.vApp pVal bVal) (E.eval ctx.env eqTm); in
                    pure { term = T.mkJ aRaw aTm pTm prTm bTm eqTm; type = retTy; }))))))

      # U(i) infers as U(i+1) (§8.1)
      else if t == "U" then
        pure { term = tm; type = V.vU (tm.level + 1); }

      # Type formers infer at U(0)
      else if t == "nat" then pure { term = T.mkNat; type = V.vU 0; }
      else if t == "bool" then pure { term = T.mkBool; type = V.vU 0; }
      else if t == "unit" then pure { term = T.mkUnit; type = V.vU 0; }
      else if t == "void" then pure { term = T.mkVoid; type = V.vU 0; }
      else if t == "string" then pure { term = T.mkString; type = V.vU 0; }
      else if t == "int" then pure { term = T.mkInt; type = V.vU 0; }
      else if t == "float" then pure { term = T.mkFloat; type = V.vU 0; }
      else if t == "attrs" then pure { term = T.mkAttrs; type = V.vU 0; }
      else if t == "path" then pure { term = T.mkPath; type = V.vU 0; }
      else if t == "function" then pure { term = T.mkFunction; type = V.vU 0; }
      else if t == "any" then pure { term = T.mkAny; type = V.vU 0; }
      # desc I — takes an index type. `desc I : U(1)`.
      else if t == "desc" then
        bind (self.check ctx tm.I (V.vU 0)) (iTm:
          pure { term = T.mkDesc iTm; type = V.vU 1; })

      # desc-ret j — `ret j : Desc I` where I is inferred from j's type.
      else if t == "desc-ret" then
        bind (self.infer ctx tm.j) (jResult:
          pure { term = T.mkDescRet jResult.term; type = V.vDesc jResult.type; })

      # desc-arg (§2.4). `S` must live in `V.vU 0`: descriptions carry
      # only small types, so any description argument type is in U 0.
      # The body `T : S → Desc I` is inferred to determine I.
      else if t == "desc-arg" then
        bind (self.check ctx tm.S (V.vU 0)) (sTm:
          let sVal = E.eval ctx.env sTm;
              ctx' = self.extend ctx "_" sVal;
          in bind (self.infer ctx' tm.T) (tResult:
            if tResult.type.tag != "VDesc"
            then typeError "desc-arg: body must have type Desc I"
              { tag = "desc"; } (Q.quote ctx'.depth tResult.type) tm.T
            else
              pure { term = T.mkDescArg sTm tResult.term;
                     type = V.vDesc tResult.type.I; }))

      # desc-rec j D — `rec j D : Desc I`. Infer j's type to get I,
      # then check D against Desc I.
      else if t == "desc-rec" then
        bind (self.infer ctx tm.j) (jResult:
          let iVal = jResult.type; in
          bind (self.check ctx tm.D (V.vDesc iVal)) (dTm:
            pure { term = T.mkDescRec jResult.term dTm;
                   type = V.vDesc iVal; }))

      # desc-pi S f D — `pi S f D : Desc I` where f : S → I determines I.
      else if t == "desc-pi" then
        bind (self.check ctx tm.S (V.vU 0)) (sTm:
          let sVal = E.eval ctx.env sTm;
          in bind (self.infer ctx tm.f) (fResult:
            let fTy = fResult.type; in
            if fTy.tag != "VPi"
            then typeError "desc-pi: f must have type S → I"
              { tag = "pi"; } (Q.quote ctx.depth fTy) tm.f
            else if !(C.conv ctx.depth fTy.domain sVal)
            then typeError "desc-pi: f domain does not match S"
              (Q.quote ctx.depth sVal) (Q.quote ctx.depth fTy.domain) tm.f
            else
              # I = codomain (non-dependent on s per the Desc grammar).
              let iVal = E.instantiate fTy.closure (V.freshVar ctx.depth);
              in bind (self.check ctx tm.D (V.vDesc iVal)) (dTm:
                pure { term = T.mkDescPi sTm fResult.term dTm;
                       type = V.vDesc iVal; })))

      # desc-plus A B — `plus A B : Desc I`. Infer A to determine I, then
      # check B against the same Desc I. Both summands share an index type.
      else if t == "desc-plus" then
        bind (self.infer ctx tm.A) (aResult:
          let aTy = aResult.type; in
          if aTy.tag != "VDesc"
          then typeError "desc-plus: A must have type Desc I"
            { tag = "desc"; } (Q.quote ctx.depth aTy) tm.A
          else
            let iVal = aTy.I; in
            bind (self.check ctx tm.B (V.vDesc iVal)) (bTm:
              pure { term = T.mkDescPlus aResult.term bTm;
                     type = V.vDesc iVal; }))

      # desc-con D i d — `con : μ D i` packing payload d at index i.
      else if t == "desc-con" then
        bind (self.infer ctx tm.D) (dResult:
          let dTy = dResult.type; in
          if dTy.tag != "VDesc"
          then typeError "desc-con: D must have type Desc I"
            { tag = "desc"; } (Q.quote ctx.depth dTy) tm.D
          else
            let iTyVal = dTy.I;
                dVal = E.eval ctx.env dResult.term;
            in bind (self.check ctx tm.i iTyVal) (iTm:
              let iVal = E.eval ctx.env iTm;
                  # X = λ(_i:I). μ I D _i as a VLam so interp can apply it.
                  muDFunc = V.vLam "_i" iTyVal (V.mkClosure [ dVal iTyVal ]
                    (T.mkMu (T.mkVar 2) (T.mkVar 1) (T.mkVar 0)));
                  interpTy = E.interp iTyVal dVal muDFunc iVal;
              in bind (self.check ctx tm.d interpTy) (dataTm:
                pure { term = T.mkDescCon dResult.term iTm dataTm;
                       type = V.vMu iTyVal dVal iVal; })))

      else if t == "desc-elim" then
        # I is recovered from the scrutinee's inferred type (Desc I),
        # not the motive's — the motive may be a bare lam (as built by
        # interpHoas / allHoas in hoas/desc.nix), for which synthesis has
        # no rule. checkMotive accepts bare lams by descending under the
        # known domain, and preserves large elim (motive body may return
        # any universe level).
        bind (self.infer ctx tm.scrut) (sResult:
          let sTy = sResult.type; in
          if sTy.tag != "VDesc"
          then typeError "desc-elim: scrutinee must have type Desc I"
            { tag = "desc"; } (Q.quote ctx.depth sTy) tm.scrut
          else
            let
              iTyVal = sTy.I;
              iTyTm = Q.quote ctx.depth iTyVal;
            in bind (self.checkMotive ctx tm.motive (self.singleton (V.vDesc iTyVal))) (pTm:
              let
                pVal = E.eval ctx.env pTm;
                pQ1 = Q.quote (ctx.depth + 1) pVal;
                pQ2 = Q.quote (ctx.depth + 2) pVal;
                pQ3 = Q.quote (ctx.depth + 3) pVal;
                pQ4 = Q.quote (ctx.depth + 4) pVal;
                # pr : Π(j:I). P (ret j)
                prTy = V.vPi "j" iTyVal (V.mkClosure ctx.env
                  (T.mkApp pQ1 (T.mkDescRet (T.mkVar 0))));
                # pa : Π(S:U(0)). Π(T:S→Desc I). (Π(s:S). P (T s)) → P (arg S T)
                paTy = V.vPi "S" (V.vU 0) (V.mkClosure ctx.env
                  (T.mkPi "T" (T.mkPi "_" (T.mkVar 0) (T.mkDesc iTyTm))
                    (T.mkPi "ih" (T.mkPi "s" (T.mkVar 1)
                        (T.mkApp pQ3 (T.mkApp (T.mkVar 1) (T.mkVar 0))))
                      (T.mkApp pQ3
                        (T.mkDescArg (T.mkVar 2)
                          (T.mkApp (T.mkVar 2) (T.mkVar 0)))))));
                # pe : Π(j:I). Π(D:Desc I). P D → P (rec j D)
                peTy = V.vPi "j" iTyVal (V.mkClosure ctx.env
                  (T.mkPi "D" (T.mkDesc iTyTm)
                    (T.mkPi "ih" (T.mkApp pQ2 (T.mkVar 0))
                      (T.mkApp pQ3 (T.mkDescRec (T.mkVar 2) (T.mkVar 1))))));
                # pp : Π(S:U(0)). Π(f:S→I). Π(D:Desc I). P D → P (pi S f D)
                ppTy = V.vPi "S" (V.vU 0) (V.mkClosure ctx.env
                  (T.mkPi "f" (T.mkPi "_" (T.mkVar 0) iTyTm)
                    (T.mkPi "D" (T.mkDesc iTyTm)
                      (T.mkPi "ih" (T.mkApp pQ3 (T.mkVar 0))
                        (T.mkApp pQ4
                          (T.mkDescPi (T.mkVar 3) (T.mkVar 2) (T.mkVar 1)))))));
                  # pq : Π(A:Desc I). Π(B:Desc I). P A → P B → P (plus A B)
                pqTy = V.vPi "A" (V.vDesc iTyVal) (V.mkClosure ctx.env
                  (T.mkPi "B" (T.mkDesc iTyTm)
                    (T.mkPi "ihA" (T.mkApp pQ2 (T.mkVar 1))
                      (T.mkPi "ihB" (T.mkApp pQ3 (T.mkVar 1))
                        (T.mkApp pQ4 (T.mkDescPlus (T.mkVar 3) (T.mkVar 2)))))));
            in bind (self.check ctx tm.onRet prTy) (prTm:
                bind (self.check ctx tm.onArg paTy) (paTm:
                  bind (self.check ctx tm.onRec peTy) (peTm:
                    bind (self.check ctx tm.onPi ppTy) (ppTm:
                      bind (self.check ctx tm.onPlus pqTy) (pqTm:
                        let retTy = E.vApp pVal (E.eval ctx.env sResult.term); in
                        pure { term = T.mkDescElim pTm prTm paTm peTm ppTm pqTm sResult.term;
                               type = retTy; })))))))

      else if t == "desc-ind" then
        bind (self.infer ctx tm.D) (dResult:
          let dTy = dResult.type; in
          if dTy.tag != "VDesc"
          then typeError "desc-ind: D must have type Desc I"
            { tag = "desc"; } (Q.quote ctx.depth dTy) tm.D
          else
            let
              iTyVal = dTy.I;
              dTm = dResult.term;
              dVal = E.eval ctx.env dTm;
              # motive : (i:I) → μ I D i → U(k)
              # 2-layer dependent chain: the inner domain `μ D i` depends
              # on the outer binder `i : I`. `checkMotive` walks both
              # lam layers and checks the innermost codomain as a type
              # at any universe level, matching the large-elim treatment
              # of the other eliminator rules.
              chain = {
                head = iTyVal;
                tail = iVal: {
                  head = V.vMu iTyVal dVal iVal;
                  tail = _xVal: null;
                };
              };
            in bind (self.checkMotive ctx tm.motive chain) (pTm:
              let
                pVal = E.eval ctx.env pTm;
                # step : Π(i:I). Π(d : ⟦D⟧(μ D) i). All D P i d → P i (con i d)
                iVar = V.freshVar ctx.depth;
                muDFunc1 = V.vLam "_i" iTyVal (V.mkClosure [ dVal iTyVal ]
                  (T.mkMu (T.mkVar 2) (T.mkVar 1) (T.mkVar 0)));
                interpTyAtI = E.interp iTyVal dVal muDFunc1 iVar;
                dVar = V.freshVar (ctx.depth + 1);
                allTyAtI = E.allTy iTyVal dVal dVal pVal iVar dVar;
                retTyAtI = E.vApp (E.vApp pVal iVar) (V.vDescCon dVal iVar dVar);
                stepTy = V.vPi "i" iTyVal (V.mkClosure ctx.env
                  (T.mkPi "d" (Q.quote (ctx.depth + 1) interpTyAtI)
                    (T.mkPi "_" (Q.quote (ctx.depth + 2) allTyAtI)
                      (Q.quote (ctx.depth + 3) retTyAtI))));
              in bind (self.check ctx tm.step stepTy) (stepTm:
                bind (self.check ctx tm.i iTyVal) (iTm:
                  let iVal = E.eval ctx.env iTm; in
                  bind (self.check ctx tm.scrut (V.vMu iTyVal dVal iVal)) (xTm:
                    let retTy = E.vApp (E.vApp pVal iVal)
                                  (E.eval ctx.env xTm); in
                    pure { term = T.mkDescInd dTm pTm stepTm iTm xTm;
                           type = retTy; })))))

      # Primitive literals infer their types
      else if t == "string-lit" then pure { term = T.mkStringLit tm.value; type = V.vString; }
      else if t == "int-lit" then pure { term = T.mkIntLit tm.value; type = V.vInt; }
      else if t == "float-lit" then pure { term = T.mkFloatLit tm.value; type = V.vFloat; }
      else if t == "attrs-lit" then pure { term = T.mkAttrsLit; type = V.vAttrs; }
      else if t == "path-lit" then pure { term = T.mkPathLit; type = V.vPath; }
      else if t == "fn-lit" then pure { term = T.mkFnLit; type = V.vFunction; }
      else if t == "any-lit" then pure { term = T.mkAnyLit; type = V.vAny; }

      # Opaque lambda: infer Pi type from annotation.
      else if t == "opaque-lam" then
        bind (self.checkType ctx tm.piTy) (piTyTm:
          let piTyVal = E.eval ctx.env piTyTm; in
          if piTyVal.tag != "VPi" then
            typeError "opaque-lam annotation must be Pi"
              { tag = "pi"; } (Q.quote ctx.depth piTyVal) tm
          else pure { term = T.mkOpaqueLam tm._fnBox piTyTm; type = piTyVal; })

      # StrEq: both args must be String, result is Bool (plus-encoded).
      else if t == "str-eq" then
        bind (self.check ctx tm.lhs V.vString) (lhsTm:
          bind (self.check ctx tm.rhs V.vString) (rhsTm:
            let boolVal = V.vMu V.vUnit (V.vDescPlus (V.vDescRet V.vTt) (V.vDescRet V.vTt)) V.vTt;
            in pure { term = T.mkStrEq lhsTm rhsTm; type = boolVal; }))

      else if t == "pi" || t == "sigma" || t == "list" || t == "sum" || t == "eq" || t == "mu" then
        bind (self.checkTypeLevel ctx tm) (r:
          pure { term = r.term; type = V.vU r.level; })

      else typeError "cannot infer type" { tag = "unknown"; } (Q.quote ctx.depth (V.vU 0)) tm;
  };
  tests = {};
}
