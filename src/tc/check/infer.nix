# Synthesis mode (§7.3).
#
# `infer : Ctx → Tm → Computation { term; type; }` produces an
# elaborated term together with the kernel value representing its type.
# Covers variables, annotations, application, projections, eliminators,
# the universe hierarchy, primitive type formers, and Desc/Mu operations.
# Type formers that infer as `U(i)` delegate to `checkTypeLevel` and lift
# the level into a VU type.
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

  D = fx.diag.error;
  P = fx.diag.positions;
  H = fx.tc.hoas;

  # Hoist the fixpoint-resolved rule-body combinators out of the rule
  # dispatch. Each `self.X` is an attribute lookup on the kernel
  # fixpoint; referenced from inside a 5000-deep rule-descent loop, the
  # cost compounds. Binding once at module init collapses each use site
  # to a plain variable reference.
  bindP = self.bindP;
  bindPChain = self.bindPChain;

  # Shared `U(0)` / `U(1)` values. Every type former infers at `U(0)`,
  # and `desc I` infers at `U(1)`; constructing a fresh attrset per call
  # was a hot-path allocation. The level field is the `VLevelZero` /
  # `VLevelSuc VLevelZero` singleton in each case.
  vU0 = V.vU V.vLevelZero;
  vU1 = V.vU (V.vLevelSuc V.vLevelZero);
  boolTyVal = E.eval [] (H.elab H.bool);

  # Cached evaluation of funext's polymorphic Π-type. The Tm lives at
  # term.nix (closed, no free variables), so evaluating once at module
  # initialisation is sound — the VPi chain is shared across every
  # infer call that hits the "funext" branch.
  funextTypeVal = E.eval [] T.funextTypeTm;
in {
  scope = {
    infer = ctx: tm:
      let t = tm.tag; in

      if t == "var" then
        pure { term = tm; type = self.lookupType ctx tm.idx; }

      else if t == "ann" then
        # `trusted` ann's body is type-correct by construction (kernel-
        # internal emission only — see `T.mkAnnTrusted`). Skipping the
        # body re-check eliminates per-layer redundant work on deep
        # recursive-data CHECK where each layer's element-D ann is the
        # same encoded description; pre-fix, `infer ctx (ann body type)`
        # ran `self.check ctx body type` per layer, walking the encoded
        # encoder cascade ~20ms per layer (~100× regression vs pre-γ
        # bare canonical bodies).
        bindP P.AnnType (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
	          if tm.trusted or false
	          then pure {
	            term =
	              if tm ? _descRef
	              then T.mkAnnTrustedWithDescRef tm.term aTm tm._descRef
	              else T.mkAnnTrusted tm.term aTm;
	            type = aVal;
	          }
	          else bindP P.AnnTerm (self.check ctx tm.term aVal) (tTm:
	            pure { term = T.mkAnn tTm aTm; type = aVal; }))

      else if t == "app" then
        bindP P.AppHead (self.infer ctx tm.fn) (fResult:
          let fTy = fResult.type; in
          if fTy.tag != "VPi"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.AppHead;
              rule     = "app";
              msg      = "expected function type";
              expected = { tag = "pi"; };
              got      = Q.quote ctx.depth fTy;
            };
          }
          else
            bindP P.AppArg (self.check ctx tm.arg fTy.domain) (uTm:
              let retTy = E.instantiate fTy.closure (E.eval ctx.env uTm); in
              pure { term = T.mkApp fResult.term uTm; type = retTy; }))

      else if t == "fst" then
        bindP P.Scrut (self.infer ctx tm.pair) (pResult:
          let pTy = pResult.type; in
          if pTy.tag != "VSigma"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.Scrut;
              rule     = "fst";
              msg      = "expected sigma type";
              expected = { tag = "sigma"; };
              got      = Q.quote ctx.depth pTy;
            };
          }
          else pure { term = T.mkFst pResult.term; type = pTy.fst; })

      else if t == "snd" then
        bindP P.Scrut (self.infer ctx tm.pair) (pResult:
          let pTy = pResult.type; in
          if pTy.tag != "VSigma"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.Scrut;
              rule     = "snd";
              msg      = "expected sigma type";
              expected = { tag = "sigma"; };
              got      = Q.quote ctx.depth pTy;
            };
          }
          else
            let bTy = E.instantiate pTy.closure (E.vFst (E.eval ctx.env pResult.term)); in
            pure { term = T.mkSnd pResult.term; type = bTy; })

      else if t == "boot-sum-elim" then
        bind (self.checkType ctx tm.left) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bind (self.checkType ctx tm.right) (bRaw:
            let bVal = E.eval ctx.env bRaw;
            in bindP P.Motive (self.checkMotive ctx tm.motive (self.singleton (V.vBootSum aVal bVal))) (pR:
              let pTm = pR.term;
                  pVal = E.eval ctx.env pTm;
                  # Capture pVal, aVal, bVal in the closure env so the
                  # body Tms reference them by `Var` instead of `Q.quote`.
                  # `Q.quote pVal` would re-emit any stuck `VNe` spine
                  # frames as `Var idx` Tms whose semantics break under
                  # re-eval at a different env shape. extEnv layout
                  # (idx-from-0):
                  # 0:pVal, 1:aVal, 2:bVal. ctx.env follows from idx 3.
                  # Inside the x-binder body (depth+1):
                  # Var 1=pVal, Var 2=aVal, Var 3=bVal.
                  extEnv = [ pVal aVal bVal ] ++ ctx.env;
                  # l : Π(x:A). P(inl x)
                  lTy = V.vPi "x" aVal (V.mkClosure extEnv
                    (T.mkApp (T.mkVar 1)
                      (T.mkBootInl (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))));
                  # r : Π(y:B). P(inr y)
                  rTy = V.vPi "y" bVal (V.mkClosure extEnv
                    (T.mkApp (T.mkVar 1)
                      (T.mkBootInr (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))));
              in bindP (P.Case "inl") (self.check ctx tm.onLeft lTy) (lTm:
                bindP (P.Case "inr") (self.check ctx tm.onRight rTy) (rTm:
                  bindP P.Scrut (self.check ctx tm.scrut (V.vBootSum aVal bVal)) (sTm:
                    let retTy = E.vApp pVal (E.eval ctx.env sTm); in
                    pure { term = T.mkBootSumElim aRaw bRaw pTm lTm rTm sTm; type = retTy; }))))))

      else if t == "boot-j" then
        bindP P.JType (self.checkType ctx tm.type) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bindP P.JLhs (self.check ctx tm.lhs aVal) (aTm:
            let aValEvaled = E.eval ctx.env aTm;
                # P : Π(y:A). Π(e:Eq(A,a,y)). U(k) for some k
                eqDomTy = depth: V.vBootEq aVal aValEvaled (V.freshVar depth);
                jMotiveErr = msg: expected: got:
                  send "typeError" {
                    error = D.mkKernelError {
                      position = P.Motive;
                      rule     = "j";
                      inherit msg expected got;
                    };
                  };
                checkJMotive =
                  if tm.motive.tag == "lam" then
                    let ctx' = self.extend ctx tm.motive.name aVal;
                    in bind (self.checkMotive ctx' tm.motive.body (self.singleton (eqDomTy ctx.depth))) (innerR:
                      pure (T.mkLam tm.motive.name (Q.quote ctx.depth aVal) innerR.term))
                  else
                    bindP P.Motive (self.infer ctx tm.motive) (result:
                      let rTy = result.type; in
                      if rTy.tag != "VPi"
                      then jMotiveErr "J motive must be a function"
                        { tag = "pi"; } (Q.quote ctx.depth rTy)
                      else if !(C.conv ctx.depth rTy.domain aVal)
                      then jMotiveErr "J motive domain mismatch"
                        (Q.quote ctx.depth aVal) (Q.quote ctx.depth rTy.domain)
                      else
                        let innerTy = E.instantiate rTy.closure (V.freshVar ctx.depth); in
                        if innerTy.tag != "VPi"
                        then jMotiveErr "J motive must take two arguments"
                          { tag = "pi"; } (Q.quote (ctx.depth + 1) innerTy)
                        else if !(C.conv (ctx.depth + 1) innerTy.domain (eqDomTy ctx.depth))
                        then jMotiveErr "J motive inner domain must be Eq(A, a, y)"
                          (Q.quote (ctx.depth + 1) (eqDomTy ctx.depth))
                          (Q.quote (ctx.depth + 1) innerTy.domain)
                        else
                          let codVal = E.instantiate innerTy.closure (V.freshVar (ctx.depth + 1)); in
                          if codVal.tag != "VU"
                          then jMotiveErr "J motive must return a type"
                            { tag = "U"; } (Q.quote (ctx.depth + 2) codVal)
                          else pure result.term);
            in bind checkJMotive (pTm:
              let pVal = E.eval ctx.env pTm; in
              bindP (P.Case "base") (self.check ctx tm.base (E.vApp (E.vApp pVal aValEvaled) V.vBootRefl)) (prTm:
                bindP P.JRhs (self.check ctx tm.rhs aVal) (bTm:
                  let bVal = E.eval ctx.env bTm; in
                  bindP P.JEq (self.check ctx tm.eq (V.vBootEq aVal aValEvaled bVal)) (eqTm:
                    let retTy = E.vApp (E.vApp pVal bVal) (E.eval ctx.env eqTm); in
                    pure { term = T.mkBootJ aRaw aTm pTm prTm bTm eqTm; type = retTy; }))))))

      # U(k) infers as U(suc k) (§8.1). `k` is a Level-typed term;
      # the level argument is checked against `Level` before being
      # evaluated and lifted by `suc`. This lets both concrete
      # (`U(0)`) and polymorphic (`Π (k : Level). U(k)`) universes
      # share the same rule. The concrete `U(0)` fast-path skips the
      # `check`/`eval`/`vLevelSuc` pipeline — `level-zero` trivially
      # checks at `Level` and lifts to the cached `U(1)` type.
      else if t == "U" then
        if tm.level.tag == "level-zero"
        then pure { term = tm; type = vU1; }
        else bindP P.ULevel (self.check ctx tm.level V.vLevel) (lTm:
          let lVal = E.eval ctx.env lTm; in
          pure { term = T.mkU lTm; type = V.vU (V.vLevelSuc lVal); })

      # Level sort. `Level : U(0)`; zero/suc/max inhabit Level.
      # Definitional equality canonicalises via conv's Level normaliser.
      else if t == "level" then pure { term = T.mkLevel; type = vU0; }
      else if t == "level-zero" then
        pure { term = T.mkLevelZero; type = V.vLevel; }
      else if t == "level-suc" then
        bindP P.LevelSucPred (self.check ctx tm.pred V.vLevel) (pTm:
          pure { term = T.mkLevelSuc pTm; type = V.vLevel; })
      else if t == "level-max" then
        bindP P.LevelMaxLhs (self.check ctx tm.lhs V.vLevel) (lTm:
          bindP P.LevelMaxRhs (self.check ctx tm.rhs V.vLevel) (rTm:
            pure { term = T.mkLevelMax lTm rTm; type = V.vLevel; }))
      # Type formers infer at U(0)
      else if t == "unit" then pure { term = T.mkUnit; type = vU0; }
      # funext postulate. Type is the cached 5-layer closed Π chain
      # from term.nix, evaluated once at module initialisation.
      else if t == "funext" then
        pure { term = T.mkFunext; type = funextTypeVal; }
      else if t == "string" then pure { term = T.mkString; type = vU0; }
      else if t == "int" then pure { term = T.mkInt; type = vU0; }
      else if t == "float" then pure { term = T.mkFloat; type = vU0; }
      else if t == "attrs" then pure { term = T.mkAttrs; type = vU0; }
      else if t == "path" then pure { term = T.mkPath; type = vU0; }
      else if t == "function" then pure { term = T.mkFunction; type = vU0; }
      else if t == "any" then pure { term = T.mkAny; type = vU0; }
      # Lift l m eq A — `Lift l m eq A : U(m)`. The bound witness
      # `eq : Eq Level (max l m) m` proves `l ≤ m` decidably via
      # `convLevel`. `A : U(l)` is the underlying type. Eval collapses
      # `Lift l l _ A ≡ A` (idempotent at equal levels via the smart
      # constructor); the inferred type returned here threads through
      # `vLiftF` so the same collapse fires at infer time. Level-zero
      # fast-paths on `l` and `m` mirror the desc-arg shape.
      else if t == "lift" then
        let
          atLevels = lVal: mVal:
            bind (self.check ctx tm.A (V.vU lVal)) (aTm:
              bind (self.check ctx tm.eq
                (V.vBootEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
                pure { term = T.mkLift tm.l tm.m eqTm aTm;
                       type = V.vU mVal; }));
          withM = lVal:
            if tm.m.tag == "level-zero"
            then atLevels lVal V.vLevelZero
            else bind (self.check ctx tm.m V.vLevel) (mTm:
              atLevels lVal (E.eval ctx.env mTm));
        in
          if tm.l.tag == "level-zero"
          then withM V.vLevelZero
          else bind (self.check ctx tm.l V.vLevel) (lTm:
            withM (E.eval ctx.env lTm))

      # lift-intro l m eq A a — `lift l m eq A a : Lift l m eq A`.
      # Threads the inferred type through `vLiftF` so the idempotent
      # collapse at `l = m` fires (the inferred type becomes `A`,
      # matching eval's `vLiftIntroF` collapse to `a` at `convLevel
      # l m`). When `l ≠ m`, the type stays as a `VLift` cell.
      else if t == "lift-intro" then
        let
          atLevels = lVal: mVal:
            bind (self.check ctx tm.A (V.vU lVal)) (aTm:
              let aVal = E.eval ctx.env aTm; in
              bind (self.check ctx tm.eq
                (V.vBootEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
                let eqVal = E.eval ctx.env eqTm; in
                bind (self.check ctx tm.a aVal) (innerTm:
                  pure { term = T.mkLiftIntro tm.l tm.m eqTm aTm innerTm;
                         type = E.vLiftF lVal mVal eqVal aVal; })));
          withM = lVal:
            if tm.m.tag == "level-zero"
            then atLevels lVal V.vLevelZero
            else bind (self.check ctx tm.m V.vLevel) (mTm:
              atLevels lVal (E.eval ctx.env mTm));
        in
          if tm.l.tag == "level-zero"
          then withM V.vLevelZero
          else bind (self.check ctx tm.l V.vLevel) (lTm:
            withM (E.eval ctx.env lTm))

      # lift-elim l m eq A x — `lower l m eq A x : A`. Synthesises the
      # underlying type `A` directly (not `Lift l m eq A`); the eval-time
      # idempotent collapse of `Lift l l _ A ≡ A` makes this rule
      # transparent at `l = m` since the scrutinee was already at `A`.
      else if t == "lift-elim" then
        let
          atLevels = lVal: mVal:
            bind (self.check ctx tm.A (V.vU lVal)) (aTm:
              let aVal = E.eval ctx.env aTm; in
              bind (self.check ctx tm.eq
                (V.vBootEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
                let eqVal = E.eval ctx.env eqTm; in
                bind (self.check ctx tm.x (V.vLift lVal mVal eqVal aVal)) (xTm:
                  pure { term = T.mkLiftElim tm.l tm.m eqTm aTm xTm;
                         type = aVal; })));
          withM = lVal:
            if tm.m.tag == "level-zero"
            then atLevels lVal V.vLevelZero
            else bind (self.check ctx tm.m V.vLevel) (mTm:
              atLevels lVal (E.eval ctx.env mTm));
        in
          if tm.l.tag == "level-zero"
          then withM V.vLevelZero
          else bind (self.check ctx tm.l V.vLevel) (lTm:
            withM (E.eval ctx.env lTm))

      # desc^k I — takes a level k and index type I. `desc^k I : U(suc k)`.
      # Level-zero fast-path: when `tm.k` is the `level-zero` singleton
      # (the overwhelmingly common shape for prelude descriptions),
      # reuse the cached `vU1` and skip the eval/vU pipeline.
      else if t == "desc" then
        let
          atLevel = kVal:
            bind (self.check ctx tm.I vU0) (iTm:
              pure { term = T.mkDesc tm.k iTm;
                     type = if tm.k.tag == "level-zero"
                            then vU1
                            else V.vU (V.vLevelSuc kVal); });
        in
          if tm.k.tag == "level-zero"
          then atLevel V.vLevelZero
          else bind (self.check ctx tm.k V.vLevel) (kTm:
            atLevel (E.eval ctx.env kTm))

      # desc-con D i d — `con : μ D i` packing payload d at index i.
      # `bindP P.MuDesc` / `P.MuIndex` / `P.MuPayload` tag the three
      # sub-delegations; the terminal D-shape mismatch emits
      # `mkKernelError` with `position = P.MuDesc`.
      else if t == "desc-con" then
        bindP P.MuDesc (self.infer ctx tm.D) (dResult:
          let dTy = dResult.type; in
          if dTy.tag != "VDesc"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.MuDesc;
              rule     = "desc-con";
              msg      = "desc-con: D must have type Desc I";
              expected = { tag = "desc"; };
              got      = Q.quote ctx.depth dTy;
            };
          }
          else
            let iTyVal = dTy.I;
                dVal = E.eval ctx.env dResult.term;
            in bindP P.MuIndex (self.check ctx tm.i iTyVal) (iTm:
              let iVal = E.eval ctx.env iTm;
                  # X = λ(_i:I). μ I D _i as a VLam so interp can apply it.
                  muDFunc = V.vLam "_i" iTyVal (V.mkClosure [ dVal iTyVal ]
                    (T.mkMu (T.mkVar 2) (T.mkVar 1) (T.mkVar 0)));
                  interpTy = E.vInterpD dTy.level iTyVal dVal muDFunc iVal;
              in bindP P.MuPayload (self.check ctx tm.d interpTy) (dataTm:
                pure { term = T.mkDescCon dResult.term iTm dataTm;
                       type = V.vMu iTyVal dVal iVal; })))

      else if t == "desc-ind" then
        bindP P.MuDesc (self.infer ctx tm.D) (dResult:
          let dTy = dResult.type; in
          if dTy.tag != "VDesc"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.MuDesc;
              rule     = "desc-ind";
              msg      = "desc-ind: D must have type Desc I";
              expected = { tag = "desc"; };
              got      = Q.quote ctx.depth dTy;
            };
          }
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
            in bindP P.Motive (self.checkMotive ctx tm.motive chain) (pR:
              let
                pTm = pR.term;
                pVal = E.eval ctx.env pTm;
                # The motive's return universe rides through allTy as a
                # Level *value* — `mkAllMotive` and `allOnPlus` reference
                # it via the closure env, so polymorphic motive levels
                # (e.g. `λk. λA. λx. u k`, where `k` is a bound Level
                # variable) flow through verbatim without a Val→Int
                # coercion that would reject non-concrete levels.
                # The All-type for a `descArg L S T` summand inhabits
                # `U(max(L, K))` (the inner Π over S:U(L) lifts the
                # codomain universe). Using `pR.level` alone would
                # promise too low when `L > pR.level`. Threading
                # `max(dVal.level, pR.level)` keeps allTy's claimed
                # universe in step with what the case bodies actually
                # inhabit in iso-style assemblies. For prelude (`dVal.level`
                # is `VLevelZero`) the max collapses to `pR.level`,
                # so existing call sites are byte-identical.
                kEff =
                  if dTy.level.tag == "VLevelZero" then pR.level
                  else if pR.level.tag == "VLevelZero" then dTy.level
                  else V.vLevelMax dTy.level pR.level;
                # step : Π(i:I). Π(d : ⟦D⟧(μ D) i). All D P i d → P i (con i d)
                #
                # Uniform construction via kernel-primitive `mkInterpD` /
                # `mkAllD` Tms. The `vInterpDF` / `vAllDF` dispatchers
                # handle encoded VDescCon, stuck VNe, and primitive VDescX
                # shapes uniformly, so D's representation no longer drives
                # the build strategy.
                #
                # extEnv layout (innermost-first): 0:pVal, 1:dVal,
                # 2:iTyVal, 3:kEff, 4:dTy.level. ctx.env follows from 5.
                # Inside i-binder body: shift +1 → 0:i, 1:pVal, 2:dVal,
                # 3:iTyVal, 4:kEff, 5:dLev. Inside i+d body: shift +2.
                # Inside i+d+_ body: shift +3.
                stepTy =
                  let
                    extEnv = [ pVal dVal iTyVal kEff dTy.level ] ++ ctx.env;
                    # `λj:I. μ I D j` under the i-binder: j adds +1 to
                    # all extEnv refs, so iTyVal is at 4 and dVal at 3.
                    muFamForInterp = T.mkLam "_j"
                      (T.mkVar 3)
                      (T.mkMu (T.mkVar 4) (T.mkVar 3) (T.mkVar 0));
                    interpTyAtTm = T.mkInterpD
                      (T.mkVar 5)         # ℓ = dTy.level
                      (T.mkVar 3)         # I = iTyVal
                      (T.mkVar 2)         # D = dVal
                      muFamForInterp      # X = λj. μ I D j
                      (T.mkVar 0);        # i = i-binder
                    # `λj:I. μ I D j` under the i+d-binder: shift +2.
                    muFamForAll = T.mkLam "_j"
                      (T.mkVar 4)
                      (T.mkMu (T.mkVar 5) (T.mkVar 4) (T.mkVar 0));
                    allTyAtTm = T.mkAllD
                      (T.mkVar 6)         # ℓ = dTy.level
                      (T.mkVar 4)         # I = iTyVal
                      (T.mkVar 3)         # D = dVal
                      (T.mkVar 5)         # K = kEff
                      muFamForAll         # X = λj. μ I D j
                      (T.mkVar 2)         # M = pVal
                      (T.mkVar 1)         # i = i-binder
                      (T.mkVar 0);        # d = d-binder
                    retTyAtTm = T.mkApp
                      (T.mkApp (T.mkVar 3) (T.mkVar 2))
                      (T.mkDescCon (T.mkVar 4) (T.mkVar 2) (T.mkVar 1));
                  in V.vPi "i" iTyVal (V.mkClosure extEnv
                    (T.mkPi "d" interpTyAtTm
                      (T.mkPi "_" allTyAtTm retTyAtTm)));
              in bindP (P.Case "step") (self.check ctx tm.step stepTy) (stepTm:
                bindP P.MuIndex (self.check ctx tm.i iTyVal) (iTm:
                  let iVal = E.eval ctx.env iTm; in
                  bindP P.Scrut (self.check ctx tm.scrut (V.vMu iTyVal dVal iVal)) (xTm:
                    let retTy = E.vApp (E.vApp pVal iVal)
                                  (E.eval ctx.env xTm); in
                    pure { term = T.mkDescInd dTm pTm stepTm iTm xTm;
                           type = retTy; })))))

      # interpD ℓ I D X i : U(ℓ) — kernel-primitive interpretation of a
      # description (CDMM §4.2.3, Table 6.2). The Tm carries explicit
      # ℓ, I, D, X, i slots; the rule walks the Π-elim chain enforcing
      # `D : Desc^ℓ I` and `X : I → U(ℓ)` and synthesises `U(ℓ)`.
      # Reduction lives in `eval/desc.nix:vInterpDF`.
      else if t == "interp-d" then
        let
          ruleAt = lVal: lTm:
            bindP P.AnnType (self.check ctx tm.I vU0) (iTm:
              let iVal = E.eval ctx.env iTm; in
              bindP P.MuDesc (self.check ctx tm.D (V.vDesc lVal iVal)) (dTm:
                let
                  # X : I → U(ℓ). Closure env [lVal]; under the binder,
                  # the body reads lVal at index 1.
                  xTy = V.vPi "_" iVal (V.mkClosure [ lVal ]
                    (T.mkU (T.mkVar 1)));
                in bindP P.Motive (self.check ctx tm.X xTy) (xTm:
                  bindP P.MuIndex (self.check ctx tm.i iVal) (iIdxTm:
                    pure {
                      term = T.mkInterpD lTm iTm dTm xTm iIdxTm;
                      type = V.vU lVal;
                    }))));
        in
          if tm.level.tag == "level-zero"
          then ruleAt V.vLevelZero T.mkLevelZero
          else bindP P.DElimLevel (self.check ctx tm.level V.vLevel) (lTm:
            ruleAt (E.eval ctx.env lTm) lTm)

      # allD ℓ I D K X M i d : U(K) — kernel-primitive All-witness type
      # over a description (CDMM §6.1). The d-binder type is computed
      # via `E.vInterpD`, which routes through the kernel-primitive
      # dispatcher rather than the legacy HOAS-elaborated cascade.
      else if t == "all-d" then
        let
          ruleAt = lVal: lTm: kVal: kTm:
            bindP P.AnnType (self.check ctx tm.I vU0) (iTm:
              let iVal = E.eval ctx.env iTm; in
              bindP P.MuDesc (self.check ctx tm.D (V.vDesc lVal iVal)) (dTm:
                let
                  dVal = E.eval ctx.env dTm;
                  xTy = V.vPi "_" iVal (V.mkClosure [ lVal ]
                    (T.mkU (T.mkVar 1)));
                in bindP (P.Case "X") (self.check ctx tm.X xTy) (xTm:
                  let
                    xVal = E.eval ctx.env xTm;
                    # M : (i:I) → X i → U(K).
                    # Closure env [kVal, xVal].
                    # Under i (outer codomain): [i, kVal, xVal] —
                    #   xVal at idx 2, i at idx 0.
                    # Under x (inner body): [x, i, kVal, xVal] —
                    #   kVal at idx 2.
                    mTy = V.vPi "i" iVal (V.mkClosure [ kVal xVal ]
                      (T.mkPi "x"
                        (T.mkApp (T.mkVar 2) (T.mkVar 0))
                        (T.mkU (T.mkVar 2))));
                  in bindP P.Motive (self.check ctx tm.M mTy) (mTm:
                    bindP P.MuIndex (self.check ctx tm.i iVal) (iIdxTm:
                      let
                        iIdxVal = E.eval ctx.env iIdxTm;
                        interpTy = E.vInterpD lVal iVal dVal xVal iIdxVal;
                      in bindP P.Scrut (self.check ctx tm.d interpTy) (dDataTm:
                        pure {
                          term = T.mkAllD lTm iTm dTm kTm xTm mTm iIdxTm dDataTm;
                          type = V.vU kVal;
                        }))))));
          withK = lVal: lTm:
            if tm.K.tag == "level-zero"
            then ruleAt lVal lTm V.vLevelZero T.mkLevelZero
            else bindP P.DElimLevel (self.check ctx tm.K V.vLevel) (kTm:
              ruleAt lVal lTm (E.eval ctx.env kTm) kTm);
        in
          if tm.level.tag == "level-zero"
          then withK V.vLevelZero T.mkLevelZero
          else bindP P.DElimLevel (self.check ctx tm.level V.vLevel) (lTm:
            withK (E.eval ctx.env lTm) lTm)

      # everywhereD ℓ I D K X M ih i d : allD ℓ I D K X M i d — kernel-
      # primitive recursor producing an `allD` witness from a per-
      # recursive-position witness `ih : Π(j:I)(x:X j). M j x`.
      # Result type computed via `E.vAllD`, the kernel-primitive
      # dispatcher.
      else if t == "everywhere-d" then
        let
          ruleAt = lVal: lTm: kVal: kTm:
            bindP P.AnnType (self.check ctx tm.I vU0) (iTm:
              let iVal = E.eval ctx.env iTm; in
              bindP P.MuDesc (self.check ctx tm.D (V.vDesc lVal iVal)) (dTm:
                let
                  dVal = E.eval ctx.env dTm;
                  xTy = V.vPi "_" iVal (V.mkClosure [ lVal ]
                    (T.mkU (T.mkVar 1)));
                in bindP (P.Case "X") (self.check ctx tm.X xTy) (xTm:
                  let
                    xVal = E.eval ctx.env xTm;
                    mTy = V.vPi "i" iVal (V.mkClosure [ kVal xVal ]
                      (T.mkPi "x"
                        (T.mkApp (T.mkVar 2) (T.mkVar 0))
                        (T.mkU (T.mkVar 2))));
                  in bindP (P.Case "M") (self.check ctx tm.M mTy) (mTm:
                    let
                      mVal = E.eval ctx.env mTm;
                      # ih : Π(j:I)(x:X j). M j x.
                      # Closure env [xVal, mVal].
                      # Under j: [j, xVal, mVal] — xVal at idx 1, j at 0.
                      # Under x: [x, j, xVal, mVal] —
                      #   mVal at idx 3, j at 1, x at 0.
                      ihTy = V.vPi "j" iVal (V.mkClosure [ xVal mVal ]
                        (T.mkPi "x"
                          (T.mkApp (T.mkVar 1) (T.mkVar 0))
                          (T.mkApp (T.mkApp (T.mkVar 3) (T.mkVar 1)) (T.mkVar 0))));
                    in bindP (P.Case "ih") (self.check ctx tm.ih ihTy) (ihTm:
                      bindP P.MuIndex (self.check ctx tm.i iVal) (iIdxTm:
                        let
                          iIdxVal = E.eval ctx.env iIdxTm;
                          interpTy = E.vInterpD lVal iVal dVal xVal iIdxVal;
                        in bindP P.Scrut (self.check ctx tm.d interpTy) (dDataTm:
                          let
                            dDataVal = E.eval ctx.env dDataTm;
                            resultTy = E.vAllD lVal iVal dVal kVal xVal mVal iIdxVal dDataVal;
                          in pure {
                            term = T.mkEverywhereD lTm iTm dTm kTm xTm mTm ihTm iIdxTm dDataTm;
                            type = resultTy;
                          })))))));
          withK = lVal: lTm:
            if tm.K.tag == "level-zero"
            then ruleAt lVal lTm V.vLevelZero T.mkLevelZero
            else bindP P.DElimLevel (self.check ctx tm.K V.vLevel) (kTm:
              ruleAt lVal lTm (E.eval ctx.env kTm) kTm);
        in
          if tm.level.tag == "level-zero"
          then withK V.vLevelZero T.mkLevelZero
          else bindP P.DElimLevel (self.check ctx tm.level V.vLevel) (lTm:
            withK (E.eval ctx.env lTm) lTm)

      # descDescApp I L : Desc^(suc L) ⊤. The term evaluates through the
      # tagged canonical application; synthesis exposes the unfolded type
      # that description checkers consume directly.
      else if t == "desc-desc-app" then
        bindP P.AnnType (self.check ctx tm.I vU0) (iTm:
          bindP P.DElimLevel (self.check ctx tm.L V.vLevel) (lTm:
            let
              lVal = E.eval ctx.env lTm;
              ty = V.vDesc (V.vLevelSuc lVal) V.vUnit;
            in pure {
              term = T.mkDescDescApp iTm lTm;
              type = ty;
            }))

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
        bindP P.OpaqueType (self.checkType ctx tm.piTy) (piTyTm:
          let piTyVal = E.eval ctx.env piTyTm; in
          if piTyVal.tag != "VPi" then
            send "typeError" {
              error = D.mkKernelError {
                position = P.OpaqueType;
                rule     = "opaque-lam";
                msg      = "opaque-lam annotation must be Pi";
                expected = { tag = "pi"; };
                got      = Q.quote ctx.depth piTyVal;
              };
            }
          else pure { term = T.mkOpaqueLam tm._fnBox piTyTm; type = piTyVal; })

      # StrEq: both args must be String, result is Bool (plus-encoded).
      else if t == "str-eq" then
        bindP P.AppHead (self.check ctx tm.lhs V.vString) (lhsTm:
          bindP P.AppArg (self.check ctx tm.rhs V.vString) (rhsTm:
            pure { term = T.mkStrEq lhsTm rhsTm; type = boolTyVal; }))

      # `recTrunc A B f x : Squash B` for `f : A → Squash B`,
      # `x : Squash A`. The motive is restricted to `Squash _` by the
      # shape of `fTy` — any non-Squash codomain fails the check on `f`.
      # `bVal` is captured at extEnv index 0 so the closure body
      # references it via `Var 1` (post-arg-push).
      else if t == "squash-elim" then
        bind (self.checkType ctx tm.A) (aTm:
          bind (self.checkType ctx tm.B) (bTm:
            let
              aVal = E.eval ctx.env aTm;
              bVal = E.eval ctx.env bTm;
              extEnv = [ bVal ] ++ ctx.env;
              fTy = V.vPi "_" aVal
                      (V.mkClosure extEnv (T.mkSquash (T.mkVar 1)));
              xTy = V.vSquash aVal;
            in
            bind (self.check ctx tm.f fTy) (fTm:
              bind (self.check ctx tm.x xTy) (xTm:
                pure { term = T.mkSquashElim aTm bTm fTm xTm;
                       type = V.vSquash bVal; }))))

      else if t == "pi" || t == "sigma" || t == "list" || t == "boot-sum" || t == "boot-eq" || t == "mu" || t == "squash" then
        bind (self.checkTypeLevel ctx tm) (r:
          pure { term = r.term; type = V.vU r.level; })

      else send "typeError" {
        error = D.mkKernelError {
          rule     = "infer";
          msg      = "cannot infer type";
          expected = { tag = "unknown"; };
          got      = Q.quote ctx.depth vU0;
        };
      };
  };
  tests = {};
}
