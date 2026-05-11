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

  D = fx.diag.error;
  P = fx.diag.positions;

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

  # Idempotent `vLevelMax`: collapses to the non-zero operand when one
  # side is `VLevelZero`, avoiding a useless `vLevelMax X 0` /
  # `vLevelMax 0 X` wrapper. Mirrors the helper at
  # `check/type.nix`'s `vLevelMaxOpt`.
  vLevelMaxOpt = a: b:
    if a.tag == "VLevelZero" then b
    else if b.tag == "VLevelZero" then a
    else V.vLevelMax a b;

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
          then pure { term = T.mkAnnTrusted tm.term aTm; type = aVal; }
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

      else if t == "nat-elim" then
        bindP P.Motive (self.checkMotive ctx tm.motive (self.singleton V.vNat)) (pR:
          let pTm = pR.term;
              pVal = E.eval ctx.env pTm; in
          bindP (P.Case "zero") (self.check ctx tm.base (E.vApp pVal V.vZero)) (zTm:
            let
              # s : Π(k:Nat). P(k) → P(S(k))
              # Capture pVal in the closure env so the body Tms reference
              # it via Var instead of Q.quote — same mechanism as desc-elim
              # and sum-elim INFER. pVal can carry stuck VNe spines whose
              # eDescInd frames embed closures over outer-elim body envs;
              # quoting and re-embedding under ctx.env+N binders re-evaluates
              # `Var idx` against slots that aren't μ-elements, throwing
              # `vDescInd on non-mu`. extEnv layout (idx-from-0): 0:pVal.
              # ctx.env follows from idx 1.
              # Inside k-binder (shift +1): Var 0=k, Var 1=pVal.
              # Inside k+ih  (shift +2):    Var 0=ih, Var 1=k, Var 2=pVal.
              extEnv = [ pVal ] ++ ctx.env;
              stepTy = V.vPi "k" V.vNat (V.mkClosure extEnv
                (T.mkPi "ih" (T.mkApp (T.mkVar 1) (T.mkVar 0))
                  (T.mkApp (T.mkVar 2) (T.mkSucc (T.mkVar 1)))));
            in bindP (P.Case "succ") (self.check ctx tm.step stepTy) (sTm:
              bindP P.Scrut (self.check ctx tm.scrut V.vNat) (nTm:
                let retTy = E.vApp pVal (E.eval ctx.env nTm); in
                pure { term = T.mkNatElim pTm zTm sTm nTm; type = retTy; }))))

      else if t == "list-elim" then
        bind (self.checkType ctx tm.elem) (aRaw:
          let aVal = E.eval ctx.env aRaw;
          in bindP P.Motive (self.checkMotive ctx tm.motive (self.singleton (V.vList aVal))) (pR:
            let pTm = pR.term;
                pVal = E.eval ctx.env pTm; in
            bindP (P.Case "nil") (self.check ctx tm.nil (E.vApp pVal (V.vNil aVal))) (nTm:
              let
                # c : Π(h:A). Π(t:List A). P(t) → P(cons h t)
                # Capture pVal, aVal in the closure env so the body Tms
                # reference them via Var instead of Q.quote — same
                # mechanism as desc-elim and sum-elim INFER. pVal can
                # carry stuck VNe spines whose eDescInd frames embed
                # closures over outer-elim body envs; quoting and
                # re-embedding under ctx.env+N binders re-evaluates
                # `Var idx` against slots that aren't μ-elements,
                # throwing `vDescInd on non-mu`. extEnv layout
                # (idx-from-0): 0:pVal, 1:aVal. ctx.env follows from 2.
                # Inside h-binder (shift +1):  Var 0=h, Var 1=pVal, Var 2=aVal.
                # Inside h+t       (shift +2): Var 0=t, Var 1=h, Var 2=pVal, Var 3=aVal.
                # Inside h+t+ih    (shift +3): Var 0=ih, Var 1=t, Var 2=h, Var 3=pVal, Var 4=aVal.
                extEnv = [ pVal aVal ] ++ ctx.env;
                consTy = V.vPi "h" aVal (V.mkClosure extEnv
                  (T.mkPi "t" (T.mkList (T.mkVar 2))
                    (T.mkPi "ih" (T.mkApp (T.mkVar 2) (T.mkVar 0))
                      (T.mkApp (T.mkVar 3)
                        (T.mkCons (T.mkVar 4) (T.mkVar 2) (T.mkVar 1))))));
              in bindP (P.Case "cons") (self.check ctx tm.cons consTy) (cTm:
                bindP P.Scrut (self.check ctx tm.scrut (V.vList aVal)) (lTm:
                  let retTy = E.vApp pVal (E.eval ctx.env lTm); in
                  pure { term = T.mkListElim aRaw pTm nTm cTm lTm; type = retTy; })))))


      else if t == "sum-elim" then
        bind (self.checkType ctx tm.left) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bind (self.checkType ctx tm.right) (bRaw:
            let bVal = E.eval ctx.env bRaw;
            in bindP P.Motive (self.checkMotive ctx tm.motive (self.singleton (V.vSum aVal bVal))) (pR:
              let pTm = pR.term;
                  pVal = E.eval ctx.env pTm;
                  # Capture pVal, aVal, bVal in the closure env so the
                  # body Tms reference them by `Var` instead of `Q.quote`.
                  # `Q.quote pVal` would re-emit any stuck `VNe` spine
                  # frames as `Var idx` Tms whose semantics break under
                  # re-eval at a different env shape — same mechanism as
                  # in desc-elim INFER. extEnv layout (idx-from-0):
                  # 0:pVal, 1:aVal, 2:bVal. ctx.env follows from idx 3.
                  # Inside the x-binder body (depth+1):
                  # Var 1=pVal, Var 2=aVal, Var 3=bVal.
                  extEnv = [ pVal aVal bVal ] ++ ctx.env;
                  # l : Π(x:A). P(inl x)
                  lTy = V.vPi "x" aVal (V.mkClosure extEnv
                    (T.mkApp (T.mkVar 1)
                      (T.mkInl (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))));
                  # r : Π(y:B). P(inr y)
                  rTy = V.vPi "y" bVal (V.mkClosure extEnv
                    (T.mkApp (T.mkVar 1)
                      (T.mkInr (T.mkVar 2) (T.mkVar 3) (T.mkVar 0))));
              in bindP (P.Case "inl") (self.check ctx tm.onLeft lTy) (lTm:
                bindP (P.Case "inr") (self.check ctx tm.onRight rTy) (rTm:
                  bindP P.Scrut (self.check ctx tm.scrut (V.vSum aVal bVal)) (sTm:
                    let retTy = E.vApp pVal (E.eval ctx.env sTm); in
                    pure { term = T.mkSumElim aRaw bRaw pTm lTm rTm sTm; type = retTy; }))))))

      else if t == "j" then
        bindP P.JType (self.checkType ctx tm.type) (aRaw:
          let aVal = E.eval ctx.env aRaw; in
          bindP P.JLhs (self.check ctx tm.lhs aVal) (aTm:
            let aValEvaled = E.eval ctx.env aTm;
                # P : Π(y:A). Π(e:Eq(A,a,y)). U(k) for some k
                eqDomTy = depth: V.vEq aVal aValEvaled (V.freshVar depth);
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
              bindP (P.Case "base") (self.check ctx tm.base (E.vApp (E.vApp pVal aValEvaled) V.vRefl)) (prTm:
                bindP P.JRhs (self.check ctx tm.rhs aVal) (bTm:
                  let bVal = E.eval ctx.env bTm; in
                  bindP P.JEq (self.check ctx tm.eq (V.vEq aVal aValEvaled bVal)) (eqTm:
                    let retTy = E.vApp (E.vApp pVal bVal) (E.eval ctx.env eqTm); in
                    pure { term = T.mkJ aRaw aTm pTm prTm bTm eqTm; type = retTy; }))))))

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
      # `natToLevel n` infers as `Level` when `n : Nat`. Asymmetric
      # bridge per Decision #2 corollary — the kernel projects Nat to
      # Level for ergonomic level literals; no inverse rule exists.
      else if t == "nat-to-level" then
        bindP P.NatToLevelN (self.check ctx tm.n V.vNat) (nTm:
          pure { term = T.mkNatToLevel nTm; type = V.vLevel; })

      # Type formers infer at U(0)
      else if t == "nat" then pure { term = T.mkNat; type = vU0; }
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
                (V.vEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
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
                (V.vEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
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
                (V.vEq V.vLevel (V.vLevelMax lVal mVal) mVal)) (eqTm:
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

      # desc-ret j — `ret j : Desc I` where I is inferred from j's type.
      # `bindP P.DRetIndex` tags the index sub-delegation so a failure
      # deep in j's inference surfaces at the `ret.j` position.
      else if t == "desc-ret" then
        bindP P.DRetIndex (self.infer ctx tm.j) (jResult:
          pure { term = T.mkDescRet jResult.term; type = V.vDesc V.vLevelZero jResult.type; })

      # desc-arg (§2.4). Per-summand level discipline: `S : U(l)` where
      # `l` is the per-summand level and `k` is the description level;
      # the bound witness `eq : Eq Level (max l k) k` proves `l ≤ k`
      # decidably via `convLevel`. The body `T : S → Desc I` is inferred
      # to determine I; the resulting description level is
      # `max(k, level T)`, not `max(l, level T)` — `l` only governs S's
      # sort, not the Desc-result level.
      # Level-zero fast-paths on both `k` and `l`: the `level-zero`
      # singleton lets the rule skip the check/eval/vU pipeline,
      # recovering the allocation cost of the per-summand slots on the
      # prelude descriptions (all of which carry k=l=0).
      else if t == "desc-arg" then
        let
          sortAt = kVal: lVal:
            bindP P.DArgSort (self.check ctx tm.S (V.vU lVal)) (sTm:
              let sVal = E.eval ctx.env sTm;
                  ctx' = self.extend ctx "_" sVal;
              in bindP P.DArgBody (self.infer ctx' tm.T) (tResult:
                if tResult.type.tag != "VDesc"
                then send "typeError" {
                  error = D.mkKernelError {
                    position = P.DArgBody;
                    rule     = "desc-arg";
                    msg      = "desc-arg: body must have type Desc I";
                    expected = { tag = "desc"; };
                    got      = Q.quote ctx'.depth tResult.type;
                  };
                }
                else
                  bindP P.DArgEq
                    (self.check ctx tm.eq
                      (V.vEq V.vLevel (V.vLevelMax lVal kVal) kVal))
                    (eqTm:
                      pure { term = T.mkDescArg tm.k tm.l sTm eqTm tResult.term;
                             type = V.vDesc (vLevelMaxOpt kVal tResult.type.level) tResult.type.I; })));
          withL = kVal:
            if tm.l.tag == "level-zero"
            then sortAt kVal V.vLevelZero
            else bindP P.DArgSort (self.check ctx tm.l V.vLevel) (lTm:
              sortAt kVal (E.eval ctx.env lTm));
        in
          if tm.k.tag == "level-zero"
          then withL V.vLevelZero
          else bindP P.DArgLevel (self.check ctx tm.k V.vLevel) (kTm:
            withL (E.eval ctx.env kTm))

      # desc-rec j D — `rec j D : Desc^L I` where L = level(D). Infer
      # j's type to get I, then route the tail D through
      # `checkDescAtAnyLevel`: canonical sub-descriptions (the prelude's
      # common shape) CHECK at the level-zero soundness anchor and read
      # their level via `levelOf`; non-canonical D (a level-polymorphic
      # variable, an applied `descDesc k`, …) INFER and use the
      # inferred `VDesc.level` directly. `bindP P.DRecIndex` /
      # `P.DRecTail` tag the descent coordinates.
      else if t == "desc-rec" then
        bindP P.DRecIndex (self.infer ctx tm.j) (jResult:
          let iVal = jResult.type; in
          bindP P.DRecTail (self.checkDescAtAnyLevel ctx tm.D iVal) (dInfo:
            pure { term = T.mkDescRec jResult.term dInfo.term;
                   type = V.vDesc dInfo.level iVal; }))

      # desc-pi k l S eq f D — `pi k l S eq f D : Desc^k I` where
      # f : S → I determines I and the bound witness
      # `eq : Eq Level (max l k) k` proves `l ≤ k`. Per-summand
      # `S : U(l)`; the Desc-result level remains `max(k, level D)`.
      # Five sub-delegations each carry their own descent coordinate:
      # `DPiLevel` for the description-level argument, `DPiSort` for
      # the per-summand domain sort, `DPiEq` for the bound witness,
      # `DPiFn` for the index selector, `DPiBody` for the tail
      # description. Level-zero fast-paths on both `k` and `l` mirror
      # the desc-arg case.
      else if t == "desc-pi" then
        let
          sortAt = kVal: lVal:
            bindP P.DPiSort (self.check ctx tm.S (V.vU lVal)) (sTm:
              let sVal = E.eval ctx.env sTm;
              in bindP P.DPiFn (self.infer ctx tm.f) (fResult:
                let fTy = fResult.type; in
                if fTy.tag != "VPi"
                then send "typeError" {
                  error = D.mkKernelError {
                    position = P.DPiFn;
                    rule     = "desc-pi";
                    msg      = "desc-pi: f must have type S → I";
                    expected = { tag = "pi"; };
                    got      = Q.quote ctx.depth fTy;
                  };
                }
                else if !(C.conv ctx.depth fTy.domain sVal)
                then send "typeError" {
                  error = D.mkKernelError {
                    position = P.DPiFn;
                    rule     = "desc-pi";
                    msg      = "desc-pi: f domain does not match S";
                    expected = Q.quote ctx.depth sVal;
                    got      = Q.quote ctx.depth fTy.domain;
                  };
                }
                else
                  # I = codomain (non-dependent on s per the Desc grammar).
                  # Result level: `max(k, level(D))`. The tail D
                  # routes through `checkDescAtAnyLevel`: canonical
                  # sub-descriptions CHECK at level-zero with `levelOf`
                  # recovery; non-canonical D INFER directly.
                  let iVal = E.instantiate fTy.closure (V.freshVar ctx.depth);
                  in bindP P.DPiBody (self.checkDescAtAnyLevel ctx tm.D iVal) (dInfo:
                    bindP P.DPiEq
                      (self.check ctx tm.eq
                        (V.vEq V.vLevel (V.vLevelMax lVal kVal) kVal))
                      (eqTm:
                        pure { term = T.mkDescPi tm.k tm.l sTm eqTm fResult.term dInfo.term;
                               type = V.vDesc (vLevelMaxOpt kVal dInfo.level) iVal; }))));
          withL = kVal:
            if tm.l.tag == "level-zero"
            then sortAt kVal V.vLevelZero
            else bindP P.DPiSort (self.check ctx tm.l V.vLevel) (lTm:
              sortAt kVal (E.eval ctx.env lTm));
        in
          if tm.k.tag == "level-zero"
          then withL V.vLevelZero
          else bindP P.DPiLevel (self.check ctx tm.k V.vLevel) (kTm:
            withL (E.eval ctx.env kTm))

      # desc-plus A B — `plus A B : Desc^L I` where L = max(level A,
      # level B). Infer A to determine I (and read its level), then
      # route B through `checkDescAtAnyLevel`: canonical summands
      # CHECK at level-zero with `levelOf` recovery; non-canonical B
      # INFER and contribute its inferred level directly. Both
      # summands share an index type. `bindP P.DPlusL` / `P.DPlusR`
      # tag the descent coordinates; a non-VDesc inferred type for A
      # emits `mkKernelError` with `position = P.DPlusL`.
      else if t == "desc-plus" then
        bindP P.DPlusL (self.infer ctx tm.A) (aResult:
          let aTy = aResult.type; in
          if aTy.tag != "VDesc"
          then send "typeError" {
            error = D.mkKernelError {
              position = P.DPlusL;
              rule     = "desc-plus";
              msg      = "desc-plus: A must have type Desc I";
              expected = { tag = "desc"; };
              got      = Q.quote ctx.depth aTy;
            };
          }
          else
            let iVal = aTy.I;
                aLev = aTy.level; in
            bindP P.DPlusR (self.checkDescAtAnyLevel ctx tm.B iVal) (bInfo:
              pure { term = T.mkDescPlus aResult.term bInfo.term;
                     type = V.vDesc (vLevelMaxOpt aLev bInfo.level) iVal; }))

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

      else if t == "desc-elim" then
        # I is recovered from the scrutinee's inferred type (Desc I),
        # not the motive's — the motive may be a bare lam (as built by
        # interpHoasAt / allHoasAt in hoas/desc.nix), for which synthesis has
        # no rule. checkMotive accepts bare lams by descending under the
        # known domain, and preserves large elim (motive body may return
        # any universe level). The leading `k` slot is the universe at
        # which `onArg` / `onPi` bind their sort `S`; the
        # `convLevel kVal sTy.level` check below enforces that `k`
        # equals the scrutinee's description level, matching the
        # homogeneous-L invariant established by `desc-arg` / `desc-pi`
        # CHECK. With this in place the reconstructed scrutinee Tms
        # (`paTy` / `ppTy`'s `descArg kTm` / `descPi kTm`) sit at the
        # same level as the scrutinee, so the case bodies' static
        # return type matches `motive scrut`. Level-zero fast-path
        # mirrors the desc-arg / desc-pi rules.
        let
          ruleAt = kVal: kTm:
            bindP P.Scrut (self.infer ctx tm.scrut) (sResult:
              let sTy = sResult.type; in
              if sTy.tag != "VDesc"
              then send "typeError" {
                error = D.mkKernelError {
                  position = P.Scrut;
                  rule     = "desc-elim";
                  msg      = "desc-elim: scrutinee must have type Desc I";
                  expected = { tag = "desc"; };
                  got      = Q.quote ctx.depth sTy;
                };
              }
              else if !(C.convLevel kVal sTy.level)
              then send "typeError" {
                error = D.mkKernelError {
                  position = P.DElimLevel;
                  rule     = "desc-elim";
                  msg      = "desc-elim: K must equal scrutinee description level";
                  expected = Q.quote ctx.depth sTy.level;
                  got      = Q.quote ctx.depth kVal;
                };
              }
              else
                let
                  iTyVal = sTy.I;
                in bindP P.Motive (self.checkMotive ctx tm.motive (self.singleton (V.vDesc sTy.level iTyVal))) (pR:
                  let
                    pTm = pR.term;
                    pVal = E.eval ctx.env pTm;
                    # Capture pVal, iTyVal, sTy.level, kVal in the closure
                    # env so the per-summand type bodies reference them via
                    # `Var` rather than `Q.quote`. pVal can carry stuck
                    # `VNe` spines with `eDescInd` frames whose stored
                    # closures embed `encodeDescElim`'s body env; quoting
                    # such values at depth `ctx.depth+N` and embedding the
                    # Tm under a closure with `ctx.env` (size `ctx.depth`)
                    # plus N binders re-evaluates `Var idx` against env
                    # slots whose values are not the μ-elements
                    # `vDescIndF` requires — re-eval throws
                    # `vDescInd on non-mu`. Capturing as env entries makes
                    # the Var refs resolve to the exact Vals at re-eval
                    # time. iTyVal/sTy.level/kVal are captured for the
                    # same reason: any of them may carry free vars from
                    # ctx.env that mid-body Q.quote translations would
                    # mis-index after re-eval under shifted envs.
                    extEnv = [ pVal iTyVal sTy.level kVal ] ++ ctx.env;
                    # extEnv layout (idx-from-0): 0:pVal, 1:iTyVal,
                    # 2:sTy.level, 3:kVal. ctx.env follows from idx 4.
                    # Inside N binders: Var(N+0)=pVal, Var(N+1)=iTyVal,
                    # Var(N+2)=sTy.level, Var(N+3)=kVal.
                    # pr : Π(j:I). P (ret j)
                    prTy = V.vPi "j" iTyVal (V.mkClosure extEnv
                      (T.mkApp (T.mkVar 1) (T.mkDescRet (T.mkVar 0))));
                    # pa : Π(S:U(k)). Π(T:S→Desc^L I). (Π(s:S). P (T s)) → P (arg k S T)
                    paTy = V.vPi "S" (V.vU kVal) (V.mkClosure extEnv
                      (T.mkPi "T" (T.mkPi "_" (T.mkVar 0) (T.mkDesc (T.mkVar 4) (T.mkVar 3)))
                        (T.mkPi "ih" (T.mkPi "s" (T.mkVar 1)
                            (T.mkApp (T.mkVar 3) (T.mkApp (T.mkVar 1) (T.mkVar 0))))
                          (T.mkApp (T.mkVar 3)
                            (T.mkDescArg (T.mkVar 6) (T.mkVar 6) (T.mkVar 2) T.mkRefl
                              (T.mkApp (T.mkVar 2) (T.mkVar 0)))))));
                    # pe : Π(j:I). Π(D:Desc^L I). P D → P (rec j D)
                    peTy = V.vPi "j" iTyVal (V.mkClosure extEnv
                      (T.mkPi "D" (T.mkDesc (T.mkVar 3) (T.mkVar 2))
                        (T.mkPi "ih" (T.mkApp (T.mkVar 2) (T.mkVar 0))
                          (T.mkApp (T.mkVar 3) (T.mkDescRec (T.mkVar 2) (T.mkVar 1))))));
                    # pp : Π(S:U(k)). Π(f:S→I). Π(D:Desc^L I). P D → P (pi k S f D)
                    ppTy = V.vPi "S" (V.vU kVal) (V.mkClosure extEnv
                      (T.mkPi "f" (T.mkPi "_" (T.mkVar 0) (T.mkVar 3))
                        (T.mkPi "D" (T.mkDesc (T.mkVar 4) (T.mkVar 3))
                          (T.mkPi "ih" (T.mkApp (T.mkVar 3) (T.mkVar 0))
                            (T.mkApp (T.mkVar 4)
                              (T.mkDescPi (T.mkVar 7) (T.mkVar 7) (T.mkVar 3) T.mkRefl
                                (T.mkVar 2) (T.mkVar 1)))))));
                      # pq : Π(A:Desc^L I). Π(B:Desc^L I). P A → P B → P (plus A B)
                    pqTy = V.vPi "A" (V.vDesc sTy.level iTyVal) (V.mkClosure extEnv
                      (T.mkPi "B" (T.mkDesc (T.mkVar 3) (T.mkVar 2))
                        (T.mkPi "ihA" (T.mkApp (T.mkVar 2) (T.mkVar 1))
                          (T.mkPi "ihB" (T.mkApp (T.mkVar 3) (T.mkVar 1))
                            (T.mkApp (T.mkVar 4) (T.mkDescPlus (T.mkVar 3) (T.mkVar 2)))))));
                in bindP (P.Case "onRet") (self.check ctx tm.onRet prTy) (prTm:
                    bindP (P.Case "onArg") (self.check ctx tm.onArg paTy) (paTm:
                      bindP (P.Case "onRec") (self.check ctx tm.onRec peTy) (peTm:
                        bindP (P.Case "onPi") (self.check ctx tm.onPi ppTy) (ppTm:
                          bindP (P.Case "onPlus") (self.check ctx tm.onPlus pqTy) (pqTm:
                            let scrutVal = E.eval ctx.env sResult.term;
                                retTy = E.vApp pVal scrutVal;
                                L_q0 = Q.quote ctx.depth sTy.level;
                                # Primitive-vs-encoded dispatch happens at
                                # eval time inside `vDescElimF`: VDescRet/
                                # Arg/Rec/Pi/Plus walk the primitive
                                # 5-summand cascade; VDescCon (encoded
                                # μ⊤(descDesc) form) routes through
                                # `encodeDescElimVal`; VNe (stuck) emits
                                # a stuck spine `vNe + [eDescElim ...]`
                                # per canonical evaluator semantics.
                                # The typing rule emits one uniform Tm
                                # regardless of the scrut's typing-time
                                # shape — the runtime value is what
                                # determines the elim semantics, so
                                # deferring dispatch eliminates the
                                # typing-time / runtime mismatch that
                                # static dispatch on inferred `scrutVal`
                                # cannot resolve (a HOAS-bound var stuck
                                # at typing time can substitute to either
                                # representation at use site).
                            in
                            pure {
                              term = T.mkDescElim L_q0 pTm prTm paTm peTm ppTm pqTm sResult.term;
                              type = retTy;
                            })))))));
        in
          if tm.k.tag == "level-zero"
          then ruleAt V.vLevelZero T.mkLevelZero
          else bindP P.DElimLevel (self.check ctx tm.k V.vLevel) (kTm:
            ruleAt (E.eval ctx.env kTm) kTm)

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
                # inhabit, and matches HOAS allHoasAt's `K` parameter
                # in iso-style assemblies. For prelude (`dVal.level`
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
            let boolVal = V.vMu V.vUnit (V.vDescPlus (V.vDescRet V.vTt) (V.vDescRet V.vTt)) V.vTt;
            in pure { term = T.mkStrEq lhsTm rhsTm; type = boolVal; }))

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

      else if t == "pi" || t == "sigma" || t == "list" || t == "sum" || t == "eq" || t == "mu" || t == "squash" then
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
