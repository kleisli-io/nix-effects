# Checking mode (§7.4) and motive checking (§7.3).
#
# `check : Ctx → Tm → Val → Computation Tm` verifies that `tm` has type
# `ty` and returns an elaborated term. The dispatch handles introduction
# forms against their corresponding type formers (Lam/Pi, Pair/Sigma,
# Zero/Nat, etc.) and falls through to synthesis for anything not
# matched, using `conv` to compare the inferred type against the
# expected one (sub rule, with cumulativity for universes).
#
# `checkMotive` enforces that a motive has type `D_1 → … → D_n → U(k)`
# for some `k`, enabling large elimination. The domain chain is a
# `{ head : Val; tail : Val → Chain } | null` sequence so each layer
# may depend on the previous binder's value (required by `desc-ind`,
# whose motive is `(i:I) → μ D i → U(k)`). 1-argument callers use the
# `singleton` helper. Lambda motives extend the context with the
# current layer's domain and recurse; non-lambda motives infer a
# Π-chain matching the expected domains and validate the innermost
# codomain is a universe.
#
# The Succ and Cons branches trampoline over `builtins.genericClosure`
# to handle deep chains without stack pressure (§11.3). The `desc-con`
# branch peels homogeneous recursive-data chains along their single
# recursive position when the outer description is a plus-coproduct
# `A ⊕ B` with exactly one linear-recursive summand.
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
    # Build a 1-layer non-dependent domain chain from a single domain Val.
    singleton = dom: { head = dom; tail = _: null; };

    checkMotive = ctx: motTm: chain:
      if chain == null then
        # Innermost body: must inhabit some universe. `checkType` accepts
        # any universe level (via `checkTypeLevel`'s fallback), supporting
        # large elimination.
        self.checkType ctx motTm
      else if motTm.tag == "lam" then
        let
          dom = chain.head;
          ctx' = self.extend ctx motTm.name dom;
          # Fresh variable at the old depth is the level the just-bound
          # variable occupies in ctx'. Threading it into `chain.tail`
          # lets the next layer's domain reference the outer binder.
          freshV = V.freshVar ctx.depth;
          restChain = chain.tail freshV;
        in bind (self.checkMotive ctx' motTm.body restChain) (bodyTm:
          pure (T.mkLam motTm.name (Q.quote ctx.depth dom) bodyTm))
      else
        # Non-lambda motive: infer a Π-chain matching the expected
        # domains, then validate the innermost codomain is a universe.
        # `d` tracks the effective depth as successive Π-closures are
        # peeked — each fresh variable occupies a new level.
        bind (self.infer ctx motTm) (result:
          let
            go = rTy: ch: d:
              if ch == null then
                if rTy.tag == "VU"
                then pure result.term
                else typeError "eliminator motive must return a type"
                  { tag = "U"; } (Q.quote d rTy) motTm
              else if rTy.tag != "VPi"
              then typeError "eliminator motive must be a function"
                { tag = "pi"; } (Q.quote d rTy) motTm
              else if !(C.conv d rTy.domain ch.head)
              then typeError "eliminator motive domain mismatch"
                (Q.quote d ch.head) (Q.quote d rTy.domain) motTm
              else
                let
                  freshV = V.freshVar d;
                  codVal = E.instantiate rTy.closure freshV;
                in go codVal (ch.tail freshV) (d + 1);
          in go result.type chain ctx.depth);

    check = ctx: tm: ty:
      let t = tm.tag; in

      if t == "lam" && ty.tag == "VPi" then
        let
          dom = ty.domain;
          cod = E.instantiate ty.closure (V.freshVar ctx.depth);
          ctx' = self.extend ctx tm.name dom;
        in bind (self.check ctx' tm.body cod) (body':
          pure (T.mkLam tm.name (Q.quote ctx.depth dom) body'))

      else if t == "pair" && ty.tag == "VSigma" then
        let fstTy = ty.fst; in
        bind (self.check ctx tm.fst fstTy) (a':
          let bTy = E.instantiate ty.closure (E.eval ctx.env a'); in
          bind (self.check ctx tm.snd bTy) (b':
            pure (T.mkPair a' b')))

      else if t == "zero" && ty.tag == "VNat" then pure T.mkZero

      # Succ trampolined for large naturals (S^10000+): peel Succ layers,
      # check the base once, fold mkSucc back.
      else if t == "succ" && ty.tag == "VNat" then
        let
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "succ"
              then [{ key = item.key + 1; val = item.val.pred; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in bind (self.check ctx base V.vNat) (base':
          pure (builtins.foldl' (acc: _: T.mkSucc acc) base' (builtins.genList (x: x) n)))

      else if t == "true" && ty.tag == "VBool" then pure T.mkTrue
      else if t == "false" && ty.tag == "VBool" then pure T.mkFalse

      else if t == "nil" && ty.tag == "VList" then
        pure (T.mkNil (Q.quote ctx.depth ty.elem))

      # Cons trampolined for deep lists (5000+ elements).
      else if t == "cons" && ty.tag == "VList" then
        let
          elemTy = ty.elem;
          elemTm = Q.quote ctx.depth elemTy;
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; }];
            operator = item:
              if item.val.tag == "cons"
              then [{ key = item.key + 1; val = item.val.tail; }]
              else [];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
        in bind (self.check ctx base ty) (baseTm:
          builtins.foldl' (accComp: i:
            let node = (builtins.elemAt chain (n - 1 - i)).val; in
            bind accComp (acc:
              bind (self.check ctx node.head elemTy) (h':
                pure (T.mkCons elemTm h' acc)))
          ) (pure baseTm) (builtins.genList (x: x) n))

      else if t == "tt" && ty.tag == "VUnit" then pure T.mkTt

      else if t == "inl" && ty.tag == "VSum" then
        bind (self.check ctx tm.term ty.left) (v':
          pure (T.mkInl (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

      else if t == "inr" && ty.tag == "VSum" then
        bind (self.check ctx tm.term ty.right) (v':
          pure (T.mkInr (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

      # Refl checked against Eq — verify lhs ≡ rhs.
      else if t == "refl" && ty.tag == "VEq" then
        if C.conv ctx.depth ty.lhs ty.rhs
        then pure T.mkRefl
        else typeError "refl requires equal sides"
          (Q.quote ctx.depth ty.lhs) (Q.quote ctx.depth ty.rhs) tm

      else if t == "let" then
        bind (self.checkType ctx tm.type) (aTm:
          let aVal = E.eval ctx.env aTm; in
          bind (self.check ctx tm.val aVal) (tTm:
            let
              tVal = E.eval ctx.env tTm;
              ctx' = {
                env = [ tVal ] ++ ctx.env;
                types = [ aVal ] ++ ctx.types;
                depth = ctx.depth + 1;
              };
            in bind (self.check ctx' tm.body ty) (uTm:
              pure (T.mkLet tm.name aTm tTm uTm))))

      else if t == "string-lit" && ty.tag == "VString" then pure (T.mkStringLit tm.value)
      else if t == "int-lit" && ty.tag == "VInt" then pure (T.mkIntLit tm.value)
      else if t == "float-lit" && ty.tag == "VFloat" then pure (T.mkFloatLit tm.value)
      else if t == "attrs-lit" && ty.tag == "VAttrs" then pure T.mkAttrsLit
      else if t == "path-lit" && ty.tag == "VPath" then pure T.mkPathLit
      else if t == "fn-lit" && ty.tag == "VFunction" then pure T.mkFnLit
      else if t == "any-lit" && ty.tag == "VAny" then pure T.mkAnyLit

      # Opaque lambda checked against Pi: verify domain conv-equality.
      else if t == "opaque-lam" && ty.tag == "VPi" then
        bind (self.checkType ctx tm.piTy) (piTyTm:
          let piTyVal = E.eval ctx.env piTyTm; in
          if piTyVal.tag != "VPi" then
            typeError "opaque-lam annotation must be Pi"
              (Q.quote ctx.depth ty) (Q.quote ctx.depth piTyVal) tm
          else if !(C.conv ctx.depth piTyVal.domain ty.domain) then
            typeError "opaque-lam domain mismatch"
              (Q.quote ctx.depth ty.domain) (Q.quote ctx.depth piTyVal.domain) tm
          else pure (T.mkOpaqueLam tm._fnBox piTyTm))

      # desc-ret checked against Desc I — j must inhabit the index type.
      else if t == "desc-ret" && ty.tag == "VDesc" then
        bind (self.check ctx tm.j ty.I) (jTm:
          pure (T.mkDescRet jTm))

      # desc-arg checked against Desc I — S : U(0), then the body T is
      # a Desc I in the context extended by `_ : S` (T is the closure
      # body, not a lambda; the binding is materialised at eval time
      # via `mkClosure env tm.T`).
      else if t == "desc-arg" && ty.tag == "VDesc" then
        bind (self.check ctx tm.S (V.vU 0)) (sTm:
          let sVal = E.eval ctx.env sTm;
              ctx' = self.extend ctx "_" sVal;
          in bind (self.check ctx' tm.T (V.vDesc ty.I)) (tTm:
            pure (T.mkDescArg sTm tTm)))

      # desc-rec checked against Desc I — j : I picks the recursive
      # child's index, and the tail D : Desc I continues the description.
      else if t == "desc-rec" && ty.tag == "VDesc" then
        bind (self.check ctx tm.j ty.I) (jTm:
          bind (self.check ctx tm.D (V.vDesc ty.I)) (dTm:
            pure (T.mkDescRec jTm dTm)))

      # desc-pi checked against Desc I — S : U(0), f : S → I selects
      # the index per branch, and the tail D : Desc I continues. f's Pi
      # type is built with a non-dependent codomain quoting ty.I at the
      # closure-body depth.
      else if t == "desc-pi" && ty.tag == "VDesc" then
        bind (self.check ctx tm.S (V.vU 0)) (sTm:
          let sVal = E.eval ctx.env sTm;
              fTy = V.vPi "_" sVal (V.mkClosure ctx.env
                (Q.quote (ctx.depth + 1) ty.I));
          in bind (self.check ctx tm.f fTy) (fTm:
            bind (self.check ctx tm.D (V.vDesc ty.I)) (dTm:
              pure (T.mkDescPi sTm fTm dTm))))

      # desc-plus checked against Desc I — both summands share the same
      # index type. Mirrors the desc-ret/arg/rec/pi CHECK rules so that
      # `plus A B` is accepted by the bidirectional kernel whenever A or
      # B carries a check-only leaf (e.g. `retI tt` where `tt` has no
      # infer rule). Without this rule the check-mode path falls through
      # to subsumption + infer, and infer on `plus` recursively requires
      # `A` to be inferable, which fails for ret-only summands.
      else if t == "desc-plus" && ty.tag == "VDesc" then
        bind (self.check ctx tm.A (V.vDesc ty.I)) (aTm:
          bind (self.check ctx tm.B (V.vDesc ty.I)) (bTm:
            pure (T.mkDescPlus aTm bTm)))

      # desc-con checked against Mu — trampolined for deep recursive
      # data (5000+). Peels a homogeneous desc-con chain along its
      # single recursive position when D = plus A B with exactly one
      # of A, B linear-recursive (descArg-chain ending in
      # `descRec descRet`). Payload shape per layer is
      # `inl/inr lTy rTy (pair f_0 … (pair REC refl))` — n data fields,
      # the recursive tail, and a refl witness. lTy/rTy are invariant
      # across layers and captured from the first peel.
      #
      # Non-linear shapes (tree, mutual recursion, multi-recursive
      # ctors, non-plus D) fall through to per-layer checking.
      #
      # Each layer carries its own target index `i : I` via the 3-arg
      # `mkDescCon D i d`. The trampoline checks `layer.i : I` and
      # conv-matches against the expected index (ty.i at the top of
      # the chain, the rec position's `j` at successors). The payload
      # type at each layer is `interp I D μD layer.i`.
      else if t == "desc-con" && ty.tag == "VMu" then
        let iTyVal = ty.I;
        in bind (self.check ctx tm.D (V.vDesc iTyVal)) (dTm:
          let dVal = E.eval ctx.env dTm;
              muDFunc = V.vLam "_i" iTyVal (V.mkClosure [ dVal iTyVal ]
                (T.mkMu (T.mkVar 2) (T.mkVar 1) (T.mkVar 0)));
          in
          if !(C.conv ctx.depth dVal ty.D)
          then typeError "desc-con description mismatch"
            (Q.quote ctx.depth ty.D) (Q.quote ctx.depth dVal) tm
          else bind (self.check ctx tm.i iTyVal) (topITm:
            let topIVal = E.eval ctx.env topITm; in
            if !(C.conv ctx.depth topIVal ty.i)
            then typeError "desc-con target index mismatch"
              (Q.quote ctx.depth ty.i) (Q.quote ctx.depth topIVal) tm
            else
              let
                classify =
                  if ty.D.tag != "VDescPlus" then null
                  else
                    let pA = E.linearProfile ty.D.A;
                        pB = E.linearProfile ty.D.B;
                    in if pA != null && pB == null then { profile = pA; side = "inl"; }
                       else if pB != null && pA == null then { profile = pB; side = "inr"; }
                       else null;
                profile = if classify == null then [] else classify.profile;
                nFields = builtins.length profile;
                sameD = d2Tm:
                  if d2Tm == tm.D then true
                  else C.conv ctx.depth (E.eval ctx.env d2Tm) dVal;
                collectPairs = inner:
                  let
                    collect = k: p: acc:
                      if k == nFields then
                        if p.tag != "pair" then null
                        else if p.snd.tag != "refl" then null
                        else if p.fst.tag != "desc-con" then null
                        else { heads = acc; tail = p.fst; }
                      else
                        if p.tag != "pair" then null
                        else collect (k + 1) p.snd (acc ++ [p.fst]);
                  in collect 0 inner [];
                walkPayload = payload:
                  if classify == null then null
                  else if payload.tag != classify.side then null
                  else
                    let inner = collectPairs payload.term; in
                    if inner == null then null
                    else inner // { lTm = payload.left; rTm = payload.right; };
                peel = node:
                  if classify == null then null
                  else if node.tag != "desc-con" then null
                  else if !(sameD node.D) then null
                  else walkPayload node.d;
                chain = builtins.genericClosure {
                  startSet = [{ key = 0; val = tm; }];
                  operator = item:
                    let peeled = peel item.val; in
                    if peeled == null then []
                    else [{ key = item.key + 1; val = peeled.tail; }];
                };
                n = builtins.length chain - 1;
                base = (builtins.elemAt chain n).val;
                topPeel = if n >= 1 then peel tm else null;
                wrapPayload = innerTm:
                  if classify.side == "inl"
                  then T.mkInl topPeel.lTm topPeel.rTm innerTm
                  else T.mkInr topPeel.lTm topPeel.rTm innerTm;
              in bind (self.check ctx base.i iTyVal) (baseITm:
                let baseIVal = E.eval ctx.env baseITm;
                    interpTyBase = E.interp iTyVal ty.D muDFunc baseIVal;
                in bind (self.check ctx base.d interpTyBase) (baseDataTm:
                  let baseTm = T.mkDescCon dTm baseITm baseDataTm; in
                  builtins.foldl' (accComp: k:
                    let
                      layer = (builtins.elemAt chain (n - 1 - k)).val;
                      peeled = peel layer;
                      heads = peeled.heads;
                      checkHeads = remaining: accTms:
                        if remaining == [] then pure accTms
                        else
                          let
                            h = builtins.head remaining;
                            rest = builtins.tail remaining;
                          in bind (self.check ctx h.head h.S) (hTm:
                            checkHeads rest (accTms ++ [hTm]));
                      tasks = builtins.genList (j:
                        { head = builtins.elemAt heads j;
                          S = (builtins.elemAt profile j).S;
                        }) nFields;
                      buildInner = hTms: innerTail:
                        if hTms == [] then innerTail
                        else T.mkPair (builtins.head hTms)
                                      (buildInner (builtins.tail hTms) innerTail);
                    in bind accComp (acc:
                      bind (self.check ctx layer.i iTyVal) (layerITm:
                        bind (checkHeads tasks []) (hTms:
                          pure (T.mkDescCon dTm layerITm
                            (wrapPayload
                              (buildInner hTms (T.mkPair acc T.mkRefl)))))))
                  ) (pure baseTm) (builtins.genList (x: x) n)))))

      # Sub rule (§7.4): fall through to synthesis, with cumulativity
      # for universes (§8.3: VU(i) ≤ VU(j) when i ≤ j).
      else
        bind (self.infer ctx tm) (result:
          let inferredTy = result.type; in
          if inferredTy.tag == "VU" && ty.tag == "VU" && inferredTy.level <= ty.level
          then pure result.term
          else if C.conv ctx.depth inferredTy ty
          then pure result.term
          else typeError "type mismatch"
            (Q.quote ctx.depth ty) (Q.quote ctx.depth inferredTy) tm);
  };
  tests = {};
}
