# Checking mode (§7.4) and motive checking (§7.3).
#
# `check : Ctx → Tm → Val → Computation Tm` verifies that `tm` has type
# `ty` and returns an elaborated term. The dispatch handles introduction
# forms against their corresponding type formers (Lam/Pi, Pair/Sigma,
# Unit, Sum, Desc/Mu, etc.) and falls through to synthesis for anything not
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
# The `desc-con` branch peels homogeneous recursive-data chains along
# their single recursive position when the outer description is a
# plus-coproduct `A ⊕ B` with exactly one linear-recursive summand.
{ self, fx, api, ... }:

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

  evalDescRef = env: ref:
    let
      base = ref // {
        I = E.eval env ref.I;
        level = E.eval env ref.level;
        params = map (E.eval env) (ref.params or [ ]);
      };
    in
    if ref ? branchDescs
    then base // { branchDescs = map (E.eval env) ref.branchDescs; }
    else base;

  listConv = depth: xs: ys:
    builtins.length xs == builtins.length ys
    && builtins.foldl'
      (ok: i: ok && C.conv depth (builtins.elemAt xs i) (builtins.elemAt ys i))
      true
      (builtins.genList (i: i) (builtins.length xs));

  sameSyntax = a: b:
    let r = builtins.tryEval (a == b); in
    r.success && r.value;

  descRefConv = depth: r1: r2:
    let
      kind = r1.kind or null;
      signatureConv =
        if kind == "datatype-desc"
        then (r1 ? signature) && (r2 ? signature)
          && (r1.signature.complete or false)
          && (r2.signature.complete or false)
          && r1.signature == r2.signature
        else true;
    in
    kind == (r2.kind or null)
    && (r1.name or null) == (r2.name or null)
    && (r1.arity or null) == (r2.arity or null)
    && (r1.indexed or null) == (r2.indexed or null)
    && (r1.constructors or [ ]) == (r2.constructors or [ ])
    && C.conv depth r1.I r2.I
    && C.conv depth r1.level r2.level
    && listConv depth (r1.params or [ ]) (r2.params or [ ])
    && signatureConv;

  # Hoist fixpoint-resolved rule-body combinators out of the rule
  # dispatch. Each `self.X` is an attribute lookup on the kernel
  # fixpoint; binding once at module init collapses each use site to a
  # plain variable reference, eliminating the repeated lookup in deep
  # rule-descent loops.
  bindPR = self.bindPR;
  bindPChain = self.bindPChain;
  yield = self._yield.wrap;

in
{
  scope = {
    singleton = api.leaf {
      description = "singleton: build a one-element motive chain — `{ head = dom; tail = _: null; }` — the trivial telescope used by `checkMotive` call sites with a single domain and no nested binder dependency.";
      signature = "singleton : Val -> Chain";
      doc = ''
        The motive chain consumed by `checkMotive` is a nested
        `{ head : Val; tail : Val → Chain } | null` structure so each
        layer's domain may depend on prior binder values. Most
        eliminator sites (Sum, Eq, Squash) have only one motive
        argument and no inter-binder dependency; `singleton dom` packs
        that into the chain shape with a constant `tail` that ignores
        its argument and returns `null` — closing the chain after a
        single layer.
      '';
      value = dom: { head = dom; tail = _: null; };
    };

    checkMotive = api.leaf {
      description = "checkMotive: eliminator-motive validation — walks the lambda layers of a motive against an expected domain chain `D_1 → … → D_n → U(k)` and returns the elaborated motive term together with the universe level `k` of its codomain.";
      signature = "checkMotive : Ctx -> Tm -> Chain -> Comp { term; level }";
      doc = ''
        The domain chain is a `{ head : Val; tail : Val → Chain } | null`
        sequence so each layer's domain may depend on the previously-bound
        value (required by `desc-ind`, whose motive is
        `(i : I) → μ D i → U(k)`). 1-argument call sites use the
        `singleton` helper to build a one-element chain.

        - Lambda motive: extend the context with the current layer's
          domain, recurse into the body with `chain.tail freshV`, and
          wrap the result in `T.mkLam`. The level threads up unchanged
          through each lam wrapper so the innermost codomain's universe
          flows back to eliminators that care about it (e.g., `desc-ind`'s
          `allTy`).
        - Non-lambda motive: fall through to `infer`, then walk the
          inferred Π-chain in lock-step with the expected `chain`,
          conv-checking each domain and instantiating each codomain
          through a fresh variable. The innermost codomain must be a
          universe; its level is the motive's level.

        Failure modes emit `D.mkKernelError` under the `P.Motive` position
        for the diagnostic renderer. Cross-ref: `singleton` for the
        unary-chain helper, `infer` for the synthesis fallback,
        `checkTypeLevel` for the innermost-universe leaf.
      '';
      value = ctx: motTm: chain:
        # Always-yield: cold path, self-recursive; head defer keeps the
        # motive descent off the host stack.
        yield (
        if chain == null then
        # Innermost body: must inhabit some universe — delegate to
        # `checkTypeLevel` which accepts any universe level and carries
        # the level back out. The level threads up through the lam
        # wrappers so eliminators that care about the motive's return
        # universe (desc-ind's allTy) can read it off the result.
          self.checkTypeLevel ctx motTm
        else if motTm.tag == "lam" then
          let
            dom = chain.head;
            ctx' = self.extend ctx motTm.name dom;
            # Fresh variable at the old depth is the level the just-bound
            # variable occupies in ctx'. Threading it into `chain.tail`
            # lets the next layer's domain reference the outer binder.
            freshV = V.freshVar ctx.depth;
            restChain = chain.tail freshV;
          in
          bind (self.checkMotive ctx' motTm.body restChain) (body:
            pure {
              term = T.mkLam motTm.name (Q.quote ctx.depth dom) body.term;
              level = body.level;
            })
        else
        # Non-lambda motive: infer a Π-chain matching the expected
        # domains, then validate the innermost codomain is a universe.
        # `d` tracks the effective depth as successive Π-closures are
        # peeked — each fresh variable occupies a new level.
          bind (self.infer ctx motTm) (result:
            let
              motiveErr = msg: expected: got:
                send "typeError" {
                  error = D.mkKernelError {
                    position = P.Motive;
                    rule = "checkMotive";
                    inherit msg expected got;
                    term = { tag = motTm.tag; };
                    frame = D.captureFrame ctx;
                  };
                };
              go = rTy: ch: d:
                if ch == null then
                  if rTy.tag == "VU"
                  then pure { term = result.term; level = rTy.level; }
                  else
                    motiveErr "eliminator motive must return a type"
                      { tag = "U"; }
                      (Q.quote d rTy)
                else if rTy.tag != "VPi"
                then
                  motiveErr "eliminator motive must be a function"
                    { tag = "pi"; }
                    (Q.quote d rTy)
                else if !(C.conv d rTy.domain ch.head)
                then
                  motiveErr "eliminator motive domain mismatch"
                    (Q.quote d ch.head)
                    (Q.quote d rTy.domain)
                else
                  let
                    freshV = V.freshVar d;
                    codVal = E.instantiate rTy.closure freshV;
                  in
                  go codVal (ch.tail freshV) (d + 1);
            in
            go result.type chain ctx.depth));
    };

    check = api.leaf {
      description = "check: bidirectional checking-mode entry — verify `tm : ty` and return the elaborated kernel term; dispatches intro-form rules against their type-formers and falls through to synthesis plus structural conversion.";
      signature = "check : Ctx -> Tm -> Val -> Comp Tm";
      doc = ''
        Dispatches intro forms against their corresponding type formers:
        `lam` vs `VPi`, `pair` vs `VSigma`, `tt` vs `VUnit`,
        `boot-inl`/`boot-inr` vs `VBootSum`, `boot-refl` vs `VBootEq`,
        `squash-intro` vs `VSquash`, `string-lit`/`int-lit`/... vs
        their primitive value types, and the trampolined `desc-con` vs
        `VMu`. Anything not matched falls through to `infer` plus a
        structural `C.conv` round-trip — the sole CHECK-to-INFER bridge
        in the bidirectional rules.

        The kernel is Tarski-style and non-cumulative: a term checked
        against `U(k)` must have inferred type exactly `U(k)` modulo
        `convLevel`. No universe-cumulativity coercion fires here.
        Per-summand level mixing in `desc-arg` / `desc-pi` is handled
        through the bound-witness slot at synthesis time.

        The `desc-con` branch is trampolined for deep recursive data
        (5000+ layers): it peels homogeneous linear-recursive chains
        along a single recursive position when the description is a
        plus-coproduct `A + B` with exactly one linear-recursive
        summand. Non-linear shapes (tree, mutual recursion, multiple
        recursive constructors, non-plus `D`) fall through to per-layer
        checking via the degenerate `n = 0` branch. Constructor
        certificates (`_descConCert`) accelerate the non-recursive case
        by skipping the chain walk entirely.

        Failure modes emit `D.mkKernelError` via the `typeError` effect;
        positions and rule keys identify the failure site for the
        diagnostic renderer. Cross-ref: `infer` for the synthesis side,
        `checkMotive` for eliminator motive validation.
      '';
      value = ctx: tm: ty0:
        let
          t = tm.tag;
          # Leaf tags: arm is `pure …` with no recursion. Left un-yielded
          # so they stay Pure and the bindP `isPure` fast path fires. A
          # mistagged recursive arm only over-forces — caught loudly by the
          # depth probe, never silent.
          isLeaf = builtins.elem t [
            "tt" "lit-val" "string-lit" "int-lit" "float-lit"
            "attrs-lit" "path-lit" "derivation-lit" "fn-lit" "any-lit"
          ];
          body =
            let ty = E.forceVal ty0; in
            if t == "lam" && ty.tag == "VPi" then
          let
            dom = ty.domain;
            cod = E.instantiate ty.closure (V.freshVar ctx.depth);
            ctx' = self.extend ctx tm.name dom;
          in
          bindPR P.LamBody "lam" (self.check ctx' tm.body cod) (body':
            pure (T.mkLam tm.name (Q.quote ctx.depth dom) body'))

        else if t == "pair" && ty.tag == "VSigma" then
          let fstTy = ty.fst; in
          bindPR P.SigmaFst "pair" (self.check ctx tm.fst fstTy) (a':
            let bTy = E.instantiate ty.closure (E.eval ctx.env a'); in
            bindPR P.SigmaSnd "pair" (self.check ctx tm.snd bTy) (b':
              pure (T.mkPair a' b')))

        else if t == "tt" && ty.tag == "VUnit" then pure T.mkTt

        else if t == "boot-inl" && ty.tag == "VBootSum" then
          bindPR P.DPlusL "boot-inl" (self.check ctx tm.term ty.left)
            (v':
              pure (T.mkBootInl (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

        else if t == "boot-inr" && ty.tag == "VBootSum" then
          bindPR P.DPlusR "boot-inr" (self.check ctx tm.term ty.right)
            (v':
              pure (T.mkBootInr (Q.quote ctx.depth ty.left) (Q.quote ctx.depth ty.right) v'))

        # Refl checked against Eq — verify lhs ≡ rhs.
        else if t == "boot-refl" && ty.tag == "VBootEq" then
          if ty.lhs.tag == "VTt" && ty.rhs.tag == "VTt"
          then pure T.mkBootRefl
          else if C.conv ctx.depth ty.lhs ty.rhs
          then pure T.mkBootRefl
          else
            send "typeError" {
              error = D.mkKernelError {
                rule = "refl";
                msg = "refl requires equal sides";
                expected = Q.quote ctx.depth ty.lhs;
                got = Q.quote ctx.depth ty.rhs;
                term = { tag = tm.tag; };
                frame = D.captureFrame ctx;
              };
            }

        # Squash intro: `squashIntro a : Squash A` requires `a : A`.
        # Conv handles definitional irrelevance among inhabitants.
        else if t == "squash-intro" && ty.tag == "VSquash" then
          bindPR P.AnnTerm "squash-intro" (self.check ctx tm.a ty.A)
            (aTm:
              pure (T.mkSquashIntro aTm))

        else if t == "let" then
          bindPR P.AnnType "let" (self.checkType ctx tm.type)
            (aTm:
              let aVal = E.eval ctx.env aTm; in
              bindPR P.AnnTerm "let" (self.check ctx tm.val aVal) (tTm:
                let
                  tVal = E.eval ctx.env tTm;
                  tyF = E.forceVal ty;
                  ctx' = {
                    env = V.envCons tVal ctx.env;
                    types = [ aVal ] ++ ctx.types;
                    depth = ctx.depth + 1;
                  };
                in
                builtins.seq tyF
                  (bindPR P.LetBody "let" (self.check ctx' tm.body tyF) (uTm:
                    pure (T.mkLet tm.name aTm tTm uTm)))))

        # Closed-Val splice: trust-mode check. The carried Val is opaque
        # to type-directed elaboration; we trust the user/elaborator that
        # produced the Val to have its type match `ty`. Same trust
        # boundary as `opaque-lam` for negative types — the splice
        # introduces a closed value reflected from the semantic domain,
        # and the kernel never inspects its internal structure here.
        else if t == "lit-val" then pure (T.mkLitVal tm.val)

        else if t == "string-lit" && ty.tag == "VString" then pure (T.mkStringLit tm.value)
        else if t == "int-lit" && ty.tag == "VInt" then pure (T.mkIntLit tm.value)
        else if t == "float-lit" && ty.tag == "VFloat" then pure (T.mkFloatLit tm.value)
        else if t == "attrs-lit" && ty.tag == "VAttrs" then pure T.mkAttrsLit
        else if t == "path-lit" && ty.tag == "VPath" then pure T.mkPathLit
        else if t == "derivation-lit" && ty.tag == "VDerivation" then pure T.mkDerivationLit
        else if t == "fn-lit" && ty.tag == "VFunction" then pure T.mkFnLit
        else if t == "any-lit" && ty.tag == "VAny" then pure T.mkAnyLit

        # Opaque lambda checked against Pi: verify domain conv-equality.
        else if t == "opaque-lam" && ty.tag == "VPi" then
          bindPR P.OpaqueType "opaque-lam" (self.checkType ctx tm.piTy)
            (piTyTm:
              let piTyVal = E.eval ctx.env piTyTm; in
              if piTyVal.tag != "VPi" then
                send "typeError"
                  {
                    error = D.mkKernelError {
                      position = P.OpaqueType;
                      rule = "opaque-lam";
                      msg = "opaque-lam annotation must be Pi";
                      expected = Q.quote ctx.depth ty;
                      got = Q.quote ctx.depth piTyVal;
                      term = { tag = tm.tag; };
                      frame = D.captureFrame ctx;
                    };
                  }
              else if !(C.conv ctx.depth piTyVal.domain ty.domain) then
                send "typeError"
                  {
                    error = D.mkKernelError {
                      position = P.OpaqueType;
                      rule = "opaque-lam";
                      msg = "opaque-lam domain mismatch";
                      expected = Q.quote ctx.depth ty.domain;
                      got = Q.quote ctx.depth piTyVal.domain;
                      term = { tag = tm.tag; };
                      frame = D.captureFrame ctx;
                    };
                  }
              else pure (T.mkOpaqueLam tm._fnBox piTyTm))

        # desc-con checked against Mu — trampolined for deep recursive
        # data (5000+). Peels a homogeneous desc-con chain along its
        # single recursive position when D classifies as plus A B with
        # exactly one of A, B linear-recursive (descArg-chain ending in
        # `descRec descRet`). Plus is read through the private desc-view;
        # `linearProfile` accepts both primitive and encoded descriptions.
        #
        # Payload at each layer is `inl/inr lTy rTy (pair f_0 … (pair REC refl))`
        # — n data fields, the recursive tail, and a refl witness for
        # the ret-leaf equality. lTy/rTy are invariant across layers (D
        # is shared) and reused from the first peel.
        #
        # Non-linear shapes (tree, mutual recursion, multi-recursive
        # ctors, non-plus D) use the generic Desc-payload checker.
        #
        # Each layer carries its own target index `i : I` via the 3-arg
        # `mkDescCon D i d`. The trampoline checks `layer.i : I` and
        # conv-matches against the expected index (ty.i at the top of
        # the chain, the rec position's `j` at successors). The payload
        # type at each layer is `interp I D μD layer.i`.
        else if t == "desc-con" && ty.tag == "VMu" then
          let iTyVal = ty.I;
          in bindPR P.MuDesc "desc-con" (self.checkDescAtAnyLevel ctx tm.D iTyVal) (dInfo:
            let
              dTm = dInfo.term;
              dVal = E.eval ctx.env dTm;
              cert = tm._descConCert or null;
              certRef = if cert == null then null else evalDescRef ctx.env cert.ref;
              certHasTarget = cert != null && (cert ? target);
              certTargetIsIndex =
                certHasTarget && sameSyntax cert.target tm.i;
              certTargetVal =
                if !certHasTarget || certTargetIsIndex then null
                else E.eval ctx.env cert.target;
              certMatchesDesc =
                cert != null
                && (cert.kind or null) == "datatype-con-payload"
                && dVal ? _descRef
                && ty.D ? _descRef
                && descRefConv ctx.depth dVal._descRef ty.D._descRef
                && descRefConv ctx.depth certRef ty.D._descRef;
              certMatchesActualDesc =
                cert != null
                && (cert.kind or null) == "datatype-con-payload"
                && dVal ? _descRef
                && descRefConv ctx.depth certRef dVal._descRef;
              certCompatibleDesc =
                certMatchesDesc
                || (certMatchesActualDesc
                && ty.D ? _descRef
                && C.conv ctx.depth dVal ty.D);
              certConstructors =
                if certRef == null then [ ] else certRef.constructors or [ ];
              certCtor = if cert == null then null else cert.ctor or null;
              certCtorShape =
                if builtins.isInt certCtor
                  && certCtor >= 0
                  && certCtor < builtins.length certConstructors
                then builtins.elemAt certConstructors certCtor
                else null;
              certFieldKinds =
                if certCtorShape == null then [ ]
                else certCtorShape.fieldKinds or [ ];
              certHasNoRec =
                builtins.foldl'
                  (ok: kind: ok && kind != "recAt")
                  true
                  certFieldKinds;
              payloadMatchesCtor = ctor: arity: payload:
                if arity == 1 then true
                else if ctor == 0 then payload.tag == "boot-inl"
                else payload.tag == "boot-inr"
                  && payloadMatchesCtor (ctor - 1) (arity - 1) payload.term;
              certNonRecursiveShape =
                certCompatibleDesc
                && certCtorShape != null
                && (cert.fieldCount or (-1)) == builtins.length certFieldKinds
                && certHasNoRec
                && payloadMatchesCtor certCtor (builtins.length certConstructors) tm.d;
              muDFunc = V.vLam "_i" iTyVal (V.mkClosure [ dVal iTyVal ]
                (T.mkMu (T.mkVar 2) (T.mkVar 1) (T.mkVar 0)));
            in
            if !(certMatchesDesc || C.conv ctx.depth dVal ty.D)
            then
              send "typeError"
                {
                  error = D.mkKernelError {
                    position = P.MuDesc;
                    rule = "desc-con";
                    msg = "desc-con description mismatch";
                    expected = Q.quote ctx.depth ty.D;
                    got = Q.quote ctx.depth dVal;
                    term = { tag = tm.tag; };
                    frame = D.captureFrame ctx;
                  };
                }
            else
              bindPR P.MuIndex "desc-con"
                (
                  if iTyVal.tag == "VUnit" && tm.i.tag == "tt"
                  then pure T.mkTt
                  else self.check ctx tm.i iTyVal
                )
                (topITm:
                  let topIVal = E.eval ctx.env topITm; in
                  if !(C.conv ctx.depth topIVal ty.i)
                  then
                    send "typeError"
                      {
                        error = D.mkKernelError {
                          position = P.MuIndex;
                          rule = "desc-con";
                          msg = "desc-con target index mismatch";
                          expected = Q.quote ctx.depth ty.i;
                          got = Q.quote ctx.depth topIVal;
                          term = { tag = tm.tag; };
                          frame = D.captureFrame ctx;
                        };
                      }
                  else
                    if certNonRecursiveShape
                      && (certTargetIsIndex || (certHasTarget && C.conv ctx.depth certTargetVal topIVal))
                    then
                      let interpTy = E.vInterpD dInfo.level iTyVal dVal muDFunc topIVal; in
                      bindPR P.MuPayload "desc-con" (self.check ctx tm.d interpTy) (dataTm:
                        pure (T.mkDescConWithCert dTm topITm dataTm cert))
                    else
                      let
                        # Classify ty.D as plus(A, B) with one linear-recursive side.
                        plusSides =
                          let view = E.descView dVal; in
                          if view != null && view.idx == 4
                          then { A = view.A; B = view.B; }
                          else null;
                        classify =
                          if plusSides == null then null
                          else
                            let
                              pA = E.linearProfile plusSides.A;
                              pB = E.linearProfile plusSides.B;
                            in
                            if pA != null && pB == null then { profile = pA; side = "inl"; }
                            else if pB != null && pA == null then { profile = pB; side = "inr"; }
                            else null;
                      in
                      if classify == null then
                        bindPR P.MuPayload "desc-con"
                          (fx.tc.generic.checkD.checkD ctx dInfo.level iTyVal dVal muDFunc topIVal tm.d)
                          (dataTm: pure (T.mkDescCon dTm topITm dataTm))
                      else
                        let
                          profile = classify.profile;
                          nFields = builtins.length profile;
                          sameD = d2Tm:
                            if d2Tm == tm.D then true
                            else C.conv ctx.depth (E.eval ctx.env d2Tm) dVal;
                          collectPairs = inner:
                            let
                              isRetLeaf = p:
                                p.tag == "boot-refl"
                                || (p.tag == "lift-intro" && p.a.tag == "boot-refl");
                              collect = k: p: acc:
                                if k == nFields then
                                  if p.tag != "pair" then null
                                  else if !(isRetLeaf p.snd) then null
                                  else if p.fst.tag != "desc-con" then null
                                  else { heads = acc; tail = p.fst; leaf = p.snd; }
                                else
                                  if p.tag != "pair" then null
                                  else collect (k + 1) p.snd (acc ++ [ p.fst ]);
                            in
                            collect 0 inner [ ];
                          walkPayload = payload:
                            if classify == null then null
                            else
                              let
                                sv = E.sumPayloadTmView payload;
                                inner =
                                  if sv == null || sv.side != classify.side
                                  then null
                                  else collectPairs sv.value;
                              in
                              if inner == null then null
                              else inner // { rebuild = sv.rebuild; };
                          peel = node:
                            if classify == null then null
                            else if node.tag != "desc-con" then null
                            else if !(sameD node.D) then null
                            else walkPayload node.d;
                          chain = builtins.genericClosure {
                            startSet = [{ key = 0; val = tm; peeled = peel tm; }];
                            operator = item:
                              if item.peeled == null then [ ]
                              else
                                let val = item.peeled.tail; in
                                [{ key = item.key + 1; inherit val; peeled = peel val; }];
                          };
                          n = builtins.length chain - 1;
                          base = (builtins.elemAt chain n).val;
                          topPeel = if n >= 1 then (builtins.elemAt chain 0).peeled else null;
                          wrapPayload = innerTm:
                            topPeel.rebuild innerTm;
                        in
                        bindPChain [ (P.DConLayer n) P.MuIndex ]
                          (
                            if iTyVal.tag == "VUnit" && base.i.tag == "tt"
                            then pure T.mkTt
                            else self.check ctx base.i iTyVal
                          )
                          (baseITm:
                            let
                              baseIVal = E.eval ctx.env baseITm;
                              interpTyBase = E.vInterpD dInfo.level iTyVal dVal muDFunc baseIVal;
                            in
                            bindPChain [ (P.DConLayer n) P.MuPayload ] (self.check ctx base.d interpTyBase) (baseDataTm:
                              let baseTm = T.mkDescCon dTm baseITm baseDataTm; in
                              # Trampoline blame discipline: each layer-k blame is
                                # tagged `[DConLayer k, MuIndex|Elem j]`. `DConLayer`
                                # is the quotient position for homogeneous μ-unfolding
                                # paths — collapses the O(k×nFields) structural prefix
                                # into a single segment so per-blame chain depth stays
                                # 2 regardless of trampoline depth.
                              builtins.foldl'
                                (accComp: k:
                                  let
                                    layerItem = builtins.elemAt chain (n - 1 - k);
                                    layer = layerItem.val;
                                    peeled = layerItem.peeled;
                                    heads = peeled.heads;
                                    # User-facing layer depth: foldl' walks bottom-up
                                    # (k_iter = 0 → just above base) while the user
                                    # numbers layers top-down (0 = outermost).
                                    layerDepth = n - 1 - k;
                                    # Per-layer attestation: each chain node carries its
                                    # own cert, so one unvalidated layer costs one slow
                                    # layer rather than unvalidating the whole chain.
                                    layerCert = layer._descConCert or null;
                                    layerAttested =
                                      layerCert != null
                                      && ((layerCert.validatedFields or { }).validated or false);
                                    checkHeads = j: remaining: accTms:
                                      # Head-yield: re-defers the `attested && depth==0` branch
                                      # whose `m` is a pure `pure h.head` that the bindP
                                      # fast path would otherwise recurse through directly.
                                      yield (if remaining == [ ] then pure accTms
                                      else
                                        let
                                          h = builtins.head remaining;
                                          rest = builtins.tail remaining;
                                        in
                                        bindPChain [ (P.DConLayer layerDepth) (P.Elem j) ]
                                          (if layerAttested && ctx.depth == 0
                                           then pure h.head
                                           else self.check ctx h.head h.S)
                                          (hTm: checkHeads (j + 1) rest (accTms ++ [ hTm ])));
                                    tasks = builtins.genList
                                      (j:
                                        {
                                          head = builtins.elemAt heads j;
                                          S = (builtins.elemAt profile j).S;
                                        })
                                      nFields;
                                    buildInner = hTms: innerTail:
                                      if hTms == [ ] then innerTail
                                      else
                                        T.mkPair (builtins.head hTms)
                                          (buildInner (builtins.tail hTms) innerTail);
                                  in
                                  bind accComp (acc:
                                    bindPChain [ (P.DConLayer layerDepth) P.MuIndex ]
                                      (
                                        if iTyVal.tag == "VUnit" && layer.i.tag == "tt"
                                        then pure T.mkTt
                                        else self.check ctx layer.i iTyVal
                                      )
                                      (layerITm:
                                        bind (checkHeads 0 tasks [ ]) (hTms:
                                          pure (T.mkDescCon dTm layerITm
                                            (wrapPayload
                                              (buildInner hTms (T.mkPair acc peeled.leaf)))))))
                                )
                                (pure baseTm)
                                (builtins.genList (x: x) n)))))

        # Sub rule (§7.4): fall through to synthesis + structural conv.
        # The kernel is Tarski + non-cumulative: a term checked against
        # `U(k)` must have inferred type exactly `U(k)` modulo `convLevel`.
        # No universe-cumulativity coercion fires — the bidirectional
        # path's only bridge from CHECK to INFER is the structural conv
        # round-trip. Per-summand level mixing in `desc-arg` / `desc-pi`
        # is handled by the bound-witness slot, not by this rule.
        # `bindP P.Sub` tags the INFER sub-call so any positional blame
        # raised inside synthesis bubbles up under the `Sub` wrapper —
        # users see a chain ending in `sub` and know the failure came
        # through the CHECK→INFER bridge.
        else
          bindPR P.Sub "check" (self.infer ctx tm) (result:
            let inferredTy = result.type; in
            if C.conv ctx.depth inferredTy ty
            then pure result.term
            else
              send "typeError" {
                error = D.mkKernelError {
                  rule = "check";
                  msg = "type mismatch";
                  expected = Q.quote ctx.depth ty;
                  got = Q.quote ctx.depth inferredTy;
                  term = { tag = tm.tag; };
                  frame = D.captureFrame ctx;
                };
              });
        in
        if isLeaf then body else yield body;
    };
  };

  tests = { };
}
