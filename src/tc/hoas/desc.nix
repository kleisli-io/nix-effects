# Description prelude (natDesc / listDesc / sumDesc), descDesc, and the
# descDesc-encoded constructor / eliminator bundle.
#
# Note on lam annotations: check.nix's check-lam discards the
# HOAS lam's domain annotation and uses the expected type's domain when
# descending, so inner case annotations are for READABILITY only. The
# motive's annotations, by contrast, build the encoded eliminator's
# case types, so the motive's annotations MUST be the true types
# (eval/desc.nix's closed Tms use U(0) placeholders for the same
# binders because eval is not re-checked; HOAS cannot).
#
# The macro-derived prelude descriptions live at the I=⊤ slice:
# `desc`/`descRet`/`descRec`/`descPi` are the ⊤-slice aliases from
# combinators.nix. `mu`/`descCon`/`descInd` carry explicit indices; at
# I=⊤, call sites write `self.ttPrim` at the index position (the
# kernel-primitive ⊤-inhabitant, not the HOAS-surface `tt` which is
# rebindable to a derived descCon).
{ self, fx, ... }:

{
  scope = {
    natDesc = self.NatDT.D;
    listDesc = elem: self.app self.ListDT.D elem;
    sumDescAt = k: l: r:
      let kTm = if builtins.isInt k then self.natToLevel k else k; in
      self.app (self.app (self.app self.SumDT.D kTm) l) r;
    sumDesc = l: r: self.sumDescAt self.levelZero l r;

    # descDesc : Π(I : U(0))(k : Level). Desc^(suc k) ⊤ — I- and
    # k-parameterised description-of-descriptions. Five summands
    # mirroring `Desc I k`'s grammar at the homogeneous-l image:
    #   ret  — Π(i : I). ⊤
    #   arg  — Π(S : U(k)). Π(T : S → ⊤). ⊤
    #   rec  — Π(i : I). Π(_ : ⊤). ⊤
    #   pi   — Π(S : U(k)). Π(f : S → I). Π(_ : ⊤). ⊤
    #   plus — Π(_ : ⊤). Π(_ : ⊤). ⊤
    # The ret / rec summands prefix `descArgAt 0 (suc k) I` to carry
    # the I-typed leaf index of `descRet I i` / `descRec I i D`. The
    # pi summand carries `descArgAt k (suc k) (S → I) (_f: ...)` to
    # encode the source's `f : S → I` selector. Bound witnesses
    # discharge via convLevel: `max 0 (suc k) = suc k`, `max k (suc k)
    # = suc k`. Heterogeneous formation (per-summand `(l, eq, S:U(l))`)
    # is allowed by Decision #3 but not encoded here — Steps 1–4 of
    # plan §T2 operate on the homogeneous-l subset; Step 5 closes the
    # heterogeneous-elimination gap uniformly via `ind`-over-`descDesc`
    # plus Lift discipline at case bodies.
    descDesc =
      let inherit (self) lam forall annTrusted level levelSuc u descAt; in
      annTrusted
        (lam "I" (u 0) (I:
           lam "k" level (k:
             let
               c = self.descEncodingCtx self.unitPrim (levelSuc k);
               inherit (c) plus descRet descArg descArgAt descRec descPiAt;
               sk = levelSuc k;
             in
             plus (descArgAt 0 sk I (_i: descRet))
             (plus (descArg sk (u k) (S: descPiAt k sk S descRet))
             (plus (descArgAt 0 sk I (_i: descRec descRet))
             (plus (descArg sk (u k) (S:
                      descArgAt k sk (forall "_" S (_: I)) (_f:
                        descRec descRet)))
                   (descRec (descRec descRet))))))))
        (forall "I" (u 0) (I:
          forall "k" level (k: descAt (levelSuc k))));

    # Pre-elaborated Nat description for the Nat type former.
    natDescTm = self.elab self.natDesc;

    # Pre-elaborated descDesc Tm + its evaluated VLam form. The Val is
    # consumed by the conv unfolding rule `Desc I k ≡ μ ⊤ (descDesc I
    # k) tt` (tc/conv.nix): vApp on v.I and v.level reduces it to the
    # finite description tree the rule compares against. Module init
    # is cycle-safe because `descDescApp` tags the recursive reference
    # before conv/quote can force the next `.D` layer.
    descDescTm = self.elab self.descDesc;
    descDescVal = fx.tc.eval.eval [] self.descDescTm;

    # Reserved surface identifier for the prelude
    # description-of-descriptions. The elaborator dispatches
    # `_htag = "desc-desc"` to `self.descDescTm`, so call sites that
    # emit `__descDesc` references avoid re-walking the descDesc HOAS
    # tree on every use. The `__` prefix marks the name as
    # kernel-internal — surface code addresses descDesc through this
    # canonical token.
    __descDesc = { _htag = "desc-desc"; };

    # Identity-tagged HOAS form of `descDesc I L`. Elaborates to the
    # `desc-desc-app` Tm; its eval rule produces a VDescCon stamped
    # with `_canonRef = { id = "descDesc"; I; L; }`. Stand-in for
    # `app (app descDesc I) L` at call sites that need conv/quote to
    # decide equality on the tag rather than walk `.D`.
    descDescApp = I: L: { _htag = "desc-desc-app"; inherit I L; };

    # Per-(I, k) HOAS encoding context for descDesc-encoded μ-trees.
    # Single source of truth for the descDesc summand layout, the
    # plus-tree spine, the right-associated `encodeTag` pathing, and
    # the descRet-leaf `Lift 0 (suc k) (Eq ⊤ tt tt)` discipline.
    # Consumed by the `iso` bundle's `to` side and by the standalone
    # `encodeDesc{Ret,Arg,Rec,Pi,Plus}` encoders.
    #
    # Inputs `I : U(0)` and `k : Level` are HOAS terms — typically the
    # bound variables of an outer `lam "I" ... lam "k" ...` chain. The
    # returned record's fields close over those terms; reusing the
    # same record across a single encoder body is fine since each
    # field is a HOAS expression referencing the same I, k variables.
    descEncodingCtx = I: kRaw:
      let
        inherit (self) lam forall pair ttPrim unitPrim
                       levelZero levelSuc u bootEq bootRefl descIAt
                       liftAt lowerAt muI mu interpD
                       encodeTagAt;
        # The local aliases describe `descDesc`'s own summands through the
        # encoded constructor layer. Each encoder body still shares this
        # one context, so recursive consumers see a uniform tagged `dDesc`
        # and encoded sub-description spine.
        plus = A: B: self.plusI self.unitPrim sk A B;
        descRet = self.retI self.unitPrim sk self.ttPrim;
        descArg = kArg: S: T: self.descArg self.unitPrim kArg S T;
        descArgAt = lArg: kArg: S: T:
          self.descArgAt self.unitPrim lArg kArg S T;
        descRec = D: self.recI self.unitPrim sk self.ttPrim D;
        descPiAt = lArg: kArg: S: D:
          self.descPiAt lArg kArg S D;
        # Callers may pass `kRaw` as a Nix-meta `Int`; coerce here so the shared level is a
        # `level-zero` / `level-suc` / `level-lit` HOAS form rather than
        # a raw `Int`.
        k =
          if builtins.isInt kRaw
          then if kRaw == 0 then levelZero
               else builtins.foldl' (acc: _: levelSuc acc) levelZero
                      (builtins.genList (x: x) kRaw)
          else kRaw;
        sk = levelSuc k;
        dDesc = self.descDescApp I k;
        muTt = mu dDesc ttPrim;
        muFam = lam "_i" unitPrim (iArg: mu dDesc iArg);
        dDescL = sk;
        descK = descIAt k I;
        conDescs = [
          (descArgAt 0 sk I (_i: descRet))
          (descArg sk (u k) (S: descPiAt k sk S descRet))
          (descArgAt 0 sk I (_i: descRec descRet))
          (descArg sk (u k) (S:
             descArgAt k sk (forall "_" S (_: I)) (_f:
               descRec descRet)))
          (descRec (descRec descRet))
        ];
        spineFrom = i:
          let n = builtins.length conDescs; remaining = n - i; in
          if remaining == 1 then builtins.elemAt conDescs i
          else plus (builtins.elemAt conDescs i) (spineFrom (i + 1));
        encodeAt = t: payload:
          encodeTagAt dDescL unitPrim dDesc conDescs ttPrim t payload;
        interpAt = dH:
          interpD dDescL unitPrim dH muFam ttPrim;
        eqLeafTy = bootEq unitPrim ttPrim ttPrim;
        liftLeaf = e: liftAt levelZero dDescL eqLeafTy e;
        lowerLeaf = x: lowerAt levelZero dDescL eqLeafTy x;
        liftedRefl = liftLeaf bootRefl;
      in {
        inherit dDesc muTt muFam dDescL descK
                plus descRet descArg descArgAt descRec descPiAt
                conDescs spineFrom encodeAt interpAt
                eqLeafTy liftLeaf lowerLeaf liftedRefl sk;
      };

    # ─────────────────────────────────────────────────────────────────
    # descDesc-encoded constructors. Each `encodeDescX` is a closed
    # HOAS term that, applied to `(I, k, …source-fields…)`, produces a
    # `μ ⊤ (descDesc I k) tt` value structurally encoding the
    # corresponding source description. Pre-elaborated to closed Tms
    # (`encodeDescXTm`) at module init so kernel-level consumers can
    # apply them via `mkApp` without re-walking the encoder HOAS tree.
    #
    # The encoders share `descEncodingCtx I k`'s summand layout with
    # `iso.to`: a single definition of the encoding shape lives in
    # `descEncodingCtx`, and both `iso` and the encoders consume it.
    # Recursive sub-descriptions (the body of `arg`, the tail of
    # `rec`, the body of `pi`, both summands of `plus`) arrive already
    # encoded — callers compose by feeding sub-results back in.
    # ─────────────────────────────────────────────────────────────────

    encodeDescRet =
      let inherit (self) lam forall ann u level pair descCon ttPrim
                         descEncodingCtx; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "j" I (j:
            descCon c.dDesc ttPrim
              (c.encodeAt 0 (pair j c.liftedRefl))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
          forall "j" I (_:
            (descEncodingCtx I k).muTt))));

    encodeDescRetTm = self.elab self.encodeDescRet;

    # encodeDescArgAt : Π(I:U(0))(k l:Level)(eq : Eq Level (max l k) k)
    #                     (S:U(l))(T:S → μ⊤(descDesc I k)tt).
    #                   μ ⊤ (descDesc I k) tt
    # Heterogeneous-l encoder for descArg: S inhabits U(l) with bound
    # witness `eq : l ≤ k`. The encoded payload's S slot expects U(k),
    # so S is `LiftAtWithEq l k eq`-wrapped; T's domain (S : U(l)) is
    # bridged to the lifted form via `lowerAtWithEq`. Idempotent at l=k:
    # `LiftAt k k refl A ≡ A` collapses via `vLiftF`'s convLevel
    # idempotency, recovering the homogeneous shape.
    encodeDescArgAt =
      let inherit (self) lam forall ann u level levelMax app pair descCon
                         ttPrim descEncodingCtx bootEq
                         LiftAtWithEq lowerAtWithEq; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
         lam "l" level (l:
         lam "eqW" (bootEq level (levelMax l k) k) (eqW:
          let c = descEncodingCtx I k; in
          lam "S" (u l) (S:
          lam "T" (forall "_" S (_: c.muTt)) (T:
            let
              sLifted = LiftAtWithEq l k eqW S;
              tLifted = lam "x" sLifted (x:
                          app T (lowerAtWithEq l k eqW S x));
            in
            descCon c.dDesc ttPrim
              (c.encodeAt 1 (pair sLifted (pair tLifted c.liftedRefl))))))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
         forall "l" level (l:
         forall "eqW" (bootEq level (levelMax l k) k) (_:
          forall "S" (u l) (S:
          forall "T" (forall "_" S (_: (descEncodingCtx I k).muTt)) (_:
            (descEncodingCtx I k).muTt)))))));

    encodeDescArgAtTm = self.elab self.encodeDescArgAt;

    # encodeDescArg : Π(I:U(0))(k:Level)(S:U(k))(T:S → μ⊤(descDesc I k)tt).
    #                 μ ⊤ (descDesc I k) tt
    # Homogeneous-l specialisation of `encodeDescArgAt` at `l = k` with
    # `refl : Eq Level (max k k) k` (decided by convLevel idempotency).
    # `LiftAt k k refl S ≡ S` collapses, so the encoded payload is
    # equivalent to a direct `(S, T, liftedRefl)` triple.
    encodeDescArg =
      let inherit (self) lam forall ann u level app bootRefl
                         descEncodingCtx encodeDescArgAt; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "S" (u k) (S:
          lam "T" (forall "_" S (_: c.muTt)) (T:
            app (app (app (app (app (app encodeDescArgAt I) k) k) bootRefl) S) T)))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
          forall "S" (u k) (S:
          forall "T" (forall "_" S (_: (descEncodingCtx I k).muTt)) (_:
            (descEncodingCtx I k).muTt)))));

    encodeDescArgTm = self.elab self.encodeDescArg;

    # encodeDescRec : Π(I:U(0))(k:Level)(j:I)(D:μ⊤(descDesc I k)tt).
    #                 μ ⊤ (descDesc I k) tt
    # Encodes a `descRec j D`-shaped source description.
    encodeDescRec =
      let inherit (self) lam forall ann u level pair descCon ttPrim
                         descEncodingCtx; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "j" I (j:
          lam "D" c.muTt (D:
            descCon c.dDesc ttPrim
              (c.encodeAt 2 (pair j (pair D c.liftedRefl))))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
          forall "j" I (_:
          forall "D" (descEncodingCtx I k).muTt (_:
            (descEncodingCtx I k).muTt)))));

    encodeDescRecTm = self.elab self.encodeDescRec;

    # encodeDescPiAt : Π(I:U(0))(k l:Level)(eq : Eq Level (max l k) k)
    #                    (S:U(l))(f:S→I)(D:μ⊤(descDesc I k)tt).
    #                  μ ⊤ (descDesc I k) tt
    # Heterogeneous-l encoder for descPi: S inhabits U(l) with bound
    # witness `eq : l ≤ k`. The encoded payload's S slot is lifted to
    # U(k) via `LiftAtWithEq`; the f-selector's domain is bridged via
    # `lowerAtWithEq`. The body D is a single recursion image (muTt) —
    # the descPi's recursive position carries one sub-description, not
    # a function. Idempotent at l=k via `LiftAt k k refl A ≡ A`.
    encodeDescPiAt =
      let inherit (self) lam forall ann u level levelMax app pair descCon
                         ttPrim descEncodingCtx bootEq
                         LiftAtWithEq lowerAtWithEq; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
         lam "l" level (l:
         lam "eqW" (bootEq level (levelMax l k) k) (eqW:
          let c = descEncodingCtx I k; in
          lam "S" (u l) (S:
          lam "f" (forall "_" S (_: I)) (f:
          lam "D" c.muTt (D:
            let
              sLifted = LiftAtWithEq l k eqW S;
              fLifted = lam "x" sLifted (x:
                          app f (lowerAtWithEq l k eqW S x));
            in
            descCon c.dDesc ttPrim
              (c.encodeAt 3 (pair sLifted (pair fLifted
                              (pair D c.liftedRefl))))))))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
         forall "l" level (l:
         forall "eqW" (bootEq level (levelMax l k) k) (_:
          forall "S" (u l) (S:
          forall "f" (forall "_" S (_: I)) (_:
          forall "D" (descEncodingCtx I k).muTt (_:
            (descEncodingCtx I k).muTt))))))));

    encodeDescPiAtTm = self.elab self.encodeDescPiAt;

    # encodeDescPi : Π(I:U(0))(k:Level)(S:U(k))(f:S→I)
    #                  (D:μ⊤(descDesc I k)tt). μ ⊤ (descDesc I k) tt
    # Homogeneous-l specialisation of `encodeDescPiAt` at `l = k` with
    # `refl : Eq Level (max k k) k`. `LiftAt k k refl S ≡ S` collapses,
    # recovering the direct `(S, f, D, liftedRefl)` payload shape.
    encodeDescPi =
      let inherit (self) lam forall ann u level app bootRefl
                         descEncodingCtx encodeDescPiAt; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "S" (u k) (S:
          lam "f" (forall "_" S (_: I)) (f:
          lam "D" c.muTt (D:
            app (app (app (app (app (app (app encodeDescPiAt I) k) k) bootRefl) S) f) D))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
          forall "S" (u k) (S:
          forall "f" (forall "_" S (_: I)) (_:
          forall "D" (descEncodingCtx I k).muTt (_:
            (descEncodingCtx I k).muTt))))));

    encodeDescPiTm = self.elab self.encodeDescPi;

    # encodeDescPlus : Π(I:U(0))(k:Level)(A:μ⊤(descDesc I k)tt)
    #                    (B:μ⊤(descDesc I k)tt). μ ⊤ (descDesc I k) tt
    # Encodes a `descPlus A B`-shaped source description.
    encodeDescPlus =
      let inherit (self) lam forall ann u level pair descCon ttPrim
                         descEncodingCtx; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "A" c.muTt (A:
          lam "B" c.muTt (B:
            descCon c.dDesc ttPrim
              (c.encodeAt 4 (pair A (pair B c.liftedRefl))))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
          forall "A" (descEncodingCtx I k).muTt (_:
          forall "B" (descEncodingCtx I k).muTt (_:
            (descEncodingCtx I k).muTt)))));

    encodeDescPlusTm = self.elab self.encodeDescPlus;

    # encodeDescElim : Π(I:U(0))(k:Level)(L:Level)
    #                    (motive : μ⊤(descDesc I k)tt → U(L))
    #                    (onRet  : Π(j:I). motive (encodeDescRet I k j))
    #                    (onArg  : Π(S:U(k))(T:S → μ⊤(descDesc I k)tt)
    #                              (ih:Π(s:S). motive (T s)).
    #                              motive (encodeDescArg I k S T))
    #                    (onRec  : Π(j:I)(D:μ⊤(descDesc I k)tt)
    #                              (ih:motive D).
    #                              motive (encodeDescRec I k j D))
    #                    (onPi   : Π(S:U(k))(f:S→I)(D:μ⊤(descDesc I k)tt)
    #                              (ih:motive D).
    #                              motive (encodeDescPi I k S f D))
    #                    (onPlus : Π(A B:μ⊤(descDesc I k)tt)
    #                              (ihA:motive A)(ihB:motive B).
    #                              motive (encodeDescPlus I k A B))
    #                    (scrut : μ⊤(descDesc I k)tt). motive scrut
    #
    # `descInd` over `μ ⊤ (descDesc I k) tt` with a step body that
    # destructures the descCon payload's right-associated Plus5
    # structure via a 4-layer `bootSumElim` cascade. Cascade pattern
    # mirrors iso's `from`: at each layer the Inl branch dispatches
    # to the matched summand's user case body, the Inr branch
    # recurses into the next summand. At depth 4 (plus) the cascade
    # terminates without a sum — the encoded descCon payload is a
    # bare pair carrying the two recursive μ-elements.
    encodeDescElim =
      let
        inherit (self) lam forall ann u level pair fst_ snd_ app
                       descCon descInd bootSum bootSumElim
                       bootInl bootInr
                       ttPrim unitPrim
                       descEncodingCtx
                       interpD allD
                       encodeDescRet encodeDescArg encodeDescRec
                       encodeDescPi encodeDescPlus;

        # Flat encoder applications used in the result-type ascriptions.
        encRet  = I: k: j:    app (app (app encodeDescRet I) k) j;
        encArg  = I: k: S: T: app (app (app (app encodeDescArg I) k) S) T;
        encRec  = I: k: j: D: app (app (app (app encodeDescRec I) k) j) D;
        encPi   = I: k: S: f: D:
                  app (app (app (app (app encodeDescPi I) k) S) f) D;
        encPlus = I: k: A: B:
                  app (app (app (app encodeDescPlus I) k) A) B;

        # The full bound-binder body; reused inside both the lam chain
        # (for the elaborated term) and the forall chain (for ann).
        bodyOnArgs = I: k: L: motive: onRet: onArg: onRec: onPi: onPlus: scrut:
          let
            c = descEncodingCtx I k;
            # descInd's motive: λ(_i:⊤). λ(x:μ⊤(descDesc I k)i). motive x.
            # I=⊤ so the index dependence is vacuous — discard `_i`.
            motiveI = lam "_i" unitPrim (_:
                      lam "x" c.muTt (x:
                        app motive x));

            # Per-summand case bodies. Receive `ctx` (the outer-payload
            # accumulator threaded by `cascade`), the matched payload
            # `r` (or bare `dCur` at depth 4) plus the per-summand
            # all-IH `rih` (or `ihCur` at depth 4); emit the user case
            # body applied to its arguments.
            caseRet = _ctx: r: _rih: app onRet (fst_ r);

            caseArg = _ctx: r: rih:
              let
                S    = fst_ r;
                T    = fst_ (snd_ r);
                ihFn = fst_ rih;
              in app (app (app onArg S) T) ihFn;

            caseRec = _ctx: r: rih:
              let
                jVal = fst_ r;
                D    = fst_ (snd_ r);
                ihD  = fst_ rih;
              in app (app (app onRec jVal) D) ihD;

            casePi = _ctx: r: rih:
              let
                S   = fst_ r;
                f   = fst_ (snd_ r);
                D   = fst_ (snd_ (snd_ r));
                ihD = fst_ rih;
              in app (app (app (app onPi S) f) D) ihD;

            # depth 4 — no enclosing sum at this layer; the rest-spine
            # is the bare descPlus pair `(A, B, leafLifted)`. `ctx` has
            # already accumulated the four outer `bootInr` wrappers.
            casePlus = _ctx: dCur: ihCur:
              let
                A   = fst_ dCur;
                B   = fst_ (snd_ dCur);
                ihA = fst_ ihCur;
                ihB = fst_ (snd_ ihCur);
              in app (app (app (app onPlus A) B) ihA) ihB;

            # Cascade layer at depthIdx in {0..4}. `dCur` is the encoded
            # descCon payload at this layer (a Sum at 0..3, a Pair at 4);
            # `ihCur` is the corresponding All-witness. `ctx` reconstructs
            # the OUTER payload from this layer's inner shape — at the
            # outermost call `ctx = id`; at each Inr descent it extends
            # to wrap one more `bootInr lTy rTy`. This makes sumMot's
            # `descCon c.dDesc tt (ctx s)` well-typed at every depth K
            # because `ctx s : interpAt c.dDesc` by construction.
            cascade = depthIdx: ctx: dCur: ihCur:
              if depthIdx == 4 then
                casePlus ctx dCur ihCur
              else
                let
                  curD      = builtins.elemAt c.conDescs depthIdx;
                  restSpine = c.spineFrom (depthIdx + 1);
                  lTy       = c.interpAt curD;
                  rTy       = c.interpAt restSpine;
                  caseFn =
                         if depthIdx == 0 then caseRet
                    else if depthIdx == 1 then caseArg
                    else if depthIdx == 2 then caseRec
                    else                        casePi;
                  sumMot = lam "s" (bootSum lTy rTy) (s:
                    forall "_rih"
                      (allD c.dDescL unitPrim (c.plus curD restSpine)
                        c.dDescL c.muFam motiveI ttPrim s)
                      (_: app motive (descCon c.dDesc ttPrim (ctx s))));
                  onInl = lam "r" lTy (r:
                          lam "rih"
                            (allD c.dDescL unitPrim curD
                              c.dDescL c.muFam motiveI ttPrim r) (rih:
                            caseFn ctx r rih));
                  ctx' = s_in: ctx (bootInr lTy rTy s_in);
                  onInr = lam "r" rTy (r:
                          lam "rih"
                            (allD c.dDescL unitPrim restSpine
                              c.dDescL c.muFam motiveI ttPrim r) (rih:
                            cascade (depthIdx + 1) ctx' r rih));
                in
                  app (bootSumElim lTy rTy sumMot onInl onInr dCur) ihCur;

            step = lam "_i" unitPrim (iArg:
                   lam "d" (interpD c.dDescL unitPrim c.dDesc c.muFam iArg) (d:
                   lam "ih" (allD c.dDescL unitPrim c.dDesc
                                c.dDescL c.muFam motiveI iArg d) (ih:
                     cascade 0 (s: s) d ih)));
          in
            descInd c.dDesc motiveI step ttPrim scrut;
      in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
         lam "L" level (L:
          let c = descEncodingCtx I k;
              motiveTy = forall "_" c.muTt (_: u L);
          in
          lam "motive" motiveTy (motive:
          lam "onRet"
            (forall "j" I (j: app motive (encRet I k j)))
            (onRet:
          lam "onArg"
            (forall "S" (u k) (S:
             forall "T" (forall "_" S (_: c.muTt)) (T:
             forall "ih" (forall "_s" S (s: app motive (app T s))) (_:
               app motive (encArg I k S T)))))
            (onArg:
          lam "onRec"
            (forall "j" I (j:
             forall "D" c.muTt (D:
             forall "ih" (app motive D) (_:
               app motive (encRec I k j D)))))
            (onRec:
          lam "onPi"
            (forall "S" (u k) (S:
             forall "f" (forall "_" S (_: I)) (f:
             forall "D" c.muTt (D:
             forall "ih" (app motive D) (_:
               app motive (encPi I k S f D))))))
            (onPi:
          lam "onPlus"
            (forall "A" c.muTt (A:
             forall "B" c.muTt (B:
             forall "ihA" (app motive A) (_:
             forall "ihB" (app motive B) (_:
               app motive (encPlus I k A B))))))
            (onPlus:
          lam "scrut" c.muTt (scrut:
            bodyOnArgs I k L motive onRet onArg onRec onPi onPlus scrut)))))))))))
        (forall "I" (u 0) (I:
         forall "k" level (k:
         forall "L" level (L:
          let c = descEncodingCtx I k;
              motiveTy = forall "_" c.muTt (_: u L);
          in
          forall "motive" motiveTy (motive:
          forall "onRet"
            (forall "j" I (j: app motive (encRet I k j)))
            (_:
          forall "onArg"
            (forall "S" (u k) (S:
             forall "T" (forall "_" S (_: c.muTt)) (T:
             forall "ih" (forall "_s" S (s: app motive (app T s))) (_:
               app motive (encArg I k S T)))))
            (_:
          forall "onRec"
            (forall "j" I (j:
             forall "D" c.muTt (D:
             forall "ih" (app motive D) (_:
               app motive (encRec I k j D)))))
            (_:
          forall "onPi"
            (forall "S" (u k) (S:
             forall "f" (forall "_" S (_: I)) (f:
             forall "D" c.muTt (D:
             forall "ih" (app motive D) (_:
               app motive (encPi I k S f D))))))
            (_:
          forall "onPlus"
            (forall "A" c.muTt (A:
             forall "B" c.muTt (B:
             forall "ihA" (app motive A) (_:
             forall "ihB" (app motive B) (_:
               app motive (encPlus I k A B))))))
            (_:
          forall "scrut" c.muTt (scrut:
            app motive scrut)))))))))));

    encodeDescElimTm = self.elab self.encodeDescElim;

    encodeDescElimVal = fx.tc.eval.eval [] self.encodeDescElimTm;
  };
}
