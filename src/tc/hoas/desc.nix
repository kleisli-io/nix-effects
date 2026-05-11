# Description-level helpers (interpHoasAt / allHoasAt) and prelude
# descriptions (natDesc / listDesc / sumDesc), plus the pre-elaborated
# natDescTm used by the elaborate layer's zero/succ/ind branches to
# avoid re-elaborating natDesc on every constructor.
#
# interpHoasAt and allHoasAt elaborate to `descElim` spines that compute
# the same values as eval/desc.nix's interpF / allTyF. Every HOAS binder
# here mirrors a named interpMotive / interpOn* / mkAllMotive / allOn*
# in eval/desc.nix; conv between stuck `desc-elim` frames on the two
# sides relies on that structural match. Both helpers take a leading
# `L : Level` parameter — the scrutinee description's `descArg`/`descPi`
# K-slot — threaded into descElim's leading k, the `descIAt L I` ann-
# wrap, and every `u L` sort-binder so the kernel typing constraints
# line up at the actual scrutinee level (zero for the prelude,
# `levelSuc k` for the descDesc-iso).
#
# Note on lam annotations: check.nix's check-lam discards the
# HOAS lam's domain annotation and uses the expected type's domain when
# descending, so inner case annotations are for READABILITY only. The
# motive's annotations, by contrast, build paTy / peTy / ppTy in the
# desc-elim check rule, so the motive's annotations MUST be the true
# types (eval/desc.nix's closed Tms use U(0) placeholders for the same
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
    # natDesc : Desc ⊤ — zero (no recursion) ⊕ succ (one rec arg). The
    # first-class coproduct `plus` replaces the Bool-tag-dispatched
    # `descArg bool (b: boolElim _ zeroD succD b)` encoding.
    # `interp (A ⊕ B) X i` reduces to kernel `Sum (⟦A⟧ X i) (⟦B⟧ X i)`,
    # eliminating the commuting-conv obligation on `interp ∘ bool-elim`.
    natDesc =
      let inherit (self) plus descRet descRec; in
      plus descRet (descRec descRet);

    # listDesc elem : Desc ⊤ — nil (retI) ⊕ cons (head : elem, tail : rec).
    # Universe-polymorphic descArg/descPi take a leading level; the
    # prelude pins `k = 0` since its domains live in `U(0)`.
    listDesc = elem:
      let inherit (self) plus descArg descRet descRec unitPrim; in
      plus descRet (descArg unitPrim 0 elem (_: descRec descRet));

    # sumDesc l r : Desc ⊤ — inl (arg : l) ⊕ inr (arg : r). Both summands
    # are `descArg _ (_: retI ttPrim)` leaves at the ⊤-slice.
    sumDesc = l: r:
      let inherit (self) plus descArg descRet unitPrim; in
      plus (descArg unitPrim 0 l (_: descRet)) (descArg unitPrim 0 r (_: descRet));

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
      let inherit (self) lam forall annTrusted level levelSuc u
                         plusPrim descRetPrim descArgPrim descArgAtPrim
                         descRecPrim descPiAtPrim descAt; in
      annTrusted
        (lam "I" (u 0) (I:
           lam "k" level (k:
             let sk = levelSuc k; in
             plusPrim (descArgAtPrim 0 sk I (_i: descRetPrim))
             (plusPrim (descArgPrim sk (u k) (S: descPiAtPrim k sk S descRetPrim))
             (plusPrim (descArgAtPrim 0 sk I (_i: descRecPrim descRetPrim))
             (plusPrim (descArgPrim sk (u k) (S:
                      descArgAtPrim k sk (forall "_" S (_: I)) (_f:
                        descRecPrim descRetPrim)))
                   (descRecPrim (descRecPrim descRetPrim))))))))
        (forall "I" (u 0) (I:
          forall "k" level (k: descAt (levelSuc k))));

    # Pre-elaborated natDesc — used by the zero/succ/nat-elim elaborate
    # branches to avoid re-elaborating on every constructor.
    natDescTm = self.elab self.natDesc;

    # Pre-elaborated descDesc Tm + its evaluated VLam form. The Val is
    # consumed by the conv unfolding rule `Desc I k ≡ μ ⊤ (descDesc I
    # k) tt` (tc/conv.nix): vApp on v.I and v.level reduces it to the
    # finite description tree the rule compares against. Module init
    # is cycle-safe — descDesc's body is plain plus / descArg / descRet
    # / descPi structure with no Lift wraps, so evalF doesn't reach
    # into convLevel during the initial reduction.
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
        inherit (self) lam forall app pair refl ttPrim unitPrim
                       levelZero levelSuc u eq descIAt
                       descDesc liftAt lowerAt muI mu interpHoasAtPrim
                       encodeTagPrim;
        # Bootstrap: descEncodingCtx supplies the *primitive* sub-
        # descriptions of `descDesc` itself (the description-of-
        # descriptions). The encoded encoders (`encodeDescRet`, ...)
        # construct `descCon dDesc tt (encodeAt t payload)` — the
        # encoding lives at the value level, but the underlying
        # `dDesc` and its sub-descriptions remain primitive HOAS so
        # `interpHoasAtPrim` and `encodeTagPrim`'s primitive cascade
        # can walk them via `descElimPrim`.
        plus = self.plusPrim;
        descRet = self.descRetPrim;
        descArg = self.descArgPrim;
        descArgAt = self.descArgAtPrim;
        descRec = self.descRecPrim;
        descPiAt = self.descPiAtPrim;
        # `app descDesc I k` is a HOAS app whose `arg` slots flow
        # through the elaborator's general `app` rule — it does NOT
        # call `elaborateLevel` on level-shaped args. Callers may pass
        # `kRaw` as a Nix-meta `Int` (e.g. `0` from `interpHoasAt 0 I
        # ...`); coerce here so the resulting HOAS app's `arg` is a
        # `level-zero` / `level-suc` / `level-lit` HOAS form rather
        # than a raw `Int`.
        k =
          if builtins.isInt kRaw
          then if kRaw == 0 then levelZero
               else builtins.foldl' (acc: _: levelSuc acc) levelZero
                      (builtins.genList (x: x) kRaw)
          else kRaw;
        sk = levelSuc k;
        dDesc = app (app descDesc I) k;
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
          encodeTagPrim unitPrim dDesc conDescs ttPrim t payload;
        interpAt = dH:
          interpHoasAtPrim dDescL unitPrim dH muFam ttPrim;
        eqLeafTy = eq unitPrim ttPrim ttPrim;
        liftLeaf = e: liftAt levelZero dDescL eqLeafTy e;
        lowerLeaf = x: lowerAt levelZero dDescL eqLeafTy x;
        liftedRefl = liftLeaf refl;
      in {
        inherit dDesc muTt muFam dDescL descK
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
                         ttPrim descEncodingCtx eq
                         LiftAtWithEq lowerAtWithEq; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
         lam "l" level (l:
         lam "eqW" (eq level (levelMax l k) k) (eqW:
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
         forall "eqW" (eq level (levelMax l k) k) (_:
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
      let inherit (self) lam forall ann u level app refl
                         descEncodingCtx encodeDescArgAt; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "S" (u k) (S:
          lam "T" (forall "_" S (_: c.muTt)) (T:
            app (app (app (app (app (app encodeDescArgAt I) k) k) refl) S) T)))))
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
                         ttPrim descEncodingCtx eq
                         LiftAtWithEq lowerAtWithEq; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
         lam "l" level (l:
         lam "eqW" (eq level (levelMax l k) k) (eqW:
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
         forall "eqW" (eq level (levelMax l k) k) (_:
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
      let inherit (self) lam forall ann u level app refl
                         descEncodingCtx encodeDescPiAt; in
      ann
        (lam "I" (u 0) (I:
         lam "k" level (k:
          let c = descEncodingCtx I k; in
          lam "S" (u k) (S:
          lam "f" (forall "_" S (_: I)) (f:
          lam "D" c.muTt (D:
            app (app (app (app (app (app (app encodeDescPiAt I) k) k) refl) S) f) D))))))
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
    # structure via a 4-layer `sumElimPrim` cascade. Cascade pattern
    # mirrors iso's `from`: at each layer the Inl branch dispatches
    # to the matched summand's user case body, the Inr branch
    # recurses into the next summand. At depth 4 (plus) the cascade
    # terminates without a sum — the encoded descCon payload is a
    # bare pair carrying the two recursive μ-elements.
    encodeDescElim =
      let
        inherit (self) lam forall ann u level pair fst_ snd_ app
                       descCon descInd sumPrim sumElimPrim
                       inlPrim inrPrim
                       ttPrim unitPrim
                       descEncodingCtx
                       interpHoasAtPrim allHoasAtPrim
                       encodeDescRet encodeDescArg encodeDescRec
                       encodeDescPi encodeDescPlus;
        # `descEncodingCtx`'s `conDescs` and `spineFrom` emit primitive
        # `desc-*` HOAS, so the binary plus combining them in the cascade
        # below must also be primitive. Mirrors `iso` / `interpHoasAt` /
        # `descEncodingCtx`'s `plus = plusPrim` discipline. The encoded
        # `self.plus` would yield `desc-plus-enc { A,B = primitive }`,
        # which leaks primitive descs into `encodeDescPlusTm`'s lam-bound
        # A/B at evaluation.
        plus = self.plusPrim;

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
            # already accumulated the four outer `inrPrim` wrappers.
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
            # to wrap one more `inrPrim lTy rTy`. This makes sumMot's
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
                  sumMot = lam "s" (sumPrim lTy rTy) (s:
                    forall "_rih"
                      (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                        (plus curD restSpine) motiveI ttPrim s)
                      (_: app motive (descCon c.dDesc ttPrim (ctx s))));
                  onInl = lam "r" lTy (r:
                          lam "rih"
                            (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                              curD motiveI ttPrim r) (rih:
                            caseFn ctx r rih));
                  ctx' = s_in: ctx (inrPrim lTy rTy s_in);
                  onInr = lam "r" rTy (r:
                          lam "rih"
                            (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                              restSpine motiveI ttPrim r) (rih:
                            cascade (depthIdx + 1) ctx' r rih));
                in
                  app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

            step = lam "_i" unitPrim (iArg:
                   lam "d" (interpHoasAtPrim c.dDescL unitPrim c.dDesc c.muFam iArg) (d:
                   lam "ih" (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                                c.dDesc motiveI iArg d) (ih:
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

    # interpHoasAtPrim L I D X i  ≡  ⟦D⟧(X) i  as a closed kernel TERM at
    # description-level `L`.
    #   L : Level       the scrutinee description's K-slot — `descArg L`
    #                   / `descPi L` summands inside `D` bind their sort
    #                   `S` at `U(L)`. Threaded into `descElim`'s leading
    #                   `k`, the `descIAt L I` annotation, the `iToU`
    #                   family codomain, and every motive / case-body
    #                   universe site.
    #   I : Type        the index type (any small type)
    #   D : Desc^L I    the description
    #   X : I → U(L)    family of recursive positions at universe L
    #   i : I           target index
    # Mirrors eval/desc.nix's interpF structurally — each binder below
    # lines up with a named closure in that file.
    interpHoasAtPrim = L: I: D: X: i:
      let
        inherit (self) annTrusted lam forall descIAt sigma app eq u sumPrim;
        descLI = descIAt L I;
        iToU = forall "_" I (_: u L);
        # motive : λ(_:Desc^L I). (I → U(L)) → I → U(L)
        motive = lam "_" descLI (_:
                 forall "_" iToU (_:
                 forall "_" I (_: u L)));
        # onRet : λ(j:I). λ(X:I→U(L)). λ(i:I). Lift 0 L (Eq I j i)
        # The `Eq I j i` leaf naturally inhabits `U(level(I))`; for the
        # prelude callers `I = unitPrim : U(0)` so the leaf is at U(0).
        # Wrapping with `LiftAt 0 L` lifts it to U(L) so the case body
        # matches the motive's U(L) codomain. Idempotent at L = 0 — the
        # smart constructor collapses `Lift 0 0 _ A ≡ A`, so prelude
        # code at homogeneous L = 0 is unaffected.
        #
        # Static L=0 fast-path: when L is statically the zero level
        # (Nix-int 0, HOAS levelZero, or kernel `mkLevelZero`), emit the
        # post-collapse form `Eq I j i'` directly. Mirrors the eval-side
        # `interpF` fast-path at `eval/desc.nix:349-404`. At L>0 (or
        # polymorphic L) the principled Lift wrap is retained.
        lIsZero =
          (builtins.isInt L && L == 0)
          || (builtins.isAttrs L
              && ((L._htag or null) == "level-zero"
                  || (L.tag or null) == "level-zero"));
        onRet  = lam "j" I (j:
                 lam "X" iToU (_:
                 lam "i" I (i':
                   if lIsZero
                   then eq I j i'
                   else self.LiftAt self.levelZero L (eq I j i'))));
        # onArg : λ(S:U(L)). λ(T:S→Desc^L I). λ(ih:Π(s:S).(I→U(L))→I→U(L)).
        #           λ(X:I→U(L)). λ(i:I). Σ(s:S). ih s X i
        onArg  = lam "S" (u L) (S:
                 lam "T" (forall "_" S (_: descLI)) (_:
                 lam "ih" (forall "s" S (_:
                            forall "_" iToU (_: forall "_" I (_: u L)))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "s" S (s: app (app (app ih s) X') i'))))));
        # onRec : λ(j:I). λ(D:Desc^L I). λ(ih:(I→U(L))→I→U(L)).
        #           λ(X:I→U(L)). λ(i:I). Σ(_:X j). ih X i
        onRec  = lam "j" I (j:
                 lam "D" descLI (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u L))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (app X' j) (_: app (app ih X') i'))))));
        # onPi : λ(S:U(L)). λ(f:S→I). λ(D:Desc^L I). λ(ih:(I→U(L))→I→U(L)).
        #          λ(X:I→U(L)). λ(i:I). Σ(_:Π(s:S). X(f s)). ih X i
        onPi   = lam "S" (u L) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descLI (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u L))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (forall "s" S (s: app X' (app f s)))
                             (_: app (app ih X') i')))))));
        # onPlus : λ(A:Desc^L I). λ(B:Desc^L I).
        #            λ(ihA:(I→U(L))→I→U(L)). λ(ihB:(I→U(L))→I→U(L)).
        #            λ(X:I→U(L)). λ(i:I). Sum (ihA X i) (ihB X i)
        onPlus = lam "A" descLI (_:
                 lam "B" descLI (_:
                 lam "ihA" (forall "_" iToU (_: forall "_" I (_: u L))) (ihA:
                 lam "ihB" (forall "_" iToU (_: forall "_" I (_: u L))) (ihB:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sumPrim (app (app ihA X') i') (app (app ihB X') i')))))));
      # `descElim`'s INFER rule synthesises its scrutinee, and a bare
      # `retI ttPrim` / plus-coproduct leaf is check-only (no INFER rule
      # for `tt`). Ann-wrap D against `Desc^L I` so the scrutinee position
      # stays inferable for every caller — parallels the CHECK-mode rewire
      # of `mu` at `check/type.nix:75-90`. `interp`'s `onArg` / `onPi`
      # bind `S` at `U(L)`, so the descElimPrim's `k` slot is `L`.
      # Bootstrap-only: this primitive interpreter is consumed by
      # `descDesc`, `iso`, `descEncodingCtx`, and the cascades inside
      # `interpHoasAt` / `allHoasAt` / `encodeDescElim`. User code at
      # the encoded surface uses `interpHoasAt` instead.
      in app (app (self.descElimPrim L motive onRet onArg onRec onPi onPlus (annTrusted D descLI)) X) i;

    # allHoasAtPrim L K I Douter Dsub P i d ≡ All Douter Dsub P i d — the
    # inductive-hypothesis TYPE for d : ⟦Dsub⟧(μ Douter) i, where
    # P : (i:I) → μ Douter i → U(K).
    #
    # Two independent universe parameters:
    #   L : Level   the scrutinee description's K-slot — `descArg L` /
    #               `descPi L` summands inside `Dsub`/`Douter` bind their
    #               sort `S` at `U(L)`. Threaded into `descElim`'s leading
    #               `k`, the `descIAt L I` annotation, and `onArg` /
    #               `onPi`'s `S` binders; `interpHoasAt L` is called for
    #               every interpretation site so the inner descElims line
    #               up at the same `L`.
    #   K : Level   the motive codomain universe — `P j x : U(K)`. The
    #               All result's Σ chain lands in `U(K)` because each
    #               `P j x` component has type `U(K)`. Independent of
    #               `L`: `K` is fixed by the caller's choice of `P`.
    #
    # The motive closes over Douter (and I); the four cases mention
    # Douter only through P's domain shape.
    allHoasAtPrim = L: K: I: Douter: Dsub: P: i: d:
      let
        inherit (self) annTrusted lam forall descIAt sigma app fst_ snd_
                        u unitPrim mu interpHoasAtPrim sumPrim sumElimPrim;
        descLI = descIAt L I;
        # muFam : λi. μ Douter i — the family fed to interpHoasAt as X.
        muFam = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg: forall "_" (mu Douter iArg) (_: u K));
        # motive : λ(D:Desc^L I).
        #   Π(P:(i:I) → μ Douter i → U(K)). Π(i:I). Π(d:⟦D⟧(μ Douter) i). U(K)
        motive = lam "_" descLI (Dm:
                 forall "P" pTy (_:
                 forall "i" I (iArg:
                 forall "d" (interpHoasAtPrim L I Dm muFam iArg) (_: u K))));
        # onRet : λj λP λi λd. Lift 0 K Unit
        # The `All`-result at a `retI` leaf is trivially `Unit`; wrapping
        # in `LiftAt 0 K` lifts the U(0) Unit type to U(K) so the case
        # body matches the motive's U(K) codomain. Idempotent at K = 0.
        onRet  = lam "j" I (_:
                 lam "P" pTy (_:
                 lam "i" I (_:
                 lam "d" unitPrim (_: self.LiftAt self.levelZero K unitPrim))));
        # onArg : λS λT λihA λP λi λd. ihA (fst d) P i (snd d)
        onArg  = lam "S" (u L) (S:
                 lam "T" (forall "_" S (_: descLI)) (T:
                 lam "ihA" (forall "s" S (s:
                            forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAtPrim L I (app T s) muFam iArg) (_: u K))))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "s" S (s: interpHoasAtPrim L I (app T s) muFam iArg)) (d2:
                   app (app (app (app ihA (fst_ d2)) P2) iArg) (snd_ d2)))))));
        # onRec : λj λD λihA λP λi λd. Σ(_: P j (fst d)). ihA P i (snd d)
        onRec  = lam "j" I (j:
                 lam "D" descLI (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAtPrim L I D2 muFam iArg) (_: u K)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (mu Douter j) (_: interpHoasAtPrim L I D2 muFam iArg)) (d2:
                   sigma "_" (app (app P2 j) (fst_ d2)) (_:
                     app (app (app ihA P2) iArg) (snd_ d2))))))));
        # onPi : λS λf λD λihA λP λi λd.
        #          Σ(_: Π(s:S). P (f s) (fst d s)). ihA P i (snd d)
        onPi   = lam "S" (u L) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descLI (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAtPrim L I D2 muFam iArg) (_: u K)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                    (_: interpHoasAtPrim L I D2 muFam iArg)) (d2:
                   sigma "_"
                     (forall "s" S (s:
                       app (app P2 (app f s)) (app (fst_ d2) s)))
                     (_: app (app (app ihA P2) iArg) (snd_ d2)))))))));
        # onPlus : λA λB λihA λihB λP λi λd. sumElim on d: inl a → ihA P i a, inr b → ihB P i b.
        # d : Sum (⟦A⟧ μFam i) (⟦B⟧ μFam i) by interp of plus (kernel Sum).
        onPlus = lam "A" descLI (A:
                 lam "B" descLI (B:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAtPrim L I A muFam iArg) (_: u K)))) (ihA:
                 lam "ihB" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAtPrim L I B muFam iArg) (_: u K)))) (ihB:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sumPrim (interpHoasAtPrim L I A muFam iArg)
                                  (interpHoasAtPrim L I B muFam iArg)) (d2:
                   sumElimPrim (interpHoasAtPrim L I A muFam iArg)
                           (interpHoasAtPrim L I B muFam iArg)
                           (lam "_" (sumPrim (interpHoasAtPrim L I A muFam iArg)
                                             (interpHoasAtPrim L I B muFam iArg))
                              (_: u K))
                           (lam "a" (interpHoasAtPrim L I A muFam iArg) (a:
                             app (app (app ihA P2) iArg) a))
                           (lam "b" (interpHoasAtPrim L I B muFam iArg) (b:
                             app (app (app ihB P2) iArg) b))
                           d2)))))));
      # Bootstrap-only: this primitive interpreter is consumed by
      # `descDesc`, `iso`, `descEncodingCtx`, and the cascades inside
      # `interpHoasAt` / `allHoasAt` / `encodeDescElim`. User code at
      # the encoded surface uses `allHoasAt` instead. The descElimPrim's
      # `k` slot is `L` (sort universe), motive codomain `U(K)` is
      # carried by the motive itself.
      in app (app (app (self.descElimPrim L motive onRet onArg onRec onPi onPlus (annTrusted Dsub descLI)) P) i) d;

    # interpHoasAt L I D X i ≡ ⟦D⟧(X) i for D : μ⊤(descDesc I L) tt.
    # Implemented via descInd over c.dDesc with a 4-layer sumElimPrim
    # cascade dispatching depthIdx 0..3 to ret/arg/rec/pi and depthIdx==4
    # to plus. Each case builds qTy = (I→U(L)) → I → U(L) per
    # interpHoasAtPrim's onRet/onArg/onRec/onPi/onPlus templates; the
    # outer body applies the resulting qTy to X then i to land in U(L).
    interpHoasAt = L: I: D: X: i:
      let
        inherit (self) lam forall app pair fst_ snd_ sigma eq u
                       descInd sumPrim sumElimPrim plusPrim
                       ttPrim unitPrim
                       descEncodingCtx
                       interpHoasAtPrim allHoasAtPrim;
        plus = plusPrim;
        c = descEncodingCtx I L;
        iToU = forall "_" I (_: u L);
        qTy = forall "_" iToU (_: forall "_" I (_: u L));
        # descInd motive at I=⊤: λ_i.λx. qTy. Constant in _i,x because
        # qTy doesn't depend on the scrutinee or its index.
        motiveI = lam "_i" unitPrim (_:
                  lam "x" c.muTt (_: qTy));

        # Static L=0 fast-path mirrors interpHoasAtPrim's lIsZero check —
        # collapses `LiftAt 0 0 (Eq I j i')` to bare `Eq I j i'` at the
        # descRet leaf.
        lIsZero =
          (builtins.isInt L && L == 0)
          || (builtins.isAttrs L
              && ((L._htag or null) == "level-zero"
                  || (L.tag or null) == "level-zero"));

        cascade = depthIdx: dCur: ihCur:
          if depthIdx == 4 then
            let A   = fst_ dCur;
                B   = fst_ (snd_ dCur);
                ihA = fst_ ihCur;
                ihB = fst_ (snd_ ihCur);
            in
              lam "X" iToU (X':
              lam "i" I (i':
                sumPrim (app (app ihA X') i') (app (app ihB X') i')))
          else
            let
              curD      = builtins.elemAt c.conDescs depthIdx;
              restSpine = c.spineFrom (depthIdx + 1);
              lTy       = c.interpAt curD;
              rTy       = c.interpAt restSpine;
              sumMot = lam "s" (sumPrim lTy rTy) (s:
                forall "_rih"
                  (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                    (plus curD restSpine) motiveI ttPrim s)
                  (_: qTy));
              onInl = lam "r" lTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          curD motiveI ttPrim r) (rih:
                        if depthIdx == 0 then
                          let j = fst_ r; in
                          lam "X" iToU (X':
                          lam "i" I (i':
                            if lIsZero
                            then eq I j i'
                            else self.LiftAt self.levelZero L (eq I j i')))
                        else if depthIdx == 1 then
                          let S    = fst_ r;
                              T    = fst_ (snd_ r);
                              ihFn = fst_ rih;
                          in
                          lam "X" iToU (X':
                          lam "i" I (i':
                            sigma "s" S (s:
                              app (app (app ihFn s) X') i')))
                        else if depthIdx == 2 then
                          let j   = fst_ r;
                              ihD = fst_ rih;
                          in
                          lam "X" iToU (X':
                          lam "i" I (i':
                            sigma "_" (app X' j) (_:
                              app (app ihD X') i')))
                        else
                          let S   = fst_ r;
                              f   = fst_ (snd_ r);
                              ihD = fst_ rih;
                          in
                          lam "X" iToU (X':
                          lam "i" I (i':
                            sigma "_" (forall "s" S (s: app X' (app f s)))
                                      (_: app (app ihD X') i')))));
              onInr = lam "r" rTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          restSpine motiveI ttPrim r) (rih:
                        cascade (depthIdx + 1) r rih));
            in
              app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoasAtPrim c.dDescL unitPrim c.dDesc c.muFam iArg) (d:
               lam "ih" (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                            c.dDesc motiveI iArg d) (ih:
                 cascade 0 d ih)));
      in
        app (app (descInd c.dDesc motiveI step ttPrim D) X) i;

    # allHoasAt L K I Douter Dsub P i d ≡ All Douter Dsub P i d for
    # Dsub : μ⊤(descDesc I L) tt. Mirrors allHoasAtPrim's per-summand
    # templates, dispatched via descInd-over-descDesc cascade; per-case
    # bodies build U(K)-typed All-witnesses. Motive's d-binder type uses
    # interpHoasAtPrim — its elaborated mkDescElim Tm flows through the
    # desc-* CHECK rules' encoder retarget for constructors, and the
    # desc-elim INFER rule's §6.6 unfolding for the eliminator scrut.
    allHoasAt = L: K: I: Douter: Dsub: P: i: d:
      let
        inherit (self) lam forall app pair fst_ snd_ sigma
                       u unitPrim mu
                       descInd sumPrim sumElimPrim plusPrim inrPrim
                       ttPrim
                       descEncodingCtx
                       interpHoasAtPrim allHoasAtPrim;
        plus = plusPrim;
        c = descEncodingCtx I L;
        muFamOuter = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg:
              forall "_" (mu Douter iArg) (_: u K));

        # descInd motive at scrut Dm:
        #   λ_i.λDm. (P:pTy) → (i:I) → (d:⟦Dm⟧(μ Douter) i) → U(K)
        motiveI = lam "_i" unitPrim (_:
                  lam "Dm" c.muTt (Dm:
                    forall "P" pTy (_:
                    forall "i" I (iArg:
                    forall "d" (interpHoasAtPrim L I Dm muFamOuter iArg) (_: u K)))));

        # Cascade layer at depthIdx in {0..4}. `dCur` is the matched
        # descCon payload at this layer (a Sum at 0..3, a Pair at 4);
        # `ihCur` is the corresponding All-witness. `ctx` reconstructs
        # the OUTER payload from this layer's inner shape — at the
        # outermost call `ctx = id`; at each Inr descent it extends to
        # wrap one more `inrPrim lTy rTy`. This makes sumMot's
        # `descCon c.dDesc tt (ctx s)` well-typed at every depth K
        # because `ctx s : interpAt c.dDesc` by construction. Mirrors
        # `encodeDescElim`'s cascade at `hoas/desc.nix:1281-1312`.
        cascade = depthIdx: ctx: dCur: ihCur:
          if depthIdx == 4 then
            let A   = fst_ dCur;
                B   = fst_ (snd_ dCur);
                ihA = fst_ ihCur;
                ihB = fst_ (snd_ ihCur);
            in
              # plus case: λP λi λd. sumElim on d. d : Sum (⟦A⟧) (⟦B⟧) by
              # interp of plus. Per-branch invokes the corresponding ih.
              lam "P" pTy (P':
              lam "i" I (iArg:
              lam "d" (sumPrim (interpHoasAtPrim L I A muFamOuter iArg)
                               (interpHoasAtPrim L I B muFamOuter iArg)) (d':
                sumElimPrim
                  (interpHoasAtPrim L I A muFamOuter iArg)
                  (interpHoasAtPrim L I B muFamOuter iArg)
                  (lam "_" (sumPrim (interpHoasAtPrim L I A muFamOuter iArg)
                                    (interpHoasAtPrim L I B muFamOuter iArg))
                     (_: u K))
                  (lam "a" (interpHoasAtPrim L I A muFamOuter iArg) (a:
                    app (app (app ihA P') iArg) a))
                  (lam "b" (interpHoasAtPrim L I B muFamOuter iArg) (b:
                    app (app (app ihB P') iArg) b))
                  d')))
          else
            let
              curD      = builtins.elemAt c.conDescs depthIdx;
              restSpine = c.spineFrom (depthIdx + 1);
              lTy       = c.interpAt curD;
              rTy       = c.interpAt restSpine;
              # Per-summand result type: motive applied to descCon's
              # encoded summand reconstructed via `ctx`. At depthIdx K,
              # `s : sumPrim lTy rTy` lives K layers deep in the OUTER
              # inrPrim chain; `ctx s` rebuilds the canonical OUTER
              # payload so `descCon c.dDesc tt (ctx s) : muTt` typechecks.
              qTyAt = s:
                forall "P" pTy (_:
                forall "i" I (iArg:
                forall "d" (interpHoasAtPrim L I
                              (self.descCon c.dDesc ttPrim (ctx s))
                              muFamOuter iArg) (_: u K)));
              sumMot = lam "s" (sumPrim lTy rTy) (s:
                forall "_rih"
                  (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                    (plus curD restSpine) motiveI ttPrim s)
                  (_: qTyAt s));
              onInl = lam "r" lTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          curD motiveI ttPrim r) (rih:
                        if depthIdx == 0 then
                          # ret: λP λi λd. Lift 0 K Unit
                          lam "P" pTy (_:
                          lam "i" I (_:
                          lam "d" unitPrim (_:
                            self.LiftAt self.levelZero K unitPrim)))
                        else if depthIdx == 1 then
                          # arg: λP λi λd:Σ(s:S).⟦Ts⟧. ihA (fst d) P i (snd d)
                          let S    = fst_ r;
                              T    = fst_ (snd_ r);
                              ihFn = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "i" I (iArg:
                          lam "d" (sigma "s" S (s:
                                     interpHoasAtPrim L I (app T s) muFamOuter iArg))
                            (d':
                            app (app (app (app ihFn (fst_ d')) P') iArg) (snd_ d'))))
                        else if depthIdx == 2 then
                          # rec: λP λi λd:Σ(_:μ Douter j).⟦D2⟧.
                          #   Σ(_:P j (fst d)). ihD P i (snd d)
                          let j   = fst_ r;
                              D2  = fst_ (snd_ r);
                              ihD = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "i" I (iArg:
                          lam "d" (sigma "_" (mu Douter j)
                                     (_: interpHoasAtPrim L I D2 muFamOuter iArg)) (d':
                            sigma "_" (app (app P' j) (fst_ d')) (_:
                              app (app (app ihD P') iArg) (snd_ d')))))
                        else
                          # pi: λP λi λd:Σ(_:Π(s:S).μ Douter (f s)).⟦D2⟧.
                          #   Σ(_:Π(s:S). P (f s) (fst d s)). ihD P i (snd d)
                          let S   = fst_ r;
                              f   = fst_ (snd_ r);
                              D2  = fst_ (snd_ (snd_ r));
                              ihD = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "i" I (iArg:
                          lam "d" (sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                     (_: interpHoasAtPrim L I D2 muFamOuter iArg)) (d':
                            sigma "_"
                              (forall "s" S (s:
                                app (app P' (app f s)) (app (fst_ d') s)))
                              (_: app (app (app ihD P') iArg) (snd_ d')))))));
              ctx' = s_in: ctx (inrPrim lTy rTy s_in);
              onInr = lam "r" rTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          restSpine motiveI ttPrim r) (rih:
                        cascade (depthIdx + 1) ctx' r rih));
            in
              app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoasAtPrim c.dDescL unitPrim c.dDesc c.muFam iArg) (dArg:
               lam "ih" (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                            c.dDesc motiveI iArg dArg) (ih:
                 cascade 0 (s: s) dArg ih)));
      in
        app (app (app (descInd c.dDesc motiveI step ttPrim Dsub) P) i) d;

    # everywhereHoasAt L K I Douter Dsub P ih i d builds the All-witness
    # VALUE for d : ⟦Dsub⟧(μ Douter) i for Dsub : μ⊤(descDesc I L) tt.
    # Mirrors evOnRet/Arg/Rec/Pi/Plus from eval/desc.nix:633-735 in
    # HOAS — vDescIndF's internal everywhere call routes through this
    # encoded-aware form. The motive's codomain uses allHoasAt for the
    # All-witness type — recursive but lazy.
    everywhereHoasAt = L: K: I: Douter: Dsub: P: ih: i: d:
      let
        inherit (self) lam forall app pair fst_ snd_
                       u unitPrim mu
                       descInd sumPrim sumElimPrim plus
                       ttPrim
                       descEncodingCtx
                       interpHoasAtPrim allHoasAtPrim allHoasAt;
        c = descEncodingCtx I L;
        muFamOuter = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg:
              forall "_" (mu Douter iArg) (_: u K));
        ihTy = forall "j" I (j:
               forall "x" (mu Douter j) (x:
                 app (app P j) x));

        # descInd motive at scrut Dm:
        #   λ_i.λDm. (P:pTy) → (ih:ihTy) → (i:I) → (d:⟦Dm⟧). allHoasAt L K I Douter Dm P i d
        motiveI = lam "_i" unitPrim (_:
                  lam "Dm" c.muTt (Dm:
                    forall "P" pTy (Pm:
                    forall "ih" ihTy (ihm:
                    forall "i" I (iArg:
                    forall "d" (interpHoasAtPrim L I Dm muFamOuter iArg) (dm:
                      allHoasAt L K I Douter Dm Pm iArg dm))))));

        cascade = depthIdx: dCur: ihCur:
          if depthIdx == 4 then
            let A    = fst_ dCur;
                B    = fst_ (snd_ dCur);
                ihEA = fst_ ihCur;
                ihEB = fst_ (snd_ ihCur);
            in
              # plus case: λP λih λi λd. sumElim on d.
              lam "P" pTy (P':
              lam "ih" ihTy (ih':
              lam "i" I (iArg:
              lam "d" (sumPrim (interpHoasAtPrim L I A muFamOuter iArg)
                               (interpHoasAtPrim L I B muFamOuter iArg)) (d':
                sumElimPrim
                  (interpHoasAtPrim L I A muFamOuter iArg)
                  (interpHoasAtPrim L I B muFamOuter iArg)
                  (lam "_" (sumPrim (interpHoasAtPrim L I A muFamOuter iArg)
                                    (interpHoasAtPrim L I B muFamOuter iArg))
                     (s: allHoasAtPrim L K I Douter (plus A B) P' iArg s))
                  (lam "a" (interpHoasAtPrim L I A muFamOuter iArg) (a:
                    app (app (app (app ihEA P') ih') iArg) a))
                  (lam "b" (interpHoasAtPrim L I B muFamOuter iArg) (b:
                    app (app (app (app ihEB P') ih') iArg) b))
                  d'))))
          else
            let
              curD      = builtins.elemAt c.conDescs depthIdx;
              restSpine = c.spineFrom (depthIdx + 1);
              lTy       = c.interpAt curD;
              rTy       = c.interpAt restSpine;
              # Result type at this cascade level — motive applied to
              # descCon dDesc tt s, i.e., ΠP.Πih.Πi.Π(d:⟦descCon⟧). allHoasAt@scrut.
              qTyAt = s:
                forall "P" pTy (Pm:
                forall "ih" ihTy (_:
                forall "i" I (iArg:
                forall "d" (interpHoasAtPrim L I
                              (self.descCon c.dDesc ttPrim s)
                              muFamOuter iArg) (dm:
                  allHoasAt L K I Douter
                    (self.descCon c.dDesc ttPrim s) Pm iArg dm))));
              sumMot = lam "s" (sumPrim lTy rTy) (s:
                forall "_rih"
                  (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                    (plus curD restSpine) motiveI ttPrim s)
                  (_: qTyAt s));
              onInl = lam "r" lTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          curD motiveI ttPrim r) (rih:
                        if depthIdx == 0 then
                          # ret: λP λih λi λd. tt
                          lam "P" pTy (_:
                          lam "ih" ihTy (_:
                          lam "i" I (_:
                          lam "d" unitPrim (_: ttPrim))))
                        else if depthIdx == 1 then
                          # arg: λP λih λi λd. ihE (fst d) P ih i (snd d)
                          let S    = fst_ r;
                              T    = fst_ (snd_ r);
                              ihE  = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "ih" ihTy (ih':
                          lam "i" I (iArg:
                          lam "d" (self.sigma "s" S (s:
                                     interpHoasAtPrim L I (app T s) muFamOuter iArg))
                            (d':
                            app (app (app (app (app ihE (fst_ d')) P') ih') iArg)
                                (snd_ d')))))
                        else if depthIdx == 2 then
                          # rec: λP λih λi λd. pair (ih j (fst d)) (ihE P ih i (snd d))
                          let j   = fst_ r;
                              D2  = fst_ (snd_ r);
                              ihE = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "ih" ihTy (ih':
                          lam "i" I (iArg:
                          lam "d" (self.sigma "_" (mu Douter j)
                                     (_: interpHoasAtPrim L I D2 muFamOuter iArg)) (d':
                            pair (app (app ih' j) (fst_ d'))
                                 (app (app (app (app ihE P') ih') iArg) (snd_ d'))))))
                        else
                          # pi: λP λih λi λd.
                          #   pair (λs:S. ih (f s) (fst d s)) (ihE P ih i (snd d))
                          let S   = fst_ r;
                              f   = fst_ (snd_ r);
                              D2  = fst_ (snd_ (snd_ r));
                              ihE = fst_ rih;
                          in
                          lam "P" pTy (P':
                          lam "ih" ihTy (ih':
                          lam "i" I (iArg:
                          lam "d" (self.sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                     (_: interpHoasAtPrim L I D2 muFamOuter iArg)) (d':
                            pair
                              (lam "s" S (s:
                                app (app ih' (app f s)) (app (fst_ d') s)))
                              (app (app (app (app ihE P') ih') iArg) (snd_ d'))))))));
              onInr = lam "r" rTy (r:
                      lam "rih"
                        (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                          restSpine motiveI ttPrim r) (rih:
                        cascade (depthIdx + 1) r rih));
            in
              app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoasAtPrim c.dDescL unitPrim c.dDesc c.muFam iArg) (dArg:
               lam "ih" (allHoasAtPrim c.dDescL c.dDescL unitPrim c.dDesc
                            c.dDesc motiveI iArg dArg) (ihArg:
                 cascade 0 dArg ihArg)));
      in
        app (app (app (app (descInd c.dDesc motiveI step ttPrim Dsub) P) ih) i) d;

    # ─── Closed Tm/Val triples for the new public bindings ───
    # Pattern parallels descDescTm / descDescVal at desc.nix:809-810.
    # Each closed form abstracts over all dependencies as outer lams,
    # then elaborates and evaluates once at module init. Kernel-level
    # consumers in eval/desc.nix's wrappers apply via vAppF chains.

    interpHoasAtClosed =
      let inherit (self) lam forall u level ann; in
      ann
        (lam "L" level (L:
         lam "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          lam "D" c.muTt (D:
          lam "X" (forall "_" I (_: u L)) (X:
          lam "i" I (i:
            self.interpHoasAt L I D X i))))))
        (forall "L" level (L:
         forall "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          forall "D" c.muTt (_:
          forall "X" (forall "_" I (_: u L)) (_:
          forall "i" I (_: u L))))));

    interpHoasAtTm = self.elab self.interpHoasAtClosed;

    allHoasAtClosed =
      let inherit (self) lam forall u level ann mu unitPrim; in
      ann
        (lam "L" level (L:
         lam "K" level (K:
         lam "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          lam "Douter" (forall "_" I (_: c.descK)) (Douter:
          lam "Dsub" c.muTt (Dsub:
          lam "P" (forall "i" I (iArg:
                    forall "_" (mu Douter iArg) (_: u K))) (P:
          lam "i" I (i:
          lam "d" (self.interpHoasAtPrim L I Dsub
                    (lam "_i" I (iArg: mu Douter iArg)) i) (d:
            self.allHoasAt L K I Douter Dsub P i d)))))))))
        (forall "L" level (L:
         forall "K" level (K:
         forall "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          forall "Douter" (forall "_" I (_: c.descK)) (Douter:
          forall "Dsub" c.muTt (_:
          forall "P" (forall "i" I (iArg:
                       forall "_" (mu Douter iArg) (_: u K))) (_:
          forall "i" I (_:
          forall "d" (u 0) (_: u K))))))))); # placeholder for d's interp-type

    allHoasAtTm = self.elab self.allHoasAtClosed;

    everywhereHoasAtClosed =
      let inherit (self) lam forall u level ann mu unitPrim; in
      ann
        (lam "L" level (L:
         lam "K" level (K:
         lam "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          lam "Douter" (forall "_" I (_: c.descK)) (Douter:
          lam "Dsub" c.muTt (Dsub:
          lam "P" (forall "i" I (iArg:
                    forall "_" (mu Douter iArg) (_: u K))) (P:
          lam "ih" (forall "j" I (j:
                    forall "x" (mu Douter j) (x:
                      self.app (self.app P j) x))) (ih:
          lam "i" I (i:
          lam "d" (self.interpHoasAtPrim L I Dsub
                    (lam "_i" I (iArg: mu Douter iArg)) i) (d:
            self.everywhereHoasAt L K I Douter Dsub P ih i d))))))))))
        (forall "L" level (L:
         forall "K" level (K:
         forall "I" (u 0) (I:
          let c = self.descEncodingCtx I L; in
          forall "Douter" (forall "_" I (_: c.descK)) (Douter:
          forall "Dsub" c.muTt (_:
          forall "P" (forall "i" I (iArg:
                       forall "_" (mu Douter iArg) (_: u K))) (Pa:
          forall "ih" (forall "j" I (j:
                       forall "x" (mu Douter j) (x:
                         self.app (self.app Pa j) x))) (_:
          forall "i" I (_:
          forall "d" (u 0) (_: u 0))))))))));

    everywhereHoasAtTm = self.elab self.everywhereHoasAtClosed;

    interpHoasAtVal = fx.tc.eval.eval [] self.interpHoasAtTm;
    allHoasAtVal = fx.tc.eval.eval [] self.allHoasAtTm;
    everywhereHoasAtVal = fx.tc.eval.eval [] self.everywhereHoasAtTm;
    encodeDescElimVal = fx.tc.eval.eval [] self.encodeDescElimTm;
  };
}
