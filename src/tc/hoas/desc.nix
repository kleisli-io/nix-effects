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
{ self, fx, api, ... }:

{
  scope = {
    natDesc = api.leaf {
      description = "natDesc: prelude `Nat` description — `descRet + descRec descRet`; the canonical two-summand description of natural numbers as zero + succ(Nat).";
      signature = "natDesc : Hoas";
      value = self.NatDT.D;
    };
    listDescAt = k: elem:
      let kTm = if builtins.isInt k then self.natToLevel k else k; in
      self.app (self.app self.ListDT.D kTm) elem;
    listDesc = api.leaf {
      description = "listDesc: prelude `List` description constructor — `listDesc A` produces the two-summand description `descRet + descArg A (_: descRec descRet)` of `List A`.";
      signature = "listDesc : Hoas -> Hoas";
      value = elem: self.listDescAt self.levelZero elem;
    };
    sumDescAt = k: l: r:
      let kTm = if builtins.isInt k then self.natToLevel k else k; in
      self.app (self.app (self.app self.SumDT.D kTm) l) r;
    sumDesc = api.leaf {
      description = "sumDesc: prelude `Sum` description constructor — `sumDesc A B` produces the two-summand description `descArg A (_: descRet) + descArg B (_: descRet)` of `Sum A B`.";
      signature = "sumDesc : Hoas -> Hoas -> Hoas";
      value = l: r: self.sumDescAt self.levelZero l r;
    };

    # descDesc : Π(iLev : Level)(I : U(iLev))(k : Level).
    #             Desc^(suc (max k iLev)) ⊤
    # I- and k-parameterised description-of-descriptions; outer iLev
    # carries the universe of I. Five summands mirror `Desc I k`'s
    # grammar at the homogeneous-l image:
    #   ret  — Π(i : I). ⊤
    #   arg  — Π(S : U(k)). Π(T : S → ⊤). ⊤
    #   rec  — Π(i : I). Π(_ : ⊤). ⊤
    #   pi   — Π(S : U(k)). Π(f : S → I). Π(_ : ⊤). ⊤
    #   plus — Π(_ : ⊤). Π(_ : ⊤). ⊤
    # ret / rec summands prefix `descArgAt iLev (suc (max k iLev)) I` to
    # carry the I-typed leaf index. The pi summand carries
    # `descArgAt (max k iLev) (suc (max k iLev)) (S → I) (_f: ...)` to
    # encode the source's `f : S → I` selector at the joined sort
    # universe. Bound witnesses discharge via convLevel: max with the
    # outer suc collapses by the semilattice quotient. At iLev=0,
    # `levelMaxOpt k 0 = k` and `levelMaxOpt 0 iLev = iLev`, so the body
    # is syntactically identical to the pre-lift ⊤-slice shape.
    # Heterogeneous formation (per-summand `(l, eq, S:U(l))`) is allowed
    # but not encoded here — `ind`-over-`descDesc` plus Lift discipline
    # at case bodies closes the heterogeneous-elimination gap uniformly.
    descDesc = api.leaf {
      description = "descDesc: levitated description-of-descriptions — `descDesc I k` is the description whose μ-carrier is `Desc^k I`; foundational for description encoding.";
      signature = "descDesc : Hoas -> Level -> Hoas  -- I, k";
      doc = ''
        The plus-tree of `descDesc` has five summands corresponding
        to the description constructors (`retI`, `descArg`, `recI`,
        `piI`, `plusI`). Every encoded HOAS description elaborates
        through `descDesc` so each `VDescCon` value carries its
        constructor tag explicitly. Universe-polymorphic over `k`.
      '';
      value =
        let inherit (self) lam forall annTrusted level levelSuc levelMaxOpt
          u descAt;
        in
        annTrusted
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let
                  sk = levelSuc (levelMaxOpt k iLev);
                  c = self.descEncodingCtx iLev self.unitPrim sk;
                  inherit (c) plus descRet descArgAt descRec descPiAt;
                in
                plus (descArgAt iLev sk I (_i: descRet))
                  (plus (descArgAt (levelSuc k) sk (u k) (S: descPiAt k sk S descRet))
                    (plus (descArgAt iLev sk I (_i: descRec descRet))
                      (plus
                        (descArgAt (levelSuc k) sk (u k) (S:
                          descArgAt (levelMaxOpt k iLev) sk
                            (forall "_" S (_: I))
                            (_f:
                              descRec descRet)))
                        (descRec (descRec descRet)))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k: descAt (levelSuc (levelMaxOpt k iLev))))));
    };

    # Pre-elaborated Nat description for the Nat type former.
    natDescTm = api.leaf {
      description = "natDescTm: pre-elaborated `Nat` description term — closed kernel `Tm` encoding `natDesc`; used by the kernel where the HOAS form would re-elaborate.";
      signature = "natDescTm : Tm";
      value = self.elab self.natDesc;
    };

    # Pre-elaborated descDesc Tm + its evaluated VLam form. The Val is
    # consumed by the conv unfolding rule `Desc I k ≡ μ ⊤ (descDesc I
    # k) tt` (tc/conv.nix): vApp on v.I and v.level reduces it to the
    # finite description tree the rule compares against. Module init
    # is cycle-safe because `descDescApp` tags the recursive reference
    # before conv/quote can force the next `.D` layer.
    descDescTm = api.leaf {
      description = "descDescTm: pre-elaborated `descDesc` term — closed kernel `Tm` form usable directly by kernel rules that need the description-of-descriptions without re-elaborating.";
      signature = "descDescTm : Tm";
      value = self.elab self.descDesc;
    };
    descDescVal = api.leaf {
      description = "descDescVal: pre-evaluated `descDesc` value — the kernel `Val` form, ready for `interpD` / `descInd` consumption without re-evaluation.";
      signature = "descDescVal : Val";
      value = fx.tc.eval.eval [ ] self.descDescTm;
    };

    # Reserved surface identifier for the prelude
    # description-of-descriptions. The elaborator dispatches
    # `_htag = "desc-desc"` to `self.descDescTm`, so call sites that
    # emit `__descDesc` references avoid re-walking the descDesc HOAS
    # tree on every use. The `__` prefix marks the name as
    # kernel-internal — surface code addresses descDesc through this
    # canonical token.
    __descDesc = api.leaf {
      description = "__descDesc: private internal-use alias for `descDesc` — exposed for the encoder cascade; surface code should use `descDesc`.";
      signature = "__descDesc : Hoas -> Level -> Hoas";
      value = { _htag = "desc-desc"; };
    };

    # Identity-tagged HOAS form of `descDesc iLev I L`. Elaborates to the
    # `desc-desc-app` Tm; its eval rule produces a VDescCon stamped with
    # `_canonRef.params = [iLev, I, L]`. Stand-in for
    # `app (app (app descDesc iLev) I) L` at call sites that need conv/quote
    # to decide equality on the tag rather than walk `.D`.
    descDescAppAtI = api.leaf {
      description = "descDescAppAtI: applied `descDesc` form with explicit index-universe level — `descDescAppAtI iLev I k` evaluates to a canonical stamp with params `[iLev, I, k]`.";
      signature = "descDescAppAtI : Level -> Hoas -> Level -> Hoas";
      value = iLev: I: L:
        { _htag = "desc-desc-app"; inherit iLev I L; };
    };
    descDescApp = api.leaf {
      description = "descDescApp: applied `descDesc` form — `descDescApp I k` produces `descDesc I k` as a closed Tm; convenience for sites that need the pre-applied form.";
      signature = "descDescApp : Hoas -> Level -> Hoas";
      value = I: L: self.descDescAppAtI self.levelZero I L;
    };

    # Generic identity-tagged HOAS form. `canonApp id params body` is a
    # stand-in for `app … (app body p_1) … p_n` at call sites that need
    # conv/quote to decide equality on the `(id, params)` tag rather
    # than walk `.D`. The eval rule applies `body` to each param in
    # order and stamps the resulting `VDescCon` with
    # `_canonRef = { id; params; }`. Use this to add cycle-safe outer
    # references for user-defined recursive descriptions (freer monads,
    # FTCQueues, ...) without coupling the kernel to each id.
    canonApp = api.leaf {
      description = "canonApp: generic identity-tagged HOAS application — `canonApp id params body` produces a `VDescCon` stamped with `_canonRef = { id; params; }` at eval time, so conv/quote short-circuit on the canonical identity instead of forcing the recursive `.D` slot. Use to add cycle-safe outer references for user-defined recursive descriptions (freer monads, FTCQueues, ...).";
      signature = "canonApp : String -> [Hoas] -> Hoas -> Hoas";
      value = id: params: body:
        { _htag = "canon-app"; inherit id params body; };
    };

    # Per-(iLev, I, k) HOAS encoding context for descDesc-encoded μ-trees.
    # Single source of truth for the descDesc summand layout, the
    # plus-tree spine, the right-associated `encodeTag` pathing, and
    # the descRet-leaf `Lift 0 (suc k) (Eq ⊤ tt tt)` discipline.
    # Consumed by the `iso` bundle's `to` side and by the standalone
    # `encodeDesc{Ret,Arg,Rec,Pi,Plus}` encoders.
    #
    # Inputs `iLev : Level`, `I : U(iLev)`, and `k : Level` are HOAS
    # terms — typically the bound variables of an outer
    # `lam "iLev" ... lam "I" ... lam "k" ...` chain. The returned
    # record's fields close over those terms. The aliases produce HOAS
    # at I = unitPrim (whose universe is 0), so they keep the default
    # `iLev = levelZero` slot; the outer `iLev` parameter is consumed
    # only by `conDescs`, which describes the descDesc summands one
    # level above context.k.
    descEncodingCtx = iLev: I: kRaw:
      let
        inherit (self) lam forall ttPrim unitPrim
          levelZero levelSuc levelMaxOpt u bootEq bootRefl descIAt
          LiftAt liftAt lowerAt mu interpD
          encodeTagAt;
        plus = A: B: self.plusI self.unitPrim sk A B;
        descRet = self.retI self.unitPrim sk self.ttPrim;
        descArg = kArg: S: T: self.descArg self.unitPrim kArg S T;
        descArgAt = lArg: kArg: S: T:
          self.descArgAt self.unitPrim lArg kArg S T;
        descRec = D: self.recI self.unitPrim sk self.ttPrim D;
        descPiAt = lArg: kArg: S: D:
          self.descPiAt lArg kArg S D;
        # Coerce a Nix-meta `Int` `kRaw` into a `level-zero`/`level-suc`
        # HOAS form so the shared level is uniform.
        k =
          if builtins.isInt kRaw
          then if kRaw == 0 then levelZero
          else
            builtins.foldl' (acc: _: levelSuc acc) levelZero
              (builtins.genList (x: x) kRaw)
          else kRaw;
        sk = levelSuc (levelMaxOpt k iLev);
        dDesc = self.descDescAppAtI iLev I k;
        muTt = mu dDesc ttPrim;
        muFam = lam "_i" unitPrim (iArg: mu dDesc iArg);
        dDescL = sk;
        descK = descIAt k I;
        conDescs = [
          (descArgAt iLev sk I (_i: descRet))
          (descArgAt (levelSuc k) sk (u k) (S: descPiAt k sk S descRet))
          (descArgAt iLev sk I (_i: descRec descRet))
          (descArgAt (levelSuc k) sk (u k) (S:
            descArgAt (levelMaxOpt k iLev) sk (forall "_" S (_: I)) (_f:
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
        liftIndex = x: liftAt iLev dDescL I x;
        lowerIndex = x: lowerAt iLev dDescL I x;
        liftSort = S: liftAt (levelSuc k) dDescL (u k) S;
        lowerSort = x: lowerAt (levelSuc k) dDescL (u k) x;
        payloadTyAtK = S: LiftAt k dDescL S;
        liftPayloadAtK = S: x: liftAt k dDescL S x;
        lowerPayloadAtK = S: x: lowerAt k dDescL S x;
        joinTy = S: LiftAt (levelMaxOpt k iLev) dDescL S;
        liftJoin = S: x: liftAt (levelMaxOpt k iLev) dDescL S x;
        lowerJoin = S: x: lowerAt (levelMaxOpt k iLev) dDescL S x;
      in
      {
        inherit dDesc muTt muFam dDescL descK
          plus descRet descArg descArgAt descRec descPiAt
          conDescs spineFrom encodeAt interpAt
          eqLeafTy liftLeaf lowerLeaf liftedRefl
          liftIndex lowerIndex liftSort lowerSort
          payloadTyAtK liftPayloadAtK lowerPayloadAtK
          joinTy liftJoin lowerJoin sk;
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

    encodeDescRet = api.leaf {
      description = "encodeDescRet: HOAS encoder for `retI` — `encodeDescRet I k j` builds the `μ ⊤ (descDesc I k) tt` value structurally encoding a `retI I k j` description.";
      signature = "encodeDescRet : Hoas -> Level -> Hoas -> Hoas  -- I, k, targetIdx";
      value =
        let inherit (self) lam forall ann u level pair descCon ttPrim
          descEncodingCtx;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let c = descEncodingCtx iLev I k; in
                lam "j" I (j:
                  descCon c.dDesc ttPrim
                    (c.encodeAt 0 (pair (c.liftIndex j) c.liftedRefl)))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "j" I (_:
                  (descEncodingCtx iLev I k).muTt)))));
    };

    encodeDescRetTm = api.leaf {
      description = "encodeDescRetTm: pre-elaborated `encodeDescRet` — closed kernel `Tm` lambda; consumed by `interpD`'s encoded-desc view branch.";
      signature = "encodeDescRetTm : Tm";
      value = self.elab self.encodeDescRet;
    };

    # encodeDescArgAt : Π(I:U(0))(k l:Level)(eq : Eq Level (max l k) k)
    #                     (S:U(l))(T:S → μ⊤(descDesc I k)tt).
    #                   μ ⊤ (descDesc I k) tt
    # Heterogeneous-l encoder for descArg: S inhabits U(l) with bound
    # witness `eq : l ≤ k`. The encoded payload's S slot expects U(k),
    # so S is `LiftAtWithEq l k eq`-wrapped; T's domain (S : U(l)) is
    # bridged to the lifted form via `lowerAtWithEq`. Idempotent at l=k:
    # `LiftAt k k refl A ≡ A` collapses via `vLiftF`'s convLevel
    # idempotency, recovering the homogeneous shape.
    encodeDescArgAt = api.leaf {
      description = "encodeDescArgAt: HOAS encoder for `descArgAt` — universe-polymorphic encoder for `descArgAt I l k S T`.";
      signature = "encodeDescArgAt : Hoas -> Level -> Level -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level levelMax app pair descCon
          ttPrim descEncodingCtx bootEq
          LiftAtWithEq lowerAtWithEq;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                lam "l" level (l:
                  lam "eqW" (bootEq level (levelMax l k) k) (eqW:
                    let c = descEncodingCtx iLev I k; in
                    lam "S" (u l) (S:
                      lam "T" (forall "_" S (_: c.muTt)) (T:
                        let
                          sLifted = LiftAtWithEq l k eqW S;
                          tPayloadDomain = c.payloadTyAtK sLifted;
                          tPayload = lam "x" tPayloadDomain (x:
                            app T (lowerAtWithEq l k eqW S
                              (c.lowerPayloadAtK sLifted x)));
                        in
                        descCon c.dDesc ttPrim
                          (c.encodeAt 1 (pair (c.liftSort sLifted)
                            (pair tPayload c.liftedRefl)))))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "l" level (l:
                  forall "eqW" (bootEq level (levelMax l k) k) (_:
                    forall "S" (u l) (S:
                      forall "T" (forall "_" S (_: (descEncodingCtx iLev I k).muTt)) (_:
                        (descEncodingCtx iLev I k).muTt))))))));
    };

    encodeDescArgAtTm = api.leaf {
      description = "encodeDescArgAtTm: pre-elaborated `encodeDescArgAt` — closed kernel `Tm`.";
      signature = "encodeDescArgAtTm : Tm";
      value = self.elab self.encodeDescArgAt;
    };

    # encodeDescArg : Π(I:U(0))(k:Level)(S:U(k))(T:S → μ⊤(descDesc I k)tt).
    #                 μ ⊤ (descDesc I k) tt
    # Homogeneous-l specialisation of `encodeDescArgAt` at `l = k` with
    # `refl : Eq Level (max k k) k` (decided by convLevel idempotency).
    # `LiftAt k k refl S ≡ S` collapses, so the encoded payload is
    # equivalent to a direct `(S, T, liftedRefl)` triple.
    encodeDescArg = api.leaf {
      description = "encodeDescArg: HOAS encoder for `descArg` — `encodeDescArg I k S T` builds the structural encoding of a `descArg I k S T` description.";
      signature = "encodeDescArg : Hoas -> Level -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level app bootRefl
          descEncodingCtx encodeDescArgAt;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let c = descEncodingCtx iLev I k; in
                lam "S" (u k) (S:
                  lam "T" (forall "_" S (_: c.muTt)) (T:
                    app (app (app (app (app (app (app encodeDescArgAt iLev) I) k) k) bootRefl) S) T))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "S" (u k) (S:
                  forall "T" (forall "_" S (_: (descEncodingCtx iLev I k).muTt)) (_:
                    (descEncodingCtx iLev I k).muTt))))));
    };

    encodeDescArgTm = api.leaf {
      description = "encodeDescArgTm: pre-elaborated `encodeDescArg` — closed kernel `Tm`.";
      signature = "encodeDescArgTm : Tm";
      value = self.elab self.encodeDescArg;
    };

    # encodeDescRec : Π(I:U(0))(k:Level)(j:I)(D:μ⊤(descDesc I k)tt).
    #                 μ ⊤ (descDesc I k) tt
    # Encodes a `descRec j D`-shaped source description.
    encodeDescRec = api.leaf {
      description = "encodeDescRec: HOAS encoder for `recI` — `encodeDescRec I k j D` builds the structural encoding of a `recI I k j D` description.";
      signature = "encodeDescRec : Hoas -> Level -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level pair descCon ttPrim
          descEncodingCtx;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let c = descEncodingCtx iLev I k; in
                lam "j" I (j:
                  lam "D" c.muTt (D:
                    descCon c.dDesc ttPrim
                      (c.encodeAt 2 (pair (c.liftIndex j)
                        (pair D c.liftedRefl)))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "j" I (_:
                  forall "D" (descEncodingCtx iLev I k).muTt (_:
                    (descEncodingCtx iLev I k).muTt))))));
    };

    encodeDescRecTm = api.leaf {
      description = "encodeDescRecTm: pre-elaborated `encodeDescRec` — closed kernel `Tm`.";
      signature = "encodeDescRecTm : Tm";
      value = self.elab self.encodeDescRec;
    };

    # encodeDescPiAt : Π(I:U(0))(k l:Level)(eq : Eq Level (max l k) k)
    #                    (S:U(l))(f:S→I)(D:μ⊤(descDesc I k)tt).
    #                  μ ⊤ (descDesc I k) tt
    # Heterogeneous-l encoder for descPi: S inhabits U(l) with bound
    # witness `eq : l ≤ k`. The encoded payload's S slot is lifted to
    # U(k) via `LiftAtWithEq`; the f-selector's domain is bridged via
    # `lowerAtWithEq`. The body D is a single recursion image (muTt) —
    # the descPi's recursive position carries one sub-description, not
    # a function. Idempotent at l=k via `LiftAt k k refl A ≡ A`.
    encodeDescPiAt = api.leaf {
      description = "encodeDescPiAt: HOAS encoder for `piIAt` — universe-polymorphic encoder for `piIAt I l k S f D`.";
      signature = "encodeDescPiAt : Hoas -> Level -> Level -> Hoas -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level levelMax app pair descCon
          ttPrim descEncodingCtx bootEq
          LiftAtWithEq lowerAtWithEq;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                lam "l" level (l:
                  lam "eqW" (bootEq level (levelMax l k) k) (eqW:
                    let c = descEncodingCtx iLev I k; in
                    lam "S" (u l) (S:
                      lam "f" (forall "_" S (_: I)) (f:
                        lam "D" c.muTt (D:
                          let
                            sLifted = LiftAtWithEq l k eqW S;
                            fLifted = lam "x" sLifted (x:
                              app f (lowerAtWithEq l k eqW S x));
                            fPayloadTy = forall "_" sLifted (_: I);
                          in
                          descCon c.dDesc ttPrim
                            (c.encodeAt 3 (pair (c.liftSort sLifted)
                              (pair (c.liftJoin fPayloadTy fLifted)
                                (pair D c.liftedRefl)))))))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "l" level (l:
                  forall "eqW" (bootEq level (levelMax l k) k) (_:
                    forall "S" (u l) (S:
                      forall "f" (forall "_" S (_: I)) (_:
                        forall "D" (descEncodingCtx iLev I k).muTt (_:
                          (descEncodingCtx iLev I k).muTt)))))))));
    };

    encodeDescPiAtTm = api.leaf {
      description = "encodeDescPiAtTm: pre-elaborated `encodeDescPiAt` — closed kernel `Tm`.";
      signature = "encodeDescPiAtTm : Tm";
      value = self.elab self.encodeDescPiAt;
    };

    # encodeDescPi : Π(I:U(0))(k:Level)(S:U(k))(f:S→I)
    #                  (D:μ⊤(descDesc I k)tt). μ ⊤ (descDesc I k) tt
    # Homogeneous-l specialisation of `encodeDescPiAt` at `l = k` with
    # `refl : Eq Level (max k k) k`. `LiftAt k k refl S ≡ S` collapses,
    # recovering the direct `(S, f, D, liftedRefl)` payload shape.
    encodeDescPi = api.leaf {
      description = "encodeDescPi: HOAS encoder for `piI` — `encodeDescPi I k S f D` builds the structural encoding of a `piI I k S f D` description.";
      signature = "encodeDescPi : Hoas -> Level -> Hoas -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level app bootRefl
          descEncodingCtx encodeDescPiAt;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let c = descEncodingCtx iLev I k; in
                lam "S" (u k) (S:
                  lam "f" (forall "_" S (_: I)) (f:
                    lam "D" c.muTt (D:
                      app (app (app (app (app (app (app (app encodeDescPiAt iLev) I) k) k) bootRefl) S) f) D)))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "S" (u k) (S:
                  forall "f" (forall "_" S (_: I)) (_:
                    forall "D" (descEncodingCtx iLev I k).muTt (_:
                      (descEncodingCtx iLev I k).muTt)))))));
    };

    encodeDescPiTm = api.leaf {
      description = "encodeDescPiTm: pre-elaborated `encodeDescPi` — closed kernel `Tm`.";
      signature = "encodeDescPiTm : Tm";
      value = self.elab self.encodeDescPi;
    };

    # encodeDescPlus : Π(I:U(0))(k:Level)(A:μ⊤(descDesc I k)tt)
    #                    (B:μ⊤(descDesc I k)tt). μ ⊤ (descDesc I k) tt
    # Encodes a `descPlus A B`-shaped source description.
    encodeDescPlus = api.leaf {
      description = "encodeDescPlus: HOAS encoder for `plusI` — `encodeDescPlus I k A B` builds the structural encoding of a `plusI I k A B` description.";
      signature = "encodeDescPlus : Hoas -> Level -> Hoas -> Hoas -> Hoas";
      value =
        let inherit (self) lam forall ann u level pair descCon ttPrim
          descEncodingCtx;
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                let c = descEncodingCtx iLev I k; in
                lam "A" c.muTt (A:
                  lam "B" c.muTt (B:
                    descCon c.dDesc ttPrim
                      (c.encodeAt 4 (pair A (pair B c.liftedRefl)))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "A" (descEncodingCtx iLev I k).muTt (_:
                  forall "B" (descEncodingCtx iLev I k).muTt (_:
                    (descEncodingCtx iLev I k).muTt))))));
    };

    encodeDescPlusTm = api.leaf {
      description = "encodeDescPlusTm: pre-elaborated `encodeDescPlus` — closed kernel `Tm`.";
      signature = "encodeDescPlusTm : Tm";
      value = self.elab self.encodeDescPlus;
    };

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
    encodeDescElim = api.leaf {
      description = "encodeDescElim: HOAS encoder for `descElim` — produces the cascade application that walks `descDesc`'s plus-tree to dispatch on a `VDescCon` value's constructor.";
      signature = "encodeDescElim : Hoas -> Level -> Level -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas";
      value =
        let
          inherit (self) lam forall ann u level fst_ snd_ app
            descCon descInd bootSum bootSumElim
            bootInl bootInr
            ttPrim unitPrim
            descEncodingCtx
            interpD allD
            LiftAt liftAt lowerAt levelMaxOpt
            encodeDescRet encodeDescArg encodeDescRec
            encodeDescPi encodeDescPlus;

          # Flat encoder applications used in the result-type ascriptions.
          encRet = iLev: I: k: j:
            app (app (app (app encodeDescRet iLev) I) k) j;
          encArg = iLev: I: k: S: T:
            app (app (app (app (app encodeDescArg iLev) I) k) S) T;
          encRec = iLev: I: k: j: D:
            app (app (app (app (app encodeDescRec iLev) I) k) j) D;
          encPi = iLev: I: k: S: f: D:
            app (app (app (app (app (app encodeDescPi iLev) I) k) S) f) D;
          encPlus = iLev: I: k: A: B:
            app (app (app (app (app encodeDescPlus iLev) I) k) A) B;

          # The full bound-binder body; reused inside both the lam chain
          # (for the elaborated term) and the forall chain (for ann).
          bodyOnArgs = iLev: I: k: L: motive: onRet: onArg: onRec: onPi: onPlus: scrut:
            let
              c = descEncodingCtx iLev I k;
              allK = levelMaxOpt c.dDescL L;
              # `descInd`'s All argument may live above the user's motive
              # level because descDesc binds field types. Lift the motive for
              # induction and lower at the public eliminator boundary.
              motiveI = lam "_i" unitPrim (_:
                lam "x" c.muTt (x:
                  LiftAt L allK (app motive x)));
              lowerMotive = target: x:
                lowerAt L allK (app motive target) x;
              liftMotive = target: x:
                liftAt L allK (app motive target) x;

              # Per-summand case bodies. Receive `ctx` (the outer-payload
              # accumulator threaded by `cascade`), the matched payload
              # `r` (or bare `dCur` at depth 4) plus the per-summand
              # all-IH `rih` (or `ihCur` at depth 4); emit the user case
              # body applied to its arguments.
              caseRet = _ctx: r: _rih:
                app onRet (c.lowerIndex (fst_ r));

              caseArg = _ctx: r: rih:
                let
                  S = c.lowerSort (fst_ r);
                  tPayload = fst_ (snd_ r);
                  T = lam "_s" S (s:
                    app tPayload (c.liftPayloadAtK S s));
                  ihRaw = fst_ rih;
                  ihFn = lam "_s" S (s:
                    let
                      sLifted = c.liftPayloadAtK S s;
                      target = app tPayload sLifted;
                    in
                    lowerMotive target (app ihRaw sLifted));
                in
                app (app (app onArg S) T) ihFn;

              caseRec = _ctx: r: rih:
                let
                  jVal = c.lowerIndex (fst_ r);
                  D = fst_ (snd_ r);
                  ihD = lowerMotive D (fst_ rih);
                in
                app (app (app onRec jVal) D) ihD;

              casePi = _ctx: r: rih:
                let
                  S = c.lowerSort (fst_ r);
                  fTy = forall "_" S (_: I);
                  f = c.lowerJoin fTy (fst_ (snd_ r));
                  D = fst_ (snd_ (snd_ r));
                  ihD = lowerMotive D (fst_ rih);
                in
                app (app (app (app onPi S) f) D) ihD;

              # depth 4 — no enclosing sum at this layer; the rest-spine
              # is the bare descPlus pair `(A, B, leafLifted)`. `ctx` has
              # already accumulated the four outer `bootInr` wrappers.
              casePlus = ctx: dCur: ihCur:
                let
                  A = fst_ dCur;
                  B = fst_ (snd_ dCur);
                  ihA = lowerMotive A (fst_ ihCur);
                  ihB = lowerMotive B (fst_ (snd_ ihCur));
                  target = descCon c.dDesc ttPrim (ctx dCur);
                in
                liftMotive target (app (app (app (app onPlus A) B) ihA) ihB);

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
                    curD = builtins.elemAt c.conDescs depthIdx;
                    restSpine = c.spineFrom (depthIdx + 1);
                    lTy = c.interpAt curD;
                    rTy = c.interpAt restSpine;
                    caseFn =
                      if depthIdx == 0 then caseRet
                      else if depthIdx == 1 then caseArg
                      else if depthIdx == 2 then caseRec
                      else casePi;
                    sumMot = lam "s" (bootSum lTy rTy) (s:
                      forall "_rih"
                        (allD c.dDescL unitPrim (c.plus curD restSpine)
                          allK
                          c.muFam
                          motiveI
                          ttPrim
                          s)
                        (_: LiftAt L allK
                          (app motive (descCon c.dDesc ttPrim (ctx s)))));
                    onInl = lam "r" lTy (r:
                      lam "rih"
                        (allD c.dDescL unitPrim curD
                          allK
                          c.muFam
                          motiveI
                          ttPrim
                          r)
                        (rih:
                          let
                            target = descCon c.dDesc ttPrim
                              (ctx (bootInl lTy rTy r));
                          in
                          liftMotive target (caseFn ctx r rih)));
                    ctx' = s_in: ctx (bootInr lTy rTy s_in);
                    onInr = lam "r" rTy (r:
                      lam "rih"
                        (allD c.dDescL unitPrim restSpine
                          allK
                          c.muFam
                          motiveI
                          ttPrim
                          r)
                        (rih:
                          cascade (depthIdx + 1) ctx' r rih));
                  in
                  app (bootSumElim lTy rTy sumMot onInl onInr dCur) ihCur;

              step = lam "_i" unitPrim (iArg:
                lam "d" (interpD c.dDescL unitPrim c.dDesc c.muFam iArg) (d:
                  lam "ih"
                    (allD c.dDescL unitPrim c.dDesc
                      allK
                      c.muFam
                      motiveI
                      iArg
                      d)
                    (ih:
                      cascade 0 (s: s) d ih)));
            in
            lowerMotive scrut (descInd c.dDesc motiveI step ttPrim scrut);
        in
        ann
          (lam "iLev" level (iLev:
            lam "I" (u iLev) (I:
              lam "k" level (k:
                lam "L" level (L:
                  let
                    c = descEncodingCtx iLev I k;
                    motiveTy = forall "_" c.muTt (_: u L);
                  in
                  lam "motive" motiveTy (motive:
                    lam "onRet"
                      (forall "j" I (j: app motive (encRet iLev I k j)))
                      (onRet:
                        lam "onArg"
                          (forall "S" (u k) (S:
                            forall "T" (forall "_" S (_: c.muTt)) (T:
                              forall "ih" (forall "_s" S (s: app motive (app T s))) (_:
                                app motive (encArg iLev I k S T)))))
                          (onArg:
                            lam "onRec"
                              (forall "j" I (j:
                                forall "D" c.muTt (D:
                                  forall "ih" (app motive D) (_:
                                    app motive (encRec iLev I k j D)))))
                              (onRec:
                                lam "onPi"
                                  (forall "S" (u k) (S:
                                    forall "f" (forall "_" S (_: I)) (f:
                                      forall "D" c.muTt (D:
                                        forall "ih" (app motive D) (_:
                                          app motive (encPi iLev I k S f D))))))
                                  (onPi:
                                    lam "onPlus"
                                      (forall "A" c.muTt (A:
                                        forall "B" c.muTt (B:
                                          forall "ihA" (app motive A) (_:
                                            forall "ihB" (app motive B) (_:
                                              app motive (encPlus iLev I k A B))))))
                                      (onPlus:
                                        lam "scrut" c.muTt (scrut:
                                          bodyOnArgs iLev I k L motive onRet onArg onRec onPi onPlus scrut))))))))))))
          (forall "iLev" level (iLev:
            forall "I" (u iLev) (I:
              forall "k" level (k:
                forall "L" level (L:
                  let
                    c = descEncodingCtx iLev I k;
                    motiveTy = forall "_" c.muTt (_: u L);
                  in
                  forall "motive" motiveTy (motive:
                    forall "onRet"
                      (forall "j" I (j: app motive (encRet iLev I k j)))
                      (_:
                        forall "onArg"
                          (forall "S" (u k) (S:
                            forall "T" (forall "_" S (_: c.muTt)) (T:
                              forall "ih" (forall "_s" S (s: app motive (app T s))) (_:
                                app motive (encArg iLev I k S T)))))
                          (_:
                            forall "onRec"
                              (forall "j" I (j:
                                forall "D" c.muTt (D:
                                  forall "ih" (app motive D) (_:
                                    app motive (encRec iLev I k j D)))))
                              (_:
                                forall "onPi"
                                  (forall "S" (u k) (S:
                                    forall "f" (forall "_" S (_: I)) (f:
                                      forall "D" c.muTt (D:
                                        forall "ih" (app motive D) (_:
                                          app motive (encPi iLev I k S f D))))))
                                  (_:
                                    forall "onPlus"
                                      (forall "A" c.muTt (A:
                                        forall "B" c.muTt (B:
                                          forall "ihA" (app motive A) (_:
                                            forall "ihB" (app motive B) (_:
                                              app motive (encPlus iLev I k A B))))))
                                      (_:
                                        forall "scrut" c.muTt (scrut:
                                          app motive scrut))))))))))));
    };

    encodeDescElimTm = api.leaf {
      description = "encodeDescElimTm: pre-elaborated `encodeDescElim` — closed kernel `Tm` form of the eliminator cascade.";
      signature = "encodeDescElimTm : Tm";
      value = self.elab self.encodeDescElim;
    };

    encodeDescElimVal = api.leaf {
      description = "encodeDescElimVal: pre-evaluated `encodeDescElim` — kernel `Val` form, ready for direct consumption without re-evaluation.";
      signature = "encodeDescElimVal : Val";
      value = fx.tc.eval.eval [ ] self.encodeDescElimTm;
    };
  };
}
