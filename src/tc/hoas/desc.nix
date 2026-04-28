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
# Principled note on lam annotations: check.nix's check-lam discards the
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
{ self, ... }:

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
      let inherit (self) plus descArg descRet descRec; in
      plus descRet (descArg 0 elem (_: descRec descRet));

    # sumDesc l r : Desc ⊤ — inl (arg : l) ⊕ inr (arg : r). Both summands
    # are `descArg _ (_: retI ttPrim)` leaves at the ⊤-slice.
    sumDesc = l: r:
      let inherit (self) plus descArg descRet; in
      plus (descArg 0 l (_: descRet)) (descArg 0 r (_: descRet));

    # descDesc : Π(k : Level). Desc^(suc k) ⊤ — k-parameterised
    # description of descriptions. Five summands mirroring the grammar
    # of `Desc^(suc k) ⊤`:
    #   ret  — retI ⊤
    #   arg  — Π(S : U(k)). Π(T : S → ⊤). ⊤
    #   rec  — Π(_ : ⊤). ⊤
    #   pi   — Π(S : U(k)). Π(T : S → ⊤). Π(_ : ⊤). ⊤
    #   plus — Π(_ : ⊤). Π(_ : ⊤). ⊤
    # Every kernel descArg / descPi inside this body announces a
    # description-level of `suc k` (matching the outer Desc^(suc k)),
    # but each individual summand's *sort* lives at its natural per-
    # summand level. The arg / pi summands' first descArg's sort is
    # `u k : U(suc k)` — homogeneous at the description level. The
    # inner `descPi` over `S : U(k)` uses the mixed-level form
    # `descPiAt k (suc k) …`: per-summand level `k`, description level
    # `suc k`, with the bound witness `refl : Eq Level (max k (suc k))
    # (suc k)` discharged by the kernel's convLevel semilattice
    # quotient (`max k (suc k) = suc k`). Replaces the prior
    # Sub-at-U-mediated coercion of `S : U(k)` into a `U(suc k)` slot.
    descDesc =
      let inherit (self) lam forall ann level u plus descAt
                         descRet descArg descRec descPi descPiAt levelSuc; in
      ann
        (lam "k" level (k:
           let sk = levelSuc k; in
           plus descRet
           (plus (descArg sk (u k) (S: descPiAt k sk S descRet))
           (plus (descRec descRet)
           (plus (descArg sk (u k) (_: descRec descRet))
                 (descRec (descRec descRet)))))))
        (forall "k" level (k: descAt (levelSuc k)));

    # iso : Π(k : Level). Iso (Desc^k ⊤) (μ (descDesc k) tt)
    #
    # Iso A B = Σ(to:A→B). Σ(from:B→A).
    #             Σ(toFrom:Π(a:A). Eq A (from(to a)) a).
    #               Π(b:B). Eq B (to(from b)) b
    #
    # Bundles four kernel-internal proofs witnessing that, at every
    # universe level k, the syntactic `Desc^k ⊤` and the descDesc-encoded
    # μ-type are isomorphic. The encoding/decoding pair commits to a
    # uniform argI/piI level k throughout the source description; the
    # reconstruction at recursive positions uses the IH provided by
    # descElim/descInd directly rather than calling to/from at the
    # meta level.
    #
    # Level alignment: `from` reconstructs `descArg k S T` / `descPi k S
    # f D`, so the source side of the iso must be `Desc^k ⊤` (level
    # slot ≥ k). At k=0 this collapses to the prelude `desc = Desc^0 ⊤`.
    # Both sides inhabit `U(suc k)`: `descDesc k : Desc^(suc k) ⊤` makes
    # `μ(descDesc k) tt : U(suc k)`; `Desc^k ⊤ : U(suc k)` matches.
    iso =
      let
        inherit (self) lam forall sigma ann level levelZero levelSuc
                       u plus pair fst_ snd_ refl ttPrim unitPrim
                       eq desc descAt descRet descArg descRec descPi descPiAt
                       descCon descElim descInd interpHoasAt allHoasAt
                       sumPrim sumElimPrim inlPrim inrPrim liftAt lowerAt
                       muI mu app descDesc encodeTag;

        # The polymorphic iso type. `dDescAt k` is `app descDesc k`
        # — the description-of-descriptions specialised at k. The
        # final two components reference earlier sigma-bound `toV` /
        # `fromV` so toFrom / fromTo's types pin the iso witness
        # functions exactly (Σ-η reduces these to the closed `to` /
        # `from` terms once the bundle is destructed).
        isoTy = forall "k" level (k:
          let
            dDescAt = app descDesc k;
            muTtAt = mu dDescAt ttPrim;
            descK = descAt k;
          in
          sigma "to_" (forall "_" descK (_: muTtAt)) (toV:
          sigma "from_" (forall "_" muTtAt (_: descK)) (fromV:
          sigma "toFrom_"
            (forall "D" descK (D: eq descK (app fromV (app toV D)) D))
            (_:
              forall "x" muTtAt (x:
                eq muTtAt (app toV (app fromV x)) x)))));
      in
      ann
        (lam "k" level (k:
          let
            dDesc = app descDesc k;
            muTt = mu dDesc ttPrim;
            muFam = lam "_i" unitPrim (iArg: mu dDesc iArg);

            # `dDesc`'s intrinsic level. Its outer `descArg`/`descPi`
            # K-slots are `levelSuc k` (their domain `u k : U(suc k)`);
            # the inner `descPi k` body's K-slot is `k` but is dominated
            # by the outer `levelSuc k` in the `max` lattice. Threaded
            # into every `interpHoasAt` / `allHoasAt` call for the iso
            # so descElim's leading K, sort binders in onArg / onPi,
            # and the `descIAt L I` ann-wrap line up with the actual
            # scrutinee descArg K-slot at type-check time.
            dDescL = levelSuc k;

            # `Desc^k ⊤` — the source side of the iso. `from`
            # reconstructs descriptions whose `descArg`/`descPi` slots
            # carry level `k`, so `from`'s codomain (and hence `to`'s
            # domain, the toFrom equality's underlying type, and every
            # internal `desc`-typed annotation in this iso) lives at
            # `Desc^k ⊤`. At k=0 `descK` ≡ `desc` (the prelude form).
            descK = descAt k;

            # Per-summand sub-descriptions of `dDesc`. Indices 0..4.
            # Used by `encodeTag` for `to`'s payload, by the sumElim
            # cascade for `from` and `fromTo`, and as L/R types in
            # the sumElim layers via `interpHoasAt`. Mirrors descDesc's
            # body shape exactly — the inner `descPiAt k (suc k)` form
            # threads the mixed-level bound witness so `S : U(k)` fits
            # the description's `Desc^(suc k)` slot via `convLevel`'s
            # `max k (suc k) = suc k` rather than via Sub-at-U.
            conDescs = [
              descRet
              (descArg (levelSuc k) (u k) (S: descPiAt k (levelSuc k) S descRet))
              (descRec descRet)
              (descArg (levelSuc k) (u k) (_: descRec descRet))
              (descRec (descRec descRet))
            ];

            # Right-spine of conDescs starting at index i (matches
            # `descDesc`'s right-associated `plus` tree; consumed by
            # the per-layer L/R type computation in the cascade).
            spineFrom = i:
              let n = builtins.length conDescs; remaining = n - i; in
              if remaining == 1 then builtins.elemAt conDescs i
              else plus (builtins.elemAt conDescs i) (spineFrom (i + 1));

            # Wrap a payload at summand `t` with the inrPrim/inlPrim
            # chain selecting the t-th summand of `dDesc`'s plus tree.
            encodeAt = t: payload:
              encodeTag unitPrim dDesc conDescs ttPrim t payload;

            # Per-layer L/R interp types at iArg=tt. The cascade's
            # sumElim layers and the All-type at each layer reference
            # these; they conv-equal the corresponding summand-spine
            # interpretations under the muFam family. `interpHoasAt`'s
            # `L = dDescL` matches the K-slot of dDesc's descArg/descPi
            # summands so descElim's leading k aligns at type-check.
            interpAt = dH: interpHoasAt dDescL unitPrim dH muFam ttPrim;

            # Lift mediation at the descRet leaf for `L = dDescL = suc k`.
            # The kernel's `interp`'s `onRet` wraps `Eq I j i` with
            # `Lift 0 L _` (eval/desc.nix `interpOnRet`); at `L = suc k
            # > 0` this is a genuine lift cell (no idempotent collapse).
            # Every value flowing into the descRet-leaf slot of a
            # descCon payload must inhabit `Lift 0 dDescL _ (Eq Unit
            # tt tt)`; every leaf-eq projection consumed by `j` (which
            # check-matches a `VEq`, never a `VLift`) must be lowered.
            # `iArg = tt` and the descRet's `j = tt` are uniform across
            # all summands, so the leaf type is invariant.
            eqLeafTy = eq unitPrim ttPrim ttPrim;
            liftLeaf = e: liftAt levelZero dDescL eqLeafTy e;
            lowerLeaf = x: lowerAt levelZero dDescL eqLeafTy x;
            liftedRefl = liftLeaf refl;

            # =================================================================
            # to : Desc ⊤ → μ dDesc tt
            #
            # descElim cascade with motive `λ_. μ dDesc tt`. Each case
            # emits `descCon dDesc tt (encodeAt t (payload))` selecting
            # the t-th summand and packing the IH-derived recursive
            # image at the recursive positions. descElim's IH supplies
            # the recursive `to`-image directly — no meta-level recursion.
            # =================================================================
            toMotive = lam "_D" descK (_: muTt);

            toOnRet = lam "j" unitPrim (_:
              descCon dDesc ttPrim (encodeAt 0 liftedRefl));

            toOnArg = lam "S" (u k) (S:
                      lam "T" (forall "_" S (_: descK)) (_:
                      lam "ih" (forall "_s" S (_: muTt)) (ih:
                        descCon dDesc ttPrim
                          (encodeAt 1 (pair S (pair ih liftedRefl))))));

            toOnRec = lam "j" unitPrim (_:
                      lam "D" descK (_:
                      lam "ih" muTt (ih:
                        descCon dDesc ttPrim
                          (encodeAt 2 (pair ih liftedRefl)))));

            toOnPi  = lam "S" (u k) (S:
                      lam "f" (forall "_" S (_: unitPrim)) (_:
                      lam "D" descK (_:
                      lam "ih" muTt (ih:
                        descCon dDesc ttPrim
                          (encodeAt 3 (pair S (pair ih liftedRefl)))))));

            toOnPlus = lam "A" descK (_:
                       lam "B" descK (_:
                       lam "ihA" muTt (ihA:
                       lam "ihB" muTt (ihB:
                         descCon dDesc ttPrim
                           (encodeAt 4 (pair ihA (pair ihB liftedRefl)))))));

            to = ann
              (lam "D" descK (D:
                descElim k toMotive
                  toOnRet toOnArg toOnRec toOnPi toOnPlus
                  (ann D descK)))
              (forall "_" descK (_: muTt));

            # =================================================================
            # from : μ dDesc tt → Desc ⊤
            #
            # descInd with constant motive `Q i x = Desc ⊤`. The step
            # body dispatches on the encoded payload via a 4-layer
            # `sumElimPrim` cascade matching descDesc's right-associated
            # plus tree. Each summand reconstructs the corresponding
            # Desc-form, reading recursive sub-descriptions out of the
            # IH structure via `fst_`/`snd_` projections. The sumElim
            # motive at each layer is `Π(rih:All …). desc`, applied to
            # the corresponding ih branch at the call site so the
            # per-summand sub-IH flows in with the matching type.
            # =================================================================
            fromMotive = lam "_i" unitPrim (_:
                         lam "_x" muTt (_: descK));

            # Reconstruction at each summand. Receives the matched
            # payload `r` and the per-summand IH `rih`; emits the
            # corresponding Desc⊤ form.
            #
            #   summand 0 (ret) : `descRet`. ih is Unit; r is the
            #     leaf-eq witness, irrelevant.
            #   summand 1 (arg) : `descArg k S (s: app ihFn s)` where
            #     S = fst r and ihFn : Π(s':S). desc is the head of
            #     the All-on-descArg-with-descPi-body Σ-chain.
            #   summand 2 (rec) : `descRec D'` where D' = fst rih is
            #     the recursive image at the descRec position.
            #   summand 3 (pi)  : `descPi k S D'` with S = fst r and
            #     D' = fst rih (the body's recursive image).
            #   summand 4 (plus): `plus A' B'` with A' = fst rih and
            #     B' = fst (snd rih) (two recursive images).
            caseRet = _r: _rih: descRet;
            caseArg = r: rih:
              let S = fst_ r;
                  ihFn = fst_ rih;
              in descArg k S (s: app ihFn s);
            caseRec = _r: rih: descRec (fst_ rih);
            casePi  = r: rih:
              let S = fst_ r;
                  D' = fst_ rih;
              in descPi k S D';
            casePlus = _r: rih:
              let A' = fst_ rih;
                  B' = fst_ (snd_ rih);
              in plus A' B';

            # Build the dispatch cascade at depth `depthIdx` on the
            # remaining payload `dCur` and ih `ihCur`. `depthIdx`
            # ranges over 0..3 (sumElim layers). At depth 4 the
            # remaining spine has a single leaf (summand 4) and the
            # branch is taken directly via `casePlus`.
            fromCascade = depthIdx: dCur: ihCur:
              if depthIdx == 4
              then casePlus dCur ihCur
              else
                let
                  curD = builtins.elemAt conDescs depthIdx;
                  restSpine = spineFrom (depthIdx + 1);
                  lTy = interpAt curD;
                  rTy = interpAt restSpine;
                  caseFn =
                         if depthIdx == 0 then caseRet
                    else if depthIdx == 1 then caseArg
                    else if depthIdx == 2 then caseRec
                    else                        casePi;
                  sumMot = lam "s" (sumPrim lTy rTy) (s:
                    forall "_rih"
                      (allHoasAt dDescL dDescL unitPrim dDesc
                        (plus curD restSpine) fromMotive ttPrim s)
                      (_: descK));
                  onInl = lam "r" lTy (r:
                          lam "rih"
                            (allHoasAt dDescL dDescL unitPrim dDesc curD
                              fromMotive ttPrim r) (rih:
                            caseFn r rih));
                  onInr = lam "r" rTy (r:
                          lam "rih"
                            (allHoasAt dDescL dDescL unitPrim dDesc restSpine
                              fromMotive ttPrim r) (rih:
                            fromCascade (depthIdx + 1) r rih));
                in
                app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

            fromStep = lam "_i" unitPrim (iArg:
                       lam "d" (interpHoasAt dDescL unitPrim dDesc muFam iArg) (d:
                       lam "ih" (allHoasAt dDescL dDescL unitPrim dDesc dDesc
                                   fromMotive iArg d) (ih:
                         fromCascade 0 d ih)));

            from = ann
              (lam "x" muTt (x:
                descInd dDesc fromMotive fromStep ttPrim x))
              (forall "_" muTt (_: descK));

            # =================================================================
            # toFrom : Π(D : Desc ⊤). Eq Desc⊤ (from (to D)) D
            #
            # descElim cascade with motive `λD. Eq Desc⊤ (from (to D)) D`.
            # The ret case collapses to `refl` (no recursion); rec/pi/plus
            # need J-transport along the descElim IH (the kernel's conv
            # cannot reduce `from (to D)` to `D` for neutral D — only
            # the IH supplies that propositional equality, and J carries
            # it up to the wrapped Desc-form). The arg case uses funext
            # to lift the pointwise IH into a function equality, then
            # J-transports through the descArg wrapping.
            # =================================================================
            toFromMotive = lam "D" descK (D:
              eq descK (app from (app to D)) D);

            toFromOnRet = lam "j" unitPrim (_: refl);

            # funext lifts the pointwise IH `Π(s:S). Eq Desc⊤
            # (from (to (T s))) (T s)` to a function equality
            # `Eq (S→Desc⊤) (λs. from (to (T s))) T`. J then transports
            # `refl : Eq Desc⊤ (descArg k S fLifted) (descArg k S fLifted)`
            # along this equality (under motive `λg _. Eq Desc⊤ (descArg
            # k S fLifted) (descArg k S g)`) to the goal at g = T.
            toFromOnArg = lam "S" (u k) (S:
                          lam "T" (forall "_" S (_: descK)) (T:
                          lam "ih" (forall "s" S (s:
                                     eq descK (app from (app to (app T s)))
                                                (app T s))) (ih:
                            let
                              fnTy = forall "_" S (_: descK);
                              fLifted = ann
                                (lam "s" S (s:
                                  app from (app to (app T s))))
                                fnTy;
                              # `funext`'s second `Level` arg is B's
                              # codomain universe. B = `λ_:S. descK`
                              # with `descK = Desc^k ⊤ : U(suc k)`.
                              # So `k_funext = levelSuc k` (matches the
                              # universe in which the resulting
                              # function-level Eq inhabits).
                              eqFns = app (app (app (app (app (app (app
                                self.funext k) (levelSuc k)) S)
                                (lam "_" S (_: descK)))
                                fLifted) T)
                                ih;
                              jMot = lam "g" fnTy (g:
                                     lam "_e" (eq fnTy fLifted g) (_:
                                       eq descK
                                         (descArg k S
                                            (s_: app fLifted s_))
                                         (descArg k S
                                            (s_: app g s_))));
                            in
                              self.j fnTy fLifted jMot refl T eqFns)));

            # `from (to (recI j D))` reduces to `descRec (from (to D))`
            # (caseRec at depthIdx=2). `recI j D` ≡ `descRec D` by
            # unit-η on j. J on the IH `Eq desc (from (to D)) D` at
            # motive `λx _. Eq desc (descRec (from (to D))) (descRec x)`
            # transports refl from x = (from (to D)) to x = D.
            toFromOnRec = lam "j" unitPrim (_:
                          lam "D" descK (D:
                          lam "ih" (eq descK (app from (app to D)) D) (ih:
                            let
                              ftD = app from (app to D);
                              jMot = lam "x" descK (x:
                                     lam "_e" (eq descK ftD x) (_:
                                       eq descK (descRec ftD) (descRec x)));
                            in self.j descK ftD jMot refl D ih)));

            # `from (to (piI k S f D))` reduces to `descPi k S (from (to D))`
            # (casePi at depthIdx=3); `piI k S f D` ≡ `descPi k S D` by
            # unit-η on f's codomain. Same J-transport pattern as onRec,
            # with the wrapping head `descPi k S _`.
            toFromOnPi  = lam "S" (u k) (S:
                          lam "f" (forall "_" S (_: unitPrim)) (_:
                          lam "D" descK (D:
                          lam "ih" (eq descK (app from (app to D)) D) (ih:
                            let
                              ftD = app from (app to D);
                              jMot = lam "x" descK (x:
                                     lam "_e" (eq descK ftD x) (_:
                                       eq descK
                                         (descPi k S ftD) (descPi k S x)));
                            in self.j descK ftD jMot refl D ih))));

            # `from (to (plus A B))` reduces to `plus (from (to A))
            # (from (to B))` (casePlus at depthIdx=4). Two nested
            # J-transports bridge each summand to its respective IH
            # target: outer J on ihA along `λa _. Eq desc (plus (fa) (fb)) (plus a fb)`
            # then on the result combined via inner J on ihB along
            # `λb _. Eq desc (plus a (fb)) (plus a b)` reaches `plus A B`.
            toFromOnPlus = lam "A" descK (A:
                           lam "B" descK (B:
                           lam "ihA" (eq descK (app from (app to A)) A) (ihA:
                           lam "ihB" (eq descK (app from (app to B)) B) (ihB:
                             let
                               fA = app from (app to A);
                               fB = app from (app to B);
                               innerJ = self.j descK fB
                                 (lam "b" descK (b:
                                  lam "_e" (eq descK fB b) (_:
                                    eq descK (plus fA fB) (plus fA b))))
                                 refl
                                 B
                                 ihB;
                               outerJMot = lam "a" descK (a:
                                           lam "_e" (eq descK fA a) (_:
                                             eq descK (plus fA fB) (plus a B)));
                             in self.j descK fA outerJMot innerJ A ihA))));

            toFrom = lam "D" descK (D:
              descElim k toFromMotive
                toFromOnRet toFromOnArg toFromOnRec toFromOnPi toFromOnPlus
                (ann D descK));

            # =================================================================
            # fromTo : Π(x : μ dDesc tt). Eq (μ dDesc tt) (to (from x)) x
            #
            # descInd with motive `Q i x = Eq (μ dDesc i) (to (from x)) x`.
            # Step dispatches via 4-layer sumElim cascade following
            # `from`'s shape, threading a `ctx` payload-reconstruction
            # function so each layer's motive expresses the goal as
            # `Eq muTt (to(from(descCon dDesc tt (ctx s)))) (descCon
            # dDesc tt (ctx s))` — at the leaf, `ctx` produces the
            # FULL encoded payload, allowing the case body to discharge
            # the equality at the original descCon target via
            # J-transports on the leaf-equality witness and (for non-ret
            # summands) recursive equality IHs supplied by descInd.
            # =================================================================
            fromToMotive = lam "_i" unitPrim (iArg:
                           lam "x" (mu dDesc iArg) (x:
                             eq (mu dDesc iArg) (app to (app from x)) x));

            # Per-layer goal type at sub-payload `s` reconstructed via
            # `ctx`: the equality between the to/from-roundtrip of the
            # full descCon and the original descCon, with the kernel
            # conv-reducing the LHS at the case body's specific s.
            fromToTargetAt = ctx: s:
              eq muTt
                (app to (app from (descCon dDesc ttPrim (ctx s))))
                (descCon dDesc ttPrim (ctx s));

            # ret-leaf proof. Payload `r` is the leaf-eq witness
            # `Eq ⊤ tt ttPrim`. After kernel reduction, `to(from(descCon
            # dDesc tt (ctx (inlPrim L R r))))` collapses to `descCon
            # dDesc tt (ctx (inlPrim L R refl))`. J on r at motive
            # `λ_y e. Eq muTt (descCon dDesc tt (ctx (inlPrim L R refl)))
            # (descCon dDesc tt (ctx (inlPrim L R e)))` transports refl
            # from e=refl to e=r.
            caseRetEq = ctx: r:
              let
                lTy0 = interpAt (builtins.elemAt conDescs 0);
                rTy0 = interpAt (spineFrom 1);
                wrap = e: ctx (inlPrim lTy0 rTy0 e);
                jMot = lam "_y" unitPrim (_:
                       lam "e" (eq unitPrim ttPrim ttPrim) (e:
                         eq muTt
                           (descCon dDesc ttPrim (wrap liftedRefl))
                           (descCon dDesc ttPrim (wrap (liftLeaf e)))));
              in self.j unitPrim ttPrim jMot refl ttPrim (lowerLeaf r);

            # arg-leaf proof. Payload `r = pair S (pair Tlifted leafEq)`.
            # The fromTo IH at the descArg+descPi descRet body provides
            # `pointwiseEq : Π(s:S). Eq muTt (to(from(Tlifted s))) (Tlifted s)`
            # — `fst rih`. funext lifts to `Eq (S→muTt) (s. to(from(Tlifted s)))
            # Tlifted`. Compose with J on leafEq via transitivity.
            caseArgEq = ctx: r: rih:
              let
                lTyHere = interpAt (builtins.elemAt conDescs 1);
                rTyHere = interpAt (spineFrom 2);
                S = fst_ r;
                Tlifted = fst_ (snd_ r);
                leafEq = snd_ (snd_ r);
                pointwiseEq = fst_ rih;
                fnTy = forall "_" S (_: muTt);
                fLifted = lam "s" S (s:
                  app to (app from (app Tlifted s)));
                # `funext`'s second `Level` arg is B's codomain
                # universe. B = `λ_:S. muTt` with `muTt = mu dDesc tt :
                # U(suc k)` (μ inherits its level from `dDesc`'s `descArg`
                # `suc k` slot). The funext call therefore takes
                # `k_funext = levelSuc k = dDescL`, not `levelZero` —
                # using `levelZero` would mis-promise B's codomain at
                # U(0) and the kernel rejects the resulting Eq when
                # the actual `B s` inhabits U(suc k).
                eqFns = app (app (app (app (app (app (app
                  self.funext k) dDescL) S)
                  (lam "_" S (_: muTt)))
                  fLifted) Tlifted)
                  pointwiseEq;
                wrap = fn: e: ctx (inlPrim lTyHere rTyHere
                  (pair S (pair fn e)));
                stage1Mot = lam "g" fnTy (g:
                            lam "_e" (eq fnTy fLifted g) (_:
                              eq muTt
                                (descCon dDesc ttPrim (wrap fLifted liftedRefl))
                                (descCon dDesc ttPrim (wrap g liftedRefl))));
                stage1 = self.j fnTy fLifted stage1Mot refl Tlifted eqFns;
                stage2Mot = lam "_y" unitPrim (_:
                            lam "e" (eq unitPrim ttPrim ttPrim) (e:
                              eq muTt
                                (descCon dDesc ttPrim (wrap Tlifted liftedRefl))
                                (descCon dDesc ttPrim (wrap Tlifted (liftLeaf e)))));
                stage2 = self.j unitPrim ttPrim stage2Mot refl ttPrim (lowerLeaf leafEq);
                composeMot = lam "y" muTt (y:
                             lam "_e" (eq muTt
                               (descCon dDesc ttPrim (wrap Tlifted liftedRefl)) y)
                               (_:
                                 eq muTt
                                   (descCon dDesc ttPrim (wrap fLifted liftedRefl))
                                   y));
              in self.j muTt
                   (descCon dDesc ttPrim (wrap Tlifted liftedRefl))
                   composeMot
                   stage1
                   (descCon dDesc ttPrim (wrap Tlifted leafEq))
                   stage2;

            # rec-leaf proof at `depthInChain` (= 2 for our descDesc).
            # Payload `r = pair Drec leafEq`; IH `rih = pair ihEq unit`
            # with `ihEq : Eq muTt (to(from Drec)) Drec`. Two J-transports
            # composed: one on the rec position (via ihEq), one on the
            # leaf-eq slot.
            caseRecEq = ctx: depthInChain: r: rih:
              let
                curD = builtins.elemAt conDescs depthInChain;
                restSpine = spineFrom (depthInChain + 1);
                lTyHere = interpAt curD;
                rTyHere = interpAt restSpine;
                Drec = fst_ r;
                leafEq = snd_ r;
                ihEq = fst_ rih;
                ftDrec = app to (app from Drec);
                wrap = x: e: ctx (inlPrim lTyHere rTyHere (pair x e));
                stage1Mot = lam "x" muTt (x:
                            lam "_e" (eq muTt ftDrec x) (_:
                              eq muTt
                                (descCon dDesc ttPrim (wrap ftDrec liftedRefl))
                                (descCon dDesc ttPrim (wrap x liftedRefl))));
                stage1 = self.j muTt ftDrec stage1Mot refl Drec ihEq;
                stage2Mot = lam "_y" unitPrim (_:
                            lam "e" (eq unitPrim ttPrim ttPrim) (e:
                              eq muTt
                                (descCon dDesc ttPrim (wrap Drec liftedRefl))
                                (descCon dDesc ttPrim (wrap Drec (liftLeaf e)))));
                stage2 = self.j unitPrim ttPrim stage2Mot refl ttPrim (lowerLeaf leafEq);
                composeMot = lam "y" muTt (y:
                             lam "_e" (eq muTt
                               (descCon dDesc ttPrim (wrap Drec liftedRefl)) y)
                               (_:
                                 eq muTt
                                   (descCon dDesc ttPrim (wrap ftDrec liftedRefl))
                                   y));
              in self.j muTt
                   (descCon dDesc ttPrim (wrap Drec liftedRefl))
                   composeMot
                   stage1
                   (descCon dDesc ttPrim (wrap Drec leafEq))
                   stage2;

            # pi-leaf proof. Payload `r = pair S (pair Drec leafEq)`,
            # same shape as rec-leaf with an additional descArg-S
            # prefix in the wrap. `ihEq : Eq muTt (to(from Drec)) Drec`
            # at `fst rih`.
            casePiEq = ctx: r: rih:
              let
                lTyHere = interpAt (builtins.elemAt conDescs 3);
                rTyHere = interpAt (spineFrom 4);
                S = fst_ r;
                Drec = fst_ (snd_ r);
                leafEq = snd_ (snd_ r);
                ihEq = fst_ rih;
                ftDrec = app to (app from Drec);
                wrap = x: e: ctx (inlPrim lTyHere rTyHere
                  (pair S (pair x e)));
                stage1Mot = lam "x" muTt (x:
                            lam "_e" (eq muTt ftDrec x) (_:
                              eq muTt
                                (descCon dDesc ttPrim (wrap ftDrec liftedRefl))
                                (descCon dDesc ttPrim (wrap x liftedRefl))));
                stage1 = self.j muTt ftDrec stage1Mot refl Drec ihEq;
                stage2Mot = lam "_y" unitPrim (_:
                            lam "e" (eq unitPrim ttPrim ttPrim) (e:
                              eq muTt
                                (descCon dDesc ttPrim (wrap Drec liftedRefl))
                                (descCon dDesc ttPrim (wrap Drec (liftLeaf e)))));
                stage2 = self.j unitPrim ttPrim stage2Mot refl ttPrim (lowerLeaf leafEq);
                composeMot = lam "y" muTt (y:
                             lam "_e" (eq muTt
                               (descCon dDesc ttPrim (wrap Drec liftedRefl)) y)
                               (_:
                                 eq muTt
                                   (descCon dDesc ttPrim (wrap ftDrec liftedRefl))
                                   y));
              in self.j muTt
                   (descCon dDesc ttPrim (wrap Drec liftedRefl))
                   composeMot
                   stage1
                   (descCon dDesc ttPrim (wrap Drec leafEq))
                   stage2;

            # plus-leaf proof (depthIdx==4 in cascade — the LAST
            # summand sits as the rest-spine without a wrapping plus).
            # Payload `dCur = pair Aenc (pair Benc leafEq)`; IH `ihCur =
            # pair ihA (pair ihB unit)` with two recursive equality
            # witnesses. Three J-transports composed: ihA, ihB, leafEq.
            casePlusEq = ctx: dCur: ihCur:
              let
                Aenc = fst_ dCur;
                Benc = fst_ (snd_ dCur);
                leafEq = snd_ (snd_ dCur);
                ihA = fst_ ihCur;
                ihB = fst_ (snd_ ihCur);
                ftA = app to (app from Aenc);
                ftB = app to (app from Benc);
                wrap = a: b: e: ctx (pair a (pair b e));
                stage1Mot = lam "a" muTt (a:
                            lam "_e" (eq muTt ftA a) (_:
                              eq muTt
                                (descCon dDesc ttPrim (wrap ftA ftB liftedRefl))
                                (descCon dDesc ttPrim (wrap a ftB liftedRefl))));
                stage1 = self.j muTt ftA stage1Mot refl Aenc ihA;
                stage2Mot = lam "b" muTt (b:
                            lam "_e" (eq muTt ftB b) (_:
                              eq muTt
                                (descCon dDesc ttPrim (wrap Aenc ftB liftedRefl))
                                (descCon dDesc ttPrim (wrap Aenc b liftedRefl))));
                stage2 = self.j muTt ftB stage2Mot refl Benc ihB;
                stage3Mot = lam "_y" unitPrim (_:
                            lam "e" (eq unitPrim ttPrim ttPrim) (e:
                              eq muTt
                                (descCon dDesc ttPrim (wrap Aenc Benc liftedRefl))
                                (descCon dDesc ttPrim (wrap Aenc Benc (liftLeaf e)))));
                stage3 = self.j unitPrim ttPrim stage3Mot refl ttPrim (lowerLeaf leafEq);
                trans12Mot = lam "y" muTt (y:
                             lam "_e" (eq muTt
                               (descCon dDesc ttPrim (wrap Aenc ftB liftedRefl)) y)
                               (_:
                                 eq muTt
                                   (descCon dDesc ttPrim (wrap ftA ftB liftedRefl))
                                   y));
                trans12 = self.j muTt
                            (descCon dDesc ttPrim (wrap Aenc ftB liftedRefl))
                            trans12Mot
                            stage1
                            (descCon dDesc ttPrim (wrap Aenc Benc liftedRefl))
                            stage2;
                trans123Mot = lam "y" muTt (y:
                              lam "_e" (eq muTt
                                (descCon dDesc ttPrim (wrap Aenc Benc liftedRefl)) y)
                                (_:
                                  eq muTt
                                    (descCon dDesc ttPrim (wrap ftA ftB liftedRefl))
                                    y));
              in self.j muTt
                   (descCon dDesc ttPrim (wrap Aenc Benc liftedRefl))
                   trans123Mot
                   trans12
                   (descCon dDesc ttPrim (wrap Aenc Benc leafEq))
                   stage3;

            # `allHoasAt`'s motive-codomain `K` for `fromToCascade`.
            # `fromToMotive`'s codomain is `Eq (μ dDesc iArg) … …`;
            # `μ dDesc iArg : U(suc k)` carries D's `suc k` level from
            # `descDesc k`'s descArg sort, so the equality lives at
            # `U(suc k)`. The motive-codomain `K` and the scrutinee-
            # description level `L = dDescL = levelSuc k` coincide
            # numerically here but remain conceptually distinct
            # parameters in `allHoasAt`'s signature.
            fromToK = dDescL;

            fromToCascade = depthIdx: ctx: dCur: ihCur:
              if depthIdx == 4
              then casePlusEq ctx dCur ihCur
              else
                let
                  curD = builtins.elemAt conDescs depthIdx;
                  restSpine = spineFrom (depthIdx + 1);
                  lTy = interpAt curD;
                  rTy = interpAt restSpine;
                  sumMot = lam "s" (sumPrim lTy rTy) (s:
                    forall "_rih"
                      (allHoasAt dDescL fromToK unitPrim dDesc
                        (plus curD restSpine) fromToMotive ttPrim s)
                      (_: fromToTargetAt ctx s));
                  onInl = lam "r" lTy (r:
                          lam "rih"
                            (allHoasAt dDescL fromToK unitPrim dDesc curD
                              fromToMotive ttPrim r) (rih:
                            (
                              if depthIdx == 0
                              then caseRetEq ctx r
                              else if depthIdx == 1
                              then caseArgEq ctx r rih
                              else if depthIdx == 2
                              then caseRecEq ctx 2 r rih
                              else casePiEq ctx r rih
                            )));
                  onInr = lam "r" rTy (r:
                          lam "rih"
                            (allHoasAt dDescL fromToK unitPrim dDesc restSpine
                              fromToMotive ttPrim r) (rih:
                            fromToCascade (depthIdx + 1)
                              (s_in: ctx (inrPrim lTy rTy s_in)) r rih));
                in
                app (sumElimPrim lTy rTy sumMot onInl onInr dCur) ihCur;

            fromToStep = lam "_i" unitPrim (iArg:
                         lam "d" (interpHoasAt dDescL unitPrim dDesc muFam iArg) (d:
                         lam "ih" (allHoasAt dDescL fromToK unitPrim dDesc dDesc
                                     fromToMotive iArg d) (ih:
                           fromToCascade 0 (s: s) d ih)));

            fromTo = lam "x" muTt (x:
              descInd dDesc fromToMotive fromToStep ttPrim x);
          in
          pair to (pair from (pair toFrom fromTo))))
        isoTy;

    # Pre-elaborated natDesc — used by the zero/succ/nat-elim elaborate
    # branches to avoid re-elaborating on every constructor.
    natDescTm = self.elab self.natDesc;

    # interpHoasAt L I D X i  ≡  ⟦D⟧(X) i  as a closed kernel TERM at
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
    interpHoasAt = L: I: D: X: i:
      let
        inherit (self) ann lam forall descIAt descElim sigma app eq u sumPrim;
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
      # bind `S` at `U(L)`, so the descElim's `k` slot is `L`.
      in app (app (descElim L motive onRet onArg onRec onPi onPlus (ann D descLI)) X) i;

    # allHoasAt L K I Douter Dsub P i d ≡ All Douter Dsub P i d — the
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
    allHoasAt = L: K: I: Douter: Dsub: P: i: d:
      let
        inherit (self) ann lam forall descIAt descElim sigma app fst_ snd_
                        u unitPrim mu interpHoasAt sumPrim sumElimPrim;
        descLI = descIAt L I;
        # muFam : λi. μ Douter i — the family fed to interpHoasAt as X.
        muFam = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg: forall "_" (mu Douter iArg) (_: u K));
        # motive : λ(D:Desc^L I).
        #   Π(P:(i:I) → μ Douter i → U(K)). Π(i:I). Π(d:⟦D⟧(μ Douter) i). U(K)
        motive = lam "_" descLI (Dm:
                 forall "P" pTy (_:
                 forall "i" I (iArg:
                 forall "d" (interpHoasAt L I Dm muFam iArg) (_: u K))));
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
                            forall "d" (interpHoasAt L I (app T s) muFam iArg) (_: u K))))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "s" S (s: interpHoasAt L I (app T s) muFam iArg)) (d2:
                   app (app (app (app ihA (fst_ d2)) P2) iArg) (snd_ d2)))))));
        # onRec : λj λD λihA λP λi λd. Σ(_: P j (fst d)). ihA P i (snd d)
        onRec  = lam "j" I (j:
                 lam "D" descLI (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAt L I D2 muFam iArg) (_: u K)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (mu Douter j) (_: interpHoasAt L I D2 muFam iArg)) (d2:
                   sigma "_" (app (app P2 j) (fst_ d2)) (_:
                     app (app (app ihA P2) iArg) (snd_ d2))))))));
        # onPi : λS λf λD λihA λP λi λd.
        #          Σ(_: Π(s:S). P (f s) (fst d s)). ihA P i (snd d)
        onPi   = lam "S" (u L) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descLI (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAt L I D2 muFam iArg) (_: u K)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                    (_: interpHoasAt L I D2 muFam iArg)) (d2:
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
                            forall "d" (interpHoasAt L I A muFam iArg) (_: u K)))) (ihA:
                 lam "ihB" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoasAt L I B muFam iArg) (_: u K)))) (ihB:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sumPrim (interpHoasAt L I A muFam iArg)
                                  (interpHoasAt L I B muFam iArg)) (d2:
                   sumElimPrim (interpHoasAt L I A muFam iArg)
                           (interpHoasAt L I B muFam iArg)
                           (lam "_" (sumPrim (interpHoasAt L I A muFam iArg)
                                             (interpHoasAt L I B muFam iArg))
                              (_: u K))
                           (lam "a" (interpHoasAt L I A muFam iArg) (a:
                             app (app (app ihA P2) iArg) a))
                           (lam "b" (interpHoasAt L I B muFam iArg) (b:
                             app (app (app ihB P2) iArg) b))
                           d2)))))));
      # Ann-wrap Dsub for the same reason as `interpHoasAt`: `descElim`
      # infers its scrutinee, and `dispatchStep` feeds bare per-summand
      # sub-descriptions (`D1`, `restSpine`, `plus D1 restSpine`) whose
      # leaves carry `tt` at the index position. `allHoasAt`'s onArg /
      # onPi bind `S` at `U(L)` (the All result's *codomain* universe
      # `K` lives in the motive, not in S's binding); descElim's `k`
      # slot is `L`.
      in app (app (app (descElim L motive onRet onArg onRec onPi onPlus (ann Dsub descLI)) P) i) d;
  };
}
