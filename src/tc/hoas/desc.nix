# Description-level helpers (interpHoas / allHoas) and prelude descriptions
# (natDesc / listDesc / sumDesc), plus the pre-elaborated natDescTm used by
# the elaborate layer's zero/succ/ind branches to avoid re-elaborating
# natDesc on every constructor.
#
# interpHoas and allHoas elaborate to `descElim` spines that compute the
# same values as eval/desc.nix's interpF / allTyF. Every HOAS binder here
# mirrors a named interpMotive / interpOn* / mkAllMotive / allOn* in
# eval/desc.nix; conv between stuck `desc-elim` frames on the two sides
# relies on that structural match.
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
    listDesc = elem:
      let inherit (self) plus descArg descRet descRec; in
      plus descRet (descArg elem (_: descRec descRet));

    # sumDesc l r : Desc ⊤ — inl (arg : l) ⊕ inr (arg : r). Both summands
    # are `descArg _ (_: retI ttPrim)` leaves at the ⊤-slice.
    sumDesc = l: r:
      let inherit (self) plus descArg descRet; in
      plus (descArg l (_: descRet)) (descArg r (_: descRet));

    # Pre-elaborated natDesc — used by the zero/succ/nat-elim elaborate
    # branches to avoid re-elaborating on every constructor.
    natDescTm = self.elab self.natDesc;

    # interpHoas I D X i  ≡  ⟦D⟧(X) i  as a closed kernel TERM.
    #   I : U(0)       the index type
    #   D : Desc I     the description
    #   X : I → U(0)   family of recursive positions
    #   i : I          target index
    # Mirrors eval/desc.nix's interpF structurally — each binder below
    # lines up with a named closure in that file.
    interpHoas = I: D: X: i:
      let
        inherit (self) ann lam forall descI descElim sigma app eq u sumPrim;
        descII = descI I;
        iToU = forall "_" I (_: u 0);
        # motive : λ(_:Desc I). (I → U) → I → U
        motive = lam "_" descII (_:
                 forall "_" iToU (_:
                 forall "_" I (_: u 0)));
        # onRet : λ(j:I). λ(X:I→U). λ(i:I). Eq I j i
        onRet  = lam "j" I (j:
                 lam "X" iToU (_:
                 lam "i" I (i':
                   eq I j i')));
        # onArg : λ(S:U). λ(T:S→Desc I). λ(ih:Π(s:S).(I→U)→I→U). λ(X:I→U). λ(i:I).
        #           Σ(s:S). ih s X i
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: descII)) (_:
                 lam "ih" (forall "s" S (_:
                            forall "_" iToU (_: forall "_" I (_: u 0)))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "s" S (s: app (app (app ih s) X') i'))))));
        # onRec : λ(j:I). λ(D:Desc I). λ(ih:(I→U)→I→U). λ(X:I→U). λ(i:I).
        #           Σ(_:X j). ih X i
        onRec  = lam "j" I (j:
                 lam "D" descII (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u 0))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (app X' j) (_: app (app ih X') i'))))));
        # onPi : λ(S:U). λ(f:S→I). λ(D:Desc I). λ(ih:(I→U)→I→U). λ(X:I→U). λ(i:I).
        #          Σ(_:Π(s:S). X(f s)). ih X i
        onPi   = lam "S" (u 0) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descII (_:
                 lam "ih" (forall "_" iToU (_: forall "_" I (_: u 0))) (ih:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sigma "_" (forall "s" S (s: app X' (app f s)))
                             (_: app (app ih X') i')))))));
        # onPlus : λ(A:Desc I). λ(B:Desc I). λ(ihA:(I→U)→I→U). λ(ihB:(I→U)→I→U).
        #            λ(X:I→U). λ(i:I). Sum (ihA X i) (ihB X i)
        onPlus = lam "A" descII (_:
                 lam "B" descII (_:
                 lam "ihA" (forall "_" iToU (_: forall "_" I (_: u 0))) (ihA:
                 lam "ihB" (forall "_" iToU (_: forall "_" I (_: u 0))) (ihB:
                 lam "X" iToU (X':
                 lam "i" I (i':
                   sumPrim (app (app ihA X') i') (app (app ihB X') i')))))));
      # `descElim`'s INFER rule synthesises its scrutinee, and a bare
      # `retI ttPrim` / plus-coproduct leaf is check-only (no INFER rule
      # for `tt`). Ann-wrap D against `Desc I` so the scrutinee position
      # stays inferable for every caller — parallels the CHECK-mode rewire
      # of `mu` at `check/type.nix:75-90`.
      in app (app (descElim motive onRet onArg onRec onPi onPlus (ann D descII)) X) i;

    # allHoas I Douter Dsub P i d ≡ All Douter Dsub P i d — the
    # inductive-hypothesis TYPE for d : ⟦Dsub⟧(μ Douter) i, where
    # P : (i:I) → μ Douter i → U. The motive closes over Douter (and I);
    # the four cases mention Douter only through P's domain shape.
    allHoas = I: Douter: Dsub: P: i: d:
      let
        inherit (self) ann lam forall descI descElim sigma app fst_ snd_
                        u unitPrim mu interpHoas sumPrim sumElimPrim;
        descII = descI I;
        # muFam : λi. μ Douter i — the family fed to interpHoas as X.
        muFam = lam "_i" I (iArg: mu Douter iArg);
        pTy = forall "i" I (iArg: forall "_" (mu Douter iArg) (_: u 0));
        # motive : λ(D:Desc I).
        #   Π(P:(i:I) → μ Douter i → U). Π(i:I). Π(d:⟦D⟧(μ Douter) i). U
        motive = lam "_" descII (Dm:
                 forall "P" pTy (_:
                 forall "i" I (iArg:
                 forall "d" (interpHoas I Dm muFam iArg) (_: u 0))));
        # onRet : λj λP λi λd. Unit
        onRet  = lam "j" I (_:
                 lam "P" pTy (_:
                 lam "i" I (_:
                 lam "d" unitPrim (_: unitPrim))));
        # onArg : λS λT λihA λP λi λd. ihA (fst d) P i (snd d)
        onArg  = lam "S" (u 0) (S:
                 lam "T" (forall "_" S (_: descII)) (T:
                 lam "ihA" (forall "s" S (s:
                            forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I (app T s) muFam iArg) (_: u 0))))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "s" S (s: interpHoas I (app T s) muFam iArg)) (d2:
                   app (app (app (app ihA (fst_ d2)) P2) iArg) (snd_ d2)))))));
        # onRec : λj λD λihA λP λi λd. Σ(_: P j (fst d)). ihA P i (snd d)
        onRec  = lam "j" I (j:
                 lam "D" descII (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I D2 muFam iArg) (_: u 0)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (mu Douter j) (_: interpHoas I D2 muFam iArg)) (d2:
                   sigma "_" (app (app P2 j) (fst_ d2)) (_:
                     app (app (app ihA P2) iArg) (snd_ d2))))))));
        # onPi : λS λf λD λihA λP λi λd.
        #          Σ(_: Π(s:S). P (f s) (fst d s)). ihA P i (snd d)
        onPi   = lam "S" (u 0) (S:
                 lam "f" (forall "_" S (_: I)) (f:
                 lam "D" descII (D2:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I D2 muFam iArg) (_: u 0)))) (ihA:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sigma "_" (forall "s" S (s: mu Douter (app f s)))
                                    (_: interpHoas I D2 muFam iArg)) (d2:
                   sigma "_"
                     (forall "s" S (s:
                       app (app P2 (app f s)) (app (fst_ d2) s)))
                     (_: app (app (app ihA P2) iArg) (snd_ d2)))))))));
        # onPlus : λA λB λihA λihB λP λi λd. sumElim on d: inl a → ihA P i a, inr b → ihB P i b.
        # d : Sum (⟦A⟧ μFam i) (⟦B⟧ μFam i) by interp of plus (kernel Sum).
        onPlus = lam "A" descII (A:
                 lam "B" descII (B:
                 lam "ihA" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I A muFam iArg) (_: u 0)))) (ihA:
                 lam "ihB" (forall "P" pTy (_:
                            forall "i" I (iArg:
                            forall "d" (interpHoas I B muFam iArg) (_: u 0)))) (ihB:
                 lam "P" pTy (P2:
                 lam "i" I (iArg:
                 lam "d" (sumPrim (interpHoas I A muFam iArg)
                                  (interpHoas I B muFam iArg)) (d2:
                   sumElimPrim (interpHoas I A muFam iArg)
                           (interpHoas I B muFam iArg)
                           (lam "_" (sumPrim (interpHoas I A muFam iArg)
                                             (interpHoas I B muFam iArg))
                              (_: u 0))
                           (lam "a" (interpHoas I A muFam iArg) (a:
                             app (app (app ihA P2) iArg) a))
                           (lam "b" (interpHoas I B muFam iArg) (b:
                             app (app (app ihB P2) iArg) b))
                           d2)))))));
      # Ann-wrap Dsub for the same reason as `interpHoas`: `descElim`
      # infers its scrutinee, and `dispatchStep` feeds bare per-summand
      # sub-descriptions (`D1`, `restSpine`, `plus D1 restSpine`) whose
      # leaves carry `tt` at the index position.
      in app (app (app (descElim motive onRet onArg onRec onPi onPlus (ann Dsub descII)) P) i) d;
  };
}
