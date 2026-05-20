# Decidability surface (HoTT-aligned, zero kernel additions).
#
# All bindings here are pure HOAS aliases over existing primitives
# (`sigma` / `sum` / `forall` / `unit` / `void` / `inl` / `inr` /
# `sumElim`). No new `_htag` is introduced; the kernel sees only
# pre-existing Σ / + / Π / Unit / Fin 0 / mu reductions.
#
# Logical connectives follow HoTT Book §1.7 (logical constants as
# types): `True = ⊤`, `False = ⊥`, `And = ×`, `Or = +`, `Not P = P → ⊥`,
# `Iff = ⇔`. The `Dec` layer follows Agda `Relation.Nullary.Dec`
# (`Dec P := P ⊎ ¬ P`) with `yes` / `no` as `inl` / `inr` and `decElim`
# as a `sumElim` wrapper at universe level zero.
#
# Naming caveats:
# - `True` / `False` are capitalised to signal "propositional-level
#   constant" and to leave `BoolDT`'s `true_` / `false_` (Bool data
#   values) unshadowed.
# - `or_` carries a trailing underscore because `or` is reserved in
#   Nix identifier position (mirrors `true_` / `false_`).
{ self, ... }:
{
  scope = {
    True  = self.unit;
    False = self.void;
    and   = P: Q: self.sigma "_" P (_: Q);
    or_   = P: Q: self.sum P Q;
    not   = P: self.forall "_" P (_: self.void);
    iff   = P: Q: self.and (self.forall "_" P (_: Q))
                           (self.forall "_" Q (_: P));

    dec   = P: self.sum P (self.not P);
    yes   = P: p: self.inl P (self.not P) p;
    no    = P: r: self.inr P (self.not P) r;
    decElim = P: motive: oy: on: d:
      self.sumElim 0 P (self.not P) motive oy on d;

    # Compositional decidability — Agda `Relation.Nullary.Product` /
    # `.Sum` / `.Negation`. Each takes `dec P` (and `dec Q` where binary)
    # and returns `dec (and P Q)` / `dec (or_ P Q)` / `dec (not P)` by
    # casing on the inputs and either re-packaging the proofs or building
    # a refutation that destructs the conjunctive / disjunctive witness.
    decAnd = P: Q: dp: dq:
      let
        inherit (self) lam app fst_ snd_ pair;
        result = self.and P Q;
      in self.decElim P
           (lam "_" (self.dec P) (_: self.dec result))
           (lam "p" P (p:
             self.decElim Q
               (lam "_" (self.dec Q) (_: self.dec result))
               (lam "q" Q (q: self.yes result (pair p q)))
               (lam "nq" (self.not Q) (nq:
                 self.no result
                   (lam "pq" result (pq: app nq (snd_ pq)))))
               dq))
           (lam "np" (self.not P) (np:
             self.no result
               (lam "pq" result (pq: app np (fst_ pq)))))
           dp;

    decOr = P: Q: dp: dq:
      let
        inherit (self) lam app inl inr sumElim;
        result = self.or_ P Q;
      in self.decElim P
           (lam "_" (self.dec P) (_: self.dec result))
           (lam "p" P (p: self.yes result (inl P Q p)))
           (lam "np" (self.not P) (np:
             self.decElim Q
               (lam "_" (self.dec Q) (_: self.dec result))
               (lam "q" Q (q: self.yes result (inr P Q q)))
               (lam "nq" (self.not Q) (nq:
                 self.no result
                   (lam "pOq" result (pOq:
                     sumElim 0 P Q
                       (lam "_s" result (_: self.void))
                       (lam "pp" P (pp: app np pp))
                       (lam "qq" Q (qq: app nq qq))
                       pOq))))
               dq))
           dp;

    decNot = P: dp:
      let inherit (self) lam app; in
      self.decElim P
        (lam "_" (self.dec P) (_: self.dec (self.not P)))
        (lam "p" P (p:
          self.no (self.not P)
            (lam "np" (self.not P) (np: app np p))))
        (lam "np" (self.not P) (np:
          self.yes (self.not P) np))
        dp;

    # ===== Nat no-confusion lemmas =====
    # Building blocks for `decideEqNat` / `decideLeNat`. Each is a closed
    # HOAS term whose body uses `bootJ` (no-confusion via discriminator
    # motive — McBride 2000 PhD §3.5) or `ind` (Nat-induction).

    # predNat : Nat -> Nat — saturating predecessor. `predNat zero = zero`;
    # `predNat (suc m) = m`. Built via `ind` with constant Nat motive.
    predNat =
      let inherit (self) lam ind nat zero; in
      lam "n" nat (nv:
        ind 0
          (lam "_n" nat (_: nat))
          zero
          (lam "k" nat (k: lam "_ih" nat (_: k)))
          nv);

    # eqCongSucc m n e : Eq Nat (suc m) (suc n) — congruence of `suc` over
    # propositional equality. bootJ at motive
    #   λ(x:Nat) (_:Eq Nat m x). Eq Nat (suc m) (suc x).
    # Base case (x = m) demands `Eq Nat (suc m) (suc m)`, satisfied by refl.
    eqCongSucc = m: n: e:
      let inherit (self) lam nat succ bootEq bootJ bootRefl; in
      bootJ nat m
        (lam "x" nat (x: lam "_eq" (bootEq nat m x) (_:
          bootEq nat (succ m) (succ x))))
        bootRefl
        n
        e;

    # eqInjSucc m n e : Eq Nat m n — injectivity of `suc`. bootJ at motive
    #   λ(x:Nat) (_:Eq Nat (suc m) x). Eq Nat m (predNat x).
    # Base case (x = suc m) demands `Eq Nat m (predNat (suc m))`; β on
    # `predNat (suc m)` yields `Eq Nat m m`, satisfied by refl. Result at
    # x = suc n yields `Eq Nat m (predNat (suc n)) ≡ Eq Nat m n`.
    eqInjSucc = m: n: e:
      let inherit (self) lam app nat succ bootEq bootJ bootRefl; in
      bootJ nat (succ m)
        (lam "x" nat (x: lam "_eq" (bootEq nat (succ m) x) (_:
          bootEq nat m (app self.predNat x))))
        bootRefl
        (succ n)
        e;

    # eqRefutSuccZero m e : void — refutation of `Eq Nat (suc m) zero`.
    # bootJ at motive `λ(x:Nat) (_:Eq Nat (suc m) x). natCaseU void unit x`.
    # Base case (x = suc m) demands `natCaseU void unit (suc m) ≡ unit`,
    # filled by `tt`. Result at x = zero is `natCaseU void unit zero ≡ void`.
    eqRefutSuccZero = m: e:
      let inherit (self) lam app nat zero succ bootEq bootJ ttPrim natCaseU
                          unit void; in
      bootJ nat (succ m)
        (lam "x" nat (x: lam "_eq" (bootEq nat (succ m) x) (_:
          app (natCaseU void unit) x)))
        ttPrim
        zero
        e;

    # eqRefutZeroSucc n e : void — symmetric refutation of `Eq Nat zero (suc n)`.
    # bootJ at motive `λ(x:Nat) (_:Eq Nat zero x). natCaseU unit void x`.
    eqRefutZeroSucc = n: e:
      let inherit (self) lam app nat zero succ bootEq bootJ ttPrim natCaseU
                          unit void; in
      bootJ nat zero
        (lam "x" nat (x: lam "_eq" (bootEq nat zero x) (_:
          app (natCaseU unit void) x)))
        ttPrim
        (succ n)
        e;

    # ===== Le no-confusion / injectivity =====

    # leRefutSuccZero m pf : void — refutation of `Le (suc m) zero`.
    # leElim at motive `λm' n' _. natCaseU unit (natCaseU void unit n') m'`:
    # at `m' = 0` the motive collapses to `unit` (so leZ case fills with `tt`);
    # at `m' = suc _` it becomes `natCaseU void unit n'`, which at `n' = 0`
    # is `void` (refutation target) and at `n' = suc _` is `unit` (so leSS
    # case also fills with `tt`).
    leRefutSuccZero = m: pf:
      let inherit (self) lam app nat zero succ unit void le leElim natCaseU
                          ttPrim; in
      let motiveType = m': n':
            app (natCaseU unit (app (natCaseU void unit) n')) m';
          K  = lam "m'" nat (mp: lam "n'" nat (np: lam "_pf" (le mp np) (_:
                 motiveType mp np)));
          Pz = lam "_n" nat (_: ttPrim);
          Ps = lam "_m" nat (_: lam "_n" nat (_:
                 lam "_lemn" unit (_: lam "_ih" unit (_: ttPrim))));
      in leElim 0 K Pz Ps (succ m) zero pf;

    # leInjSS m n pf : Le m n — injectivity of `leSS`. leElim at motive
    # `λm' n' _. Le (predNat m') (predNat n')`. leZ-case at (0, n) yields
    # `Le 0 (predNat n)`, filled by `leZ (predNat n)`. leSS-case at
    # (suc m', suc n') with `lemn : Le m' n'` yields `Le m' n'` (β on
    # `predNat (suc _)`), filled by `lemn`.
    leInjSS = m: n: pf:
      let inherit (self) lam app nat succ le leZ leElim; in
      let K  = lam "m'" nat (mp: lam "n'" nat (np: lam "_pf" (le mp np) (_:
                 le (app self.predNat mp) (app self.predNat np))));
          Pz = lam "n" nat (nv: leZ (app self.predNat nv));
          Ps = lam "m'" nat (_: lam "n'" nat (_:
                 lam "lemn" (le _ _) (lemn:
                   lam "_ih" (self.le _ _) (_: lemn))));
      in leElim 0 K Pz Ps (succ m) (succ n) pf;

    # ===== Decidability witnesses over Nat =====
    # Agda `Data.Nat.Properties._≟_` and `_≤?_` — exact textbook recipe.
    # Both perform simultaneous structural recursion via outer `ind` on
    # `m` followed by inner `ind` on `n`. The IH from the outer ind is
    # used to decide the recursive sub-proposition in the (suc m, suc n)
    # case; the result is then lifted by `eqCongSucc` / `leSS` (yes) or
    # `eqInjSucc` / `leInjSS` (no).

    # Closed-term HOAS body retained under `<name>Hoas` so the elaborator
    # can pre-elaborate it once at module load. The public `<name>` is an
    # opaque `pre-elab` HOAS node carrying the cached `Tm`; call sites
    # like `app (app decideEqNat m) n` short-circuit elaboration of the
    # decider body to a single attrset lookup.
    decideEqNatHoas =
      let
        inherit (self) lam app forall ind nat zero succ bootEq bootRefl
                        dec yes no decElim not;
        decAt = mv: nv: dec (bootEq nat mv nv);
        outerMot = lam "_m" nat (mv: forall "_n" nat (nv: decAt mv nv));

        baseM = lam "n" nat (nv:
          ind 0
            (lam "_n" nat (n': decAt zero n'))
            (yes (bootEq nat zero zero) bootRefl)
            (lam "n'" nat (np: lam "_ihN" (decAt zero np) (_:
              no (bootEq nat zero (succ np))
                (lam "e" (bootEq nat zero (succ np)) (e:
                  self.eqRefutZeroSucc np e)))))
            nv);

        stepM = lam "m'" nat (mp:
                lam "ihM" (forall "_n" nat (n': decAt mp n')) (ihM:
                  lam "n" nat (nv:
                    ind 0
                      (lam "_n" nat (n': decAt (succ mp) n'))
                      (no (bootEq nat (succ mp) zero)
                        (lam "e" (bootEq nat (succ mp) zero) (e:
                          self.eqRefutSuccZero mp e)))
                      (lam "n'" nat (np:
                        lam "_ihN" (decAt (succ mp) np) (_:
                          decElim (bootEq nat mp np)
                            (lam "_d" (dec (bootEq nat mp np)) (_:
                              decAt (succ mp) (succ np)))
                            (lam "emn" (bootEq nat mp np) (emn:
                              yes (bootEq nat (succ mp) (succ np))
                                  (self.eqCongSucc mp np emn)))
                            (lam "nemn" (not (bootEq nat mp np)) (nemn:
                              no (bootEq nat (succ mp) (succ np))
                                (lam "e" (bootEq nat (succ mp) (succ np)) (e:
                                  app nemn (self.eqInjSucc mp np e)))))
                            (app ihM np))))
                      nv)));
      in lam "m" nat (mv: ind 0 outerMot baseM stepM mv);
    decideEqNatTm = self.elab self.decideEqNatHoas;
    decideEqNat = { _htag = "pre-elab"; tm = self.decideEqNatTm; };

    decideLeNatHoas =
      let
        inherit (self) lam app forall ind nat zero succ
                        dec yes no decElim not le leZ leSS;
        decAt = mv: nv: dec (le mv nv);
        outerMot = lam "_m" nat (mv: forall "_n" nat (nv: decAt mv nv));

        baseM = lam "n" nat (nv: yes (le zero nv) (leZ nv));

        stepM = lam "m'" nat (mp:
                lam "ihM" (forall "_n" nat (n': decAt mp n')) (ihM:
                  lam "n" nat (nv:
                    ind 0
                      (lam "_n" nat (n': decAt (succ mp) n'))
                      (no (le (succ mp) zero)
                        (lam "pf" (le (succ mp) zero) (pf:
                          self.leRefutSuccZero mp pf)))
                      (lam "n'" nat (np:
                        lam "_ihN" (decAt (succ mp) np) (_:
                          decElim (le mp np)
                            (lam "_d" (dec (le mp np)) (_:
                              decAt (succ mp) (succ np)))
                            (lam "lemn" (le mp np) (lemn:
                              yes (le (succ mp) (succ np))
                                  (leSS mp np lemn)))
                            (lam "nlemn" (not (le mp np)) (nlemn:
                              no (le (succ mp) (succ np))
                                (lam "pf" (le (succ mp) (succ np)) (pf:
                                  app nlemn (self.leInjSS mp np pf)))))
                            (app ihM np))))
                      nv)));
      in lam "m" nat (mv: ind 0 outerMot baseM stepM mv);
    decideLeNatTm = self.elab self.decideLeNatHoas;
    decideLeNat = { _htag = "pre-elab"; tm = self.decideLeNatTm; };

    # ===== IntZ literals and no-confusion =====

    # intzLit n — Nix-meta bridge from a Nix integer to the canonical
    # `IntZ` HOAS encoding. Mirrors `natLit`'s shape (combinators.nix-
    # local helper, no kernel reflection). `n >= 0` produces `pos n`;
    # `n < 0` produces `negSucc (-n - 1)` so that `intzLit (-1) =
    # negSucc 0` and `intzLit (-3) = negSucc 2`.
    intzLit = n:
      if n >= 0
      then self.intzPos     (self.natLit n)
      else self.intzNegSucc (self.natLit ((-n) - 1));

    # signsDiffer m n e : void — McBride no-confusion lemma refuting
    # `Eq IntZ (pos m) (negSucc n)`. Builds a sign-discriminator
    # `sgnDisc : IntZ → U(0)` via `intzElim` returning `unit` on `pos`
    # and `void` on `negSucc`, then `bootJ`-transports `tt : sgnDisc
    # (pos m)` along `e` to land at `sgnDisc (negSucc n) ≡ void`.
    # Generalises the absurdFin0 / eqRefutSuccZero technique to a
    # constructor mismatch on a 2-constructor non-indexed datatype.
    signsDiffer = m: n: e:
      let
        inherit (self) lam nat intz intzPos intzNegSucc intzElim
                        bootEq bootJ ttPrim unit void u;
      in bootJ intz (intzPos m)
           (lam "x" intz (x: lam "_eq" (bootEq intz (intzPos m) x) (_:
             intzElim 1
               (lam "_z" intz (_: u 0))
               (lam "_n" nat (_: unit))
               (lam "_n" nat (_: void))
               x)))
           ttPrim
           (intzNegSucc n)
           e;

    # intzLe : IntZ → IntZ → U(0) — Agda `Data.Integer.Base._≤_` four-
    # case definition via `intzElim` cascade with U-typed motive.
    #
    # | m         | n         | intzLe m n           |
    # |-----------|-----------|----------------------|
    # | pos m'    | pos n'    | le m' n'  (Nat)      |
    # | pos _     | negSucc _ | void                 |
    # | negSucc _ | pos _     | unit                 |
    # | negSucc m'| negSucc n'| le n' m'  (flipped)  |
    #
    # Mirrors Agda exactly. The `negSucc` ordering is flipped because
    # `negSucc` is monotonically decreasing in its argument (`negSucc 0
    # = -1`, `negSucc 1 = -2`, …). A future `decideLeIntZ` decision
    # procedure cascades on the same four-case structure, delegating to
    # `decideLeNat` for both Nat-typed sub-cases.
    #
    # Named `intzLe` (not `leZ`) to avoid clashing with `leZ`, the
    # `z≤n` constructor of `LeDT`. `intzLe` is the IntZ ordering
    # type-family; `leZ` is a witness constructor for Nat ≤.
    intzLe = m: n:
      let
        inherit (self) lam app nat intz intzElim le unit void u;
      in intzElim 1
           (lam "_z" intz (_: u 0))
           (lam "mp" nat (mp:
             intzElim 1
               (lam "_z" intz (_: u 0))
               (lam "np" nat (np: le mp np))
               (lam "_np" nat (_: void))
               n))
           (lam "mp" nat (mp:
             intzElim 1
               (lam "_z" intz (_: u 0))
               (lam "_np" nat (_: unit))
               (lam "np" nat (np: le np mp))
               n))
           m;

    # ===== IntZ no-confusion / cong / injectivity =====
    # IntZ-lifted analogues of the Nat lemmas above.

    # signsDifferRev m n e : void — refutation of `Eq IntZ (negSucc m)
    # (pos n)`. Same shape as `signsDiffer` with the sign discriminator's
    # pos / negSucc targets swapped (`void` on pos, `unit` on negSucc).
    signsDifferRev = m: n: e:
      let
        inherit (self) lam nat intz intzPos intzNegSucc intzElim
                        bootEq bootJ ttPrim unit void u;
      in bootJ intz (intzNegSucc m)
           (lam "x" intz (x: lam "_eq" (bootEq intz (intzNegSucc m) x) (_:
             intzElim 1
               (lam "_z" intz (_: u 0))
               (lam "_n" nat (_: void))
               (lam "_n" nat (_: unit))
               x)))
           ttPrim
           (intzPos n)
           e;

    # intzPosCong m n e : Eq IntZ (pos m) (pos n) — congruence of
    # `intzPos`. bootJ at motive `λ(x:Nat) (_:Eq Nat m x). Eq IntZ (pos m)
    # (pos x)`. Mirror of `eqCongSucc` with `intzPos` in place of `succ`.
    intzPosCong = m: n: e:
      let inherit (self) lam nat intz intzPos bootEq bootJ bootRefl; in
      bootJ nat m
        (lam "x" nat (x: lam "_eq" (bootEq nat m x) (_:
          bootEq intz (intzPos m) (intzPos x))))
        bootRefl
        n
        e;

    # intzNegSuccCong m n e : Eq IntZ (negSucc m) (negSucc n) — symmetric
    # congruence for `intzNegSucc`.
    intzNegSuccCong = m: n: e:
      let inherit (self) lam nat intz intzNegSucc bootEq bootJ bootRefl; in
      bootJ nat m
        (lam "x" nat (x: lam "_eq" (bootEq nat m x) (_:
          bootEq intz (intzNegSucc m) (intzNegSucc x))))
        bootRefl
        n
        e;

    # intzDecode : intz → Nat — sign-erasing payload extractor.
    # `intzPos n ↦ n`, `intzNegSucc n ↦ n`. Used as the bootJ motive
    # discriminator for constructor injectivity below.
    intzDecode =
      let inherit (self) lam nat intz intzElim; in
      lam "z" intz (zv:
        intzElim 0
          (lam "_z" intz (_: nat))
          (lam "k" nat (k: k))
          (lam "k" nat (k: k))
          zv);

    # intzPosInjective m n e : Eq Nat m n — injectivity of `intzPos`.
    # bootJ at motive `λ(x:intz) _. Eq Nat m (intzDecode x)`; β on the
    # decoder collapses to `Eq Nat m m` at the base case and `Eq Nat m n`
    # at the target.
    intzPosInjective = m: n: e:
      let inherit (self) lam app nat intz intzPos
                          bootEq bootJ bootRefl; in
      bootJ intz (intzPos m)
        (lam "x" intz (xv: lam "_eq" (bootEq intz (intzPos m) xv) (_:
          bootEq nat m (app self.intzDecode xv))))
        bootRefl
        (intzPos n)
        e;

    # intzNegSuccInjective m n e : Eq Nat m n — symmetric injectivity for
    # `intzNegSucc`, same `intzDecode` motive.
    intzNegSuccInjective = m: n: e:
      let inherit (self) lam app nat intz intzNegSucc
                          bootEq bootJ bootRefl; in
      bootJ intz (intzNegSucc m)
        (lam "x" intz (xv: lam "_eq" (bootEq intz (intzNegSucc m) xv) (_:
          bootEq nat m (app self.intzDecode xv))))
        bootRefl
        (intzNegSucc n)
        e;

    # ===== Decidability witnesses over IntZ =====
    # Agda `Data.Integer.Properties._≟_` and `_≤?_` — four-case sign
    # cascade. Outer `intzElim` on `m`, inner `intzElim` on `n`. Same-sign
    # quadrants delegate to `decideEqNat` / `decideLeNat` and lift via
    # cong / injectivity (Eq) or directly (Le, reduction-bridged). Cross-
    # sign Eq cases refute with `signsDiffer` / `signsDifferRev`; cross-
    # sign Le cases collapse to `void` / `unit` via `intzLe`'s reduction.

    decideEqIntZHoas =
      let
        inherit (self) lam app nat intz intzPos intzNegSucc intzElim
                        bootEq dec yes no decElim not;
        decAt = mv: nv: dec (bootEq intz mv nv);
      in lam "m" intz (mv:
         lam "n" intz (nv:
           intzElim 0
             (lam "_m" intz (mp': decAt mp' nv))
             (lam "mp" nat (mp:
               intzElim 0
                 (lam "_n" intz (np': decAt (intzPos mp) np'))
                 (lam "np" nat (np:
                   # pos-pos: delegate to decideEqNat; lift via cong / inj.
                   decElim (bootEq nat mp np)
                     (lam "_d" (dec (bootEq nat mp np)) (_:
                       decAt (intzPos mp) (intzPos np)))
                     (lam "emn" (bootEq nat mp np) (emn:
                       yes (bootEq intz (intzPos mp) (intzPos np))
                           (self.intzPosCong mp np emn)))
                     (lam "nemn" (not (bootEq nat mp np)) (nemn:
                       no (bootEq intz (intzPos mp) (intzPos np))
                         (lam "e" (bootEq intz (intzPos mp) (intzPos np)) (e:
                           app nemn (self.intzPosInjective mp np e)))))
                     (app (app self.decideEqNat mp) np)))
                 (lam "np" nat (np:
                   # pos-negSucc: signsDiffer refutes any equality witness.
                   no (bootEq intz (intzPos mp) (intzNegSucc np))
                     (lam "e" (bootEq intz (intzPos mp) (intzNegSucc np)) (e:
                       self.signsDiffer mp np e))))
                 nv))
             (lam "mp" nat (mp:
               intzElim 0
                 (lam "_n" intz (np': decAt (intzNegSucc mp) np'))
                 (lam "np" nat (np:
                   # negSucc-pos: signsDifferRev refutes.
                   no (bootEq intz (intzNegSucc mp) (intzPos np))
                     (lam "e" (bootEq intz (intzNegSucc mp) (intzPos np)) (e:
                       self.signsDifferRev mp np e))))
                 (lam "np" nat (np:
                   # negSucc-negSucc: delegate to decideEqNat; lift.
                   decElim (bootEq nat mp np)
                     (lam "_d" (dec (bootEq nat mp np)) (_:
                       decAt (intzNegSucc mp) (intzNegSucc np)))
                     (lam "emn" (bootEq nat mp np) (emn:
                       yes (bootEq intz (intzNegSucc mp) (intzNegSucc np))
                           (self.intzNegSuccCong mp np emn)))
                     (lam "nemn" (not (bootEq nat mp np)) (nemn:
                       no (bootEq intz (intzNegSucc mp) (intzNegSucc np))
                         (lam "e" (bootEq intz (intzNegSucc mp) (intzNegSucc np)) (e:
                           app nemn (self.intzNegSuccInjective mp np e)))))
                     (app (app self.decideEqNat mp) np)))
                 nv))
             mv));
    decideEqIntZTm = self.elab self.decideEqIntZHoas;
    decideEqIntZ = { _htag = "pre-elab"; tm = self.decideEqIntZTm; };

    decideLeIntZHoas =
      let
        inherit (self) lam app nat intz intzPos intzNegSucc intzElim
                        dec yes no decElim not intzLe le ttPrim;
        decAt = mv: nv: dec (intzLe mv nv);
      in lam "m" intz (mv:
         lam "n" intz (nv:
           intzElim 0
             (lam "_m" intz (mp': decAt mp' nv))
             (lam "mp" nat (mp:
               intzElim 0
                 (lam "_n" intz (np': decAt (intzPos mp) np'))
                 (lam "np" nat (np:
                   # pos-pos: intzLe (pos mp) (pos np) ≡ le mp np; delegate.
                   decElim (le mp np)
                     (lam "_d" (dec (le mp np)) (_:
                       decAt (intzPos mp) (intzPos np)))
                     (lam "lemn" (le mp np) (lemn:
                       yes (intzLe (intzPos mp) (intzPos np)) lemn))
                     (lam "nlemn" (not (le mp np)) (nlemn:
                       no (intzLe (intzPos mp) (intzPos np))
                         (lam "pf" (intzLe (intzPos mp) (intzPos np)) (pf:
                           app nlemn pf))))
                     (app (app self.decideLeNat mp) np)))
                 (lam "np" nat (np:
                   # pos-negSucc: target reduces to `void`; refutation is identity.
                   no (intzLe (intzPos mp) (intzNegSucc np))
                     (lam "pf" (intzLe (intzPos mp) (intzNegSucc np)) (pf:
                       pf))))
                 nv))
             (lam "mp" nat (mp:
               intzElim 0
                 (lam "_n" intz (np': decAt (intzNegSucc mp) np'))
                 (lam "np" nat (np:
                   # negSucc-pos: target reduces to `unit`; inhabited by `tt`.
                   yes (intzLe (intzNegSucc mp) (intzPos np)) ttPrim))
                 (lam "np" nat (np:
                   # negSucc-negSucc: target reduces to `le np mp` (flipped
                   # — negSucc is monotonically decreasing); delegate.
                   decElim (le np mp)
                     (lam "_d" (dec (le np mp)) (_:
                       decAt (intzNegSucc mp) (intzNegSucc np)))
                     (lam "lemn" (le np mp) (lemn:
                       yes (intzLe (intzNegSucc mp) (intzNegSucc np)) lemn))
                     (lam "nlemn" (not (le np mp)) (nlemn:
                       no (intzLe (intzNegSucc mp) (intzNegSucc np))
                         (lam "pf" (intzLe (intzNegSucc mp) (intzNegSucc np)) (pf:
                           app nlemn pf))))
                     (app (app self.decideLeNat np) mp)))
                 nv))
             mv));
    decideLeIntZTm = self.elab self.decideLeIntZHoas;
    decideLeIntZ = { _htag = "pre-elab"; tm = self.decideLeIntZTm; };

    # ===== Refinement-predicate carrier =====

    # refinementPred dom predFn : U(_) — Σ-encoded refinement carrier
    # `Σ (x : dom) (Dec (predFn x))`. McBride & McKinna 2004 "The view
    # from the left"; Pollack 2002. `predFn` is a Nix-meta predicate
    # `Hoas -> Hoas` matching the surface convention of `sigma` /
    # `forall` / `lam`; the user need not pre-encode it as a HOAS lambda.
    # Inhabitants pair a witness with a decision proof; the decision
    # procedure is supplied at the value level (`pair v (decideProc v)`).
    refinementPred = dom: predFn:
      self.sigma "x" dom (xv: self.dec (predFn xv));
  };
  tests = {};
  __docs = {
    False = {
      description = "False: propositional falsehood — alias for `void = Fin 0` per HoTT Book §1.7 (`False = ⊥`). The empty type is vacuous by McBride no-confusion on `Eq Nat (succ m) zero`.";
      signature = "False : Hoas";
    };
    True = {
      description = "True: propositional truth — alias for `unit` per HoTT Book §1.7 (`True = ⊤`). Distinct from `BoolDT`'s data-level `true_`.";
      signature = "True : Hoas";
    };
    and = {
      description = "and: propositional conjunction — `and P Q := Σ (_:P). Q` per HoTT Book §1.7. Elaborates to a sigma.";
      signature = "and : Hoas -> Hoas -> Hoas";
    };
    dec = {
      description = "dec: decidability proposition — `dec P := P ⊎ ¬ P` per Agda `Relation.Nullary.Dec`. Defined as `sum P (not P)`; inhabitants built via `yes` / `no` and eliminated via `decElim`.";
      signature = "dec : Hoas -> Hoas";
    };
    decAnd = {
      description = "decAnd: conjunction decidability — `decAnd P Q dp dq : dec (and P Q)` given `dp : dec P` and `dq : dec Q`. Both yes ⇒ yes (pair); either no ⇒ no (refute via fst_/snd_).";
      signature = "decAnd : Hoas -> Hoas -> Hoas -> Hoas -> Hoas  -- P, Q, decP, decQ";
    };
    decElim = {
      description = "decElim: eliminator for `dec P` — `decElim P motive oy on d` discharges `d : dec P` against motive `M : dec P -> U(0)` with branches `oy : (p:P) -> M (yes _ p)` and `on : (r: not P) -> M (no _ r)`. Forwards to `sumElim` at level 0.";
      signature = "decElim : Hoas -> Hoas -> Hoas -> Hoas -> Hoas -> Hoas  -- P, motive, oyes, ono, d";
    };
    decNot = {
      description = "decNot: negation decidability — `decNot P dp : dec (not P)`. yes ⇒ no (negation contradicts the proof); no ⇒ yes (the refutation IS the negation witness).";
      signature = "decNot : Hoas -> Hoas -> Hoas  -- P, decP";
    };
    decOr = {
      description = "decOr: disjunction decidability — `decOr P Q dp dq : dec (or_ P Q)`. Either yes ⇒ yes (inl/inr); both no ⇒ no (refute via sumElim).";
      signature = "decOr : Hoas -> Hoas -> Hoas -> Hoas -> Hoas  -- P, Q, decP, decQ";
    };
    decideEqIntZ = {
      description = "decideEqIntZ: decidability of IntZ equality — `decideEqIntZ m n : dec (Eq IntZ m n)`. Four-case `intzElim` sign cascade; same-sign quadrants delegate to `decideEqNat` and lift via cong / injectivity; cross-sign quadrants refute via `signsDiffer` / `signsDifferRev`. Agda `Data.Integer.Properties._≟_`.";
      signature = "decideEqIntZ : Hoas  -- closed kernel function Π m. Π n. dec (Eq IntZ m n)";
    };
    decideEqNat = {
      description = "decideEqNat: decidability of Nat equality — `decideEqNat m n : dec (Eq Nat m n)`. Closed kernel `lam`-term performing simultaneous structural recursion on both arguments. Agda `Data.Nat.Properties._≟_`.";
      signature = "decideEqNat : Hoas  -- closed kernel function Π m. Π n. dec (Eq Nat m n)";
    };
    decideLeIntZ = {
      description = "decideLeIntZ: decidability of `intzLe` — `decideLeIntZ m n : dec (intzLe m n)`. Four-case `intzElim` sign cascade following `intzLe`'s quadrant table; pos-pos delegates to `decideLeNat`, pos-negSucc returns `no` (target reduces to `void`), negSucc-pos returns `yes tt` (target reduces to `unit`), negSucc-negSucc delegates to `decideLeNat` at flipped arguments. Agda `Data.Integer.Properties._≤?_`.";
      signature = "decideLeIntZ : Hoas  -- closed kernel function Π m. Π n. dec (intzLe m n)";
    };
    decideLeNat = {
      description = "decideLeNat: decidability of `Le` — `decideLeNat m n : dec (le m n)`. Closed kernel `lam`-term following Agda `Data.Nat.Properties._≤?_` four-case recipe (zero-zero, zero-suc, suc-zero, suc-suc).";
      signature = "decideLeNat : Hoas  -- closed kernel function Π m. Π n. dec (le m n)";
    };
    eqCongSucc = {
      description = "eqCongSucc: congruence of `suc` — `eqCongSucc m n e : Eq Nat (suc m) (suc n)` given `e : Eq Nat m n`. bootJ at motive `λx _. Eq Nat (suc m) (suc x)`; base case satisfied by `bootRefl`.";
      signature = "eqCongSucc : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, eq";
    };
    eqInjSucc = {
      description = "eqInjSucc: injectivity of `suc` — `eqInjSucc m n e : Eq Nat m n` given `e : Eq Nat (suc m) (suc n)`. bootJ at motive `λx _. Eq Nat m (predNat x)`; base case `Eq Nat m m` via β-reduction of `predNat (suc m)`.";
      signature = "eqInjSucc : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, eqSucc";
    };
    eqRefutSuccZero = {
      description = "eqRefutSuccZero: McBride no-confusion — `eqRefutSuccZero m e : void` refutes `e : Eq Nat (suc m) zero`. bootJ at motive `λx _. natCaseU void unit x`; base `tt` at unit, result `void` at zero.";
      signature = "eqRefutSuccZero : Hoas -> Hoas -> Hoas  -- m, eq";
    };
    eqRefutZeroSucc = {
      description = "eqRefutZeroSucc: symmetric McBride no-confusion — `eqRefutZeroSucc n e : void` refutes `e : Eq Nat zero (suc n)`. bootJ at motive `λx _. natCaseU unit void x`.";
      signature = "eqRefutZeroSucc : Hoas -> Hoas -> Hoas  -- n, eq";
    };
    iff = {
      description = "iff: propositional biconditional — `iff P Q := (P → Q) × (Q → P)` per HoTT Book §1.7. Built as `and (P→Q) (Q→P)`.";
      signature = "iff : Hoas -> Hoas -> Hoas";
    };
    intzDecode = {
      description = "intzDecode: sign-erasing payload extractor `intz -> Nat`. `intzPos n` and `intzNegSucc n` both yield `n`. Used as the bootJ motive discriminator in `intzPosInjective` / `intzNegSuccInjective`.";
      signature = "intzDecode : Hoas";
    };
    intzLe = {
      description = "intzLe: prelude `IntZ` ordering type-family — `intzLe m n : U(0)` follows Agda `Data.Integer.Base._≤_` four cases: pos-pos delegates to Nat `le`; pos-negSucc is `void` (positives never ≤ negatives); negSucc-pos is `unit` (negatives always ≤ positives); negSucc-negSucc flips arguments and delegates back to Nat `le` (negSucc is monotonically decreasing in its argument).";
      signature = "intzLe : Hoas -> Hoas -> Hoas  -- m, n";
    };
    intzLit = {
      description = "intzLit: Nix-meta bridge from a Nix integer to `IntZ` — `intzLit n` returns `intzPos (natLit n)` for `n >= 0` and `intzNegSucc (natLit (-n - 1))` for `n < 0`. Boundary cases: `intzLit 0 = intzPos 0`; `intzLit (-1) = intzNegSucc 0`.";
      signature = "intzLit : Int -> Hoas";
    };
    intzNegSuccCong = {
      description = "intzNegSuccCong: congruence of `intzNegSucc` — `intzNegSuccCong m n e : Eq IntZ (negSucc m) (negSucc n)` lifts `e : Eq Nat m n`.";
      signature = "intzNegSuccCong : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, natEq";
    };
    intzNegSuccInjective = {
      description = "intzNegSuccInjective: symmetric injectivity of `intzNegSucc` via the same `intzDecode` motive.";
      signature = "intzNegSuccInjective : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, intzEq";
    };
    intzPosCong = {
      description = "intzPosCong: congruence of `intzPos` — `intzPosCong m n e : Eq IntZ (pos m) (pos n)` lifts `e : Eq Nat m n`. bootJ at motive `λx _. Eq IntZ (pos m) (pos x)`; mirrors `eqCongSucc`.";
      signature = "intzPosCong : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, natEq";
    };
    intzPosInjective = {
      description = "intzPosInjective: injectivity of `intzPos` — `intzPosInjective m n e : Eq Nat m n` from `e : Eq IntZ (pos m) (pos n)`. bootJ at motive `λx _. Eq Nat m (intzDecode x)`; β on the decoder collapses base case to `Eq Nat m m`.";
      signature = "intzPosInjective : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, intzEq";
    };
    leInjSS = {
      description = "leInjSS: injectivity of `leSS` — `leInjSS m n pf : Le m n` given `pf : Le (suc m) (suc n)`. leElim at motive `λm' n' _. Le (predNat m') (predNat n')`; leZ fills via `leZ ∘ predNat`, leSS fills with the recursive witness directly (via β on `predNat (suc _)`).";
      signature = "leInjSS : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, leSuccSucc";
    };
    leRefutSuccZero = {
      description = "leRefutSuccZero: refutation of `Le (suc m) zero` — leElim at motive `λm' n' _. natCaseU unit (natCaseU void unit n') m'`; both leZ and leSS case targets collapse to `unit`, while the refutation target at (suc m, 0) collapses to `void`.";
      signature = "leRefutSuccZero : Hoas -> Hoas -> Hoas  -- m, leProof";
    };
    no = {
      description = "no: negative decidability witness — `no P r : dec P` for a refutation `r : not P`. Routes through `inr P (not P) r`.";
      signature = "no : Hoas -> Hoas -> Hoas  -- P, refutation";
    };
    not = {
      description = "not: propositional negation — `not P := P → ⊥` per HoTT Book §1.7. Elaborates to a pi with `void` codomain.";
      signature = "not : Hoas -> Hoas";
    };
    or_ = {
      description = "or_: propositional disjunction — `or_ P Q := P + Q` per HoTT Book §1.7. Trailing underscore avoids the Nix `or` keyword in identifier position (mirrors `true_` / `false_`).";
      signature = "or_ : Hoas -> Hoas -> Hoas";
    };
    predNat = {
      description = "predNat: saturating Nat predecessor — `predNat zero ≡ zero`, `predNat (suc m) ≡ m`. Built via `ind` with constant `nat` motive. Consumed by `eqInjSucc` and `leInjSS`.";
      signature = "predNat : Hoas  -- closed function nat -> nat";
    };
    refinementPred = {
      description = "refinementPred: Σ-encoded refinement-predicate carrier `refinementPred dom predFn = Σ (x : dom) (Dec (predFn x))`. McBride & McKinna 2004 'The view from the left'. `predFn` is a Nix-meta `Hoas -> Hoas` predicate following the surface convention of `sigma` / `forall` / `lam`. Inhabitants pair a value with a decision proof; the decision procedure is supplied at the value level rather than encoded in the type.";
      signature = "refinementPred : Hoas -> (Hoas -> Hoas) -> Hoas  -- domain, predFn";
    };
    signsDiffer = {
      description = "signsDiffer: no-confusion refutation `(m n : Nat) -> Eq IntZ (pos m) (negSucc n) -> void`. McBride 2000 PhD §3.5 discriminator-motive technique applied to the IntZ sign discriminator (`unit` on `pos`, `void` on `negSucc`) plus `bootJ` transport.";
      signature = "signsDiffer : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, e";
    };
    signsDifferRev = {
      description = "signsDifferRev: symmetric no-confusion refutation `(m n : Nat) -> Eq IntZ (negSucc m) (pos n) -> void`. Same discriminator-motive technique as `signsDiffer` with the `pos` / `negSucc` targets swapped.";
      signature = "signsDifferRev : Hoas -> Hoas -> Hoas -> Hoas  -- m, n, e";
    };
    yes = {
      description = "yes: positive decidability witness — `yes P p : dec P` for a proof `p : P`. Routes through `inl P (not P) p`.";
      signature = "yes : Hoas -> Hoas -> Hoas  -- P, proof";
    };
  };
}
