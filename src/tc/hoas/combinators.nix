# HOAS node constructors — kernel-primitive types, compound-type sugar,
# binding forms (pi/sigma/lam/let), intros, literals, annotation/app/projection,
# descriptions, and the eliminator wrappers that compile via desc-ind adapters.
#
# The macro-derived prelude types (`nat`, `listOf`, `sum`) and their
# constructors/introduction forms (`zero`, `succ`, `nil`, `cons`, `inl`, `inr`)
# live in `datatype.nix` because they reference `NatDT`/`ListDT`/`SumDT` from
# the macro layer. Cross-part references go through `self.<name>`.
{ self, ... }:

let
  # HOAS variable markers. A marker stands for a bound variable at a specific
  # binding depth (level); `elaborate` converts it to `T.mkVar` with the
  # correct de Bruijn index.
  _hoasTag = "__nix-effects-hoas-marker__";
in {
  scope = {
    mkMarker = level: { _hoas = _hoasTag; inherit level; };
    isMarker = x: builtins.isAttrs x && x ? _hoas && x._hoas == _hoasTag;

    # Kernel-primitive value types tying the type theory to the
    # underlying Nix value layer. `bool` / `unit` / `void` are
    # defined further down as derived μ-forms; the kernel-primitive
    # nodes for those types live under the internal `*Prim` aliases
    # (`boolPrim` / `unitPrim` / `voidPrim`).
    string = { _htag = "string"; };
    int_ = { _htag = "int"; };
    float_ = { _htag = "float"; };
    attrs = { _htag = "attrs"; };
    path = { _htag = "path"; };
    function_ = { _htag = "function"; };
    any = { _htag = "any"; };

    eq = type: lhs: rhs: { _htag = "eq"; inherit type lhs rhs; };
    u = level: { _htag = "U"; inherit level; };

    # Compound types (sugar for nested sigma/sum — carry structural info
    # for elaborateValue).
    # fields : [ { name; type; } ... ] — sorted by name
    record = fields: { _htag = "record"; inherit fields; };
    # maybe = Sum(inner, Unit) — null for Right/Unit, value for Left/inner.
    maybe = inner: { _htag = "maybe"; inherit inner; };
    # branches : [ { tag; type; } ... ] — sorted by tag
    variant = branches: { _htag = "variant"; inherit branches; };

    # Binding forms — take Nix lambda for the body.
    forall = name: domain: bodyFn:
      { _htag = "pi"; inherit name domain; body = bodyFn; };
    sigma = name: fst: sndFn:
      { _htag = "sigma"; inherit name fst; body = sndFn; };
    lam = name: domain: bodyFn:
      { _htag = "lam"; inherit name domain; body = bodyFn; };
    let_ = name: type: val: bodyFn:
      { _htag = "let"; inherit name type val; body = bodyFn; };

    # Intro forms and term combinators. `true_` / `false_` / `tt`
    # are derived μ-form constructors (see the Bool/Unit/Void block
    # below); the kernel-primitive nodes for them live under
    # `truePrim_` / `falsePrim_` / `ttPrim`.
    pair = fst: snd: { _htag = "pair"; inherit fst snd; };
    refl = { _htag = "refl"; };

    stringLit = s: { _htag = "string-lit"; value = s; };
    intLit = n: { _htag = "int-lit"; value = n; };
    floatLit = f: { _htag = "float-lit"; value = f; };
    attrsLit = { _htag = "attrs-lit"; };
    pathLit = { _htag = "path-lit"; };
    fnLit = { _htag = "fn-lit"; };
    anyLit = { _htag = "any-lit"; };

    strEq = lhs: rhs: { _htag = "str-eq"; inherit lhs rhs; };
    opaqueLam = nixFn: piHoas:
      { _htag = "opaque-lam"; _fnBox = { _fn = nixFn; }; inherit nixFn piHoas; };
    # Surface `absurd` routes through `absurdFin0`. After the Phase 9
    # rebind, the HOAS `void` is `app fin zero` (a derived `VMu (Fin 0
    # desc) zero`), not the kernel's `V.vVoid` primitive. The kernel's
    # `absurd` INFER rule at `check/infer.nix:125-129` checks its
    # witness against `V.vVoid`, so it no longer matches derived-void
    # witnesses. `absurdFin0` generalises: it takes a `Fin 0` witness
    # and discharges by no-confusion on `Eq Nat (succ m) zero`.
    # Internal sites that still produce `V.vVoid` witnesses (e.g.
    # `noConfSuccZero m emz`) use `absurdPrim` directly.
    absurd = type: term: self.absurdFin0 type term;
    ann = term: type: { _htag = "ann"; inherit term type; };
    app = fn: arg: { _htag = "app"; inherit fn arg; };
    fst_ = pair: { _htag = "fst"; inherit pair; };
    snd_ = pair: { _htag = "snd"; inherit pair; };

    # Eliminators. `ind`/`listElim`/`sumElim` wrap motive/base/step in
    # `let_`-bindings at their required types before the application spine,
    # making motive/step/base inferable (VAR via lookupType) and emitting a
    # `let_ P … let_ B … let_ S … <elim>` Tm shape. The user-facing
    # `boolElim` is derived in the Bool/Unit/Void block below; the
    # kernel-primitive `bool-elim` node stays reachable internally via
    # `boolElimPrim`.
    ind = motive: base: step: scrut:
      let
        inherit (self) forall app let_ nat zero succ u NatDT;
        piMotiveTy = forall "_" nat (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "B" (app P zero) base (B:
      let_ "S" (forall "k" nat (k:
                forall "_" (app P k) (_: app P (succ k)))) step (S:
        app (app (app (app NatDT.elim P) B) S) scrut)));

    # Stable alias for the kernel-primitive bool-elim node. Retained as
    # an internal-only alias pending Phase D kernel-primitive retirement
    # — no scaffolding now references it (prelude descriptions, the
    # datatype macro's spine/dispatch, and the derived `boolElim` all
    # dispatch via the plus-coproduct / `sumElimPrim` path).
    boolElimPrim = motive: onTrue: onFalse: scrut:
      { _htag = "bool-elim"; inherit motive onTrue onFalse scrut; };

    # Stable aliases for the kernel-primitive Bool/Unit/Void type and
    # intro nodes. Internal-only: description scaffolding and any other
    # module-internal site that must reference the kernel primitives
    # directly uses these aliases rather than the surface names `bool`,
    # `true_`, etc. (which are the derived μ-forms in the Bool/Unit/Void
    # block below). Not exported from the HOAS module.
    boolPrim   = { _htag = "bool"; };
    truePrim_  = { _htag = "true"; };
    falsePrim_ = { _htag = "false"; };
    unitPrim   = { _htag = "unit"; };
    ttPrim     = { _htag = "tt"; };
    voidPrim   = { _htag = "void"; };
    absurdPrim = type: term: { _htag = "absurd"; inherit type term; };

    # Kernel-primitive sum HOAS surface. The user-facing `sum`/`inl`/`inr`
    # at `datatype.nix` are description-derived `μ(sumDesc)` forms; these
    # primitive aliases route to the kernel's `VSum`/`VInl`/`VInr` directly,
    # as needed by `plus`'s interpretation (`interp (A ⊕ B) X i = Sum (⟦A⟧
    # X i) (⟦B⟧ X i)` uses kernel Sum for sum-elim dispatch in `descElim`
    # scaffolding). Internal-only.
    sumPrim = L: R: { _htag = "sum-prim"; inherit L R; };
    inlPrim = L: R: v: { _htag = "inl-prim"; inherit L R; term = v; };
    inrPrim = L: R: v: { _htag = "inr-prim"; inherit L R; term = v; };
    # Kernel-primitive sum-elim. Emitted only by `allHoas`'s `onPlus` so
    # that the stuck frame under a neutral scrutinee bottoms out in a
    # kernel `ESumElim` rather than re-entering the derived `SumDT.elim`
    # descInd (whose step itself contains `allHoas` — the two would
    # diverge during quote-under-binder on neutral descInd scrutinees).
    sumElimPrim = left: right: motive: onLeft: onRight: scrut:
      { _htag = "sum-elim-prim"; inherit left right motive onLeft onRight scrut; };

    listElim = A: motive: onNil: onCons: scrut:
      let
        inherit (self) forall app let_ listOf nil cons u ListDT;
        piMotiveTy = forall "_" (listOf A) (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "N" (app P (nil A)) onNil (N:
      let_ "C" (forall "h" A (hVar:
                forall "t" (listOf A) (tVar:
                forall "_" (app P tVar) (_:
                  app P (cons A hVar tVar))))) onCons (C:
        app (app (app (app (app ListDT.elim A) P) N) C) scrut)));

    sumElim = A: B: motive: onLeft: onRight: scrut:
      let
        inherit (self) forall app let_ sum inl inr u SumDT;
        piMotiveTy = forall "_" (sum A B) (_: u 0);
      in
      let_ "P" piMotiveTy motive (P:
      let_ "L" (forall "a" A (aVar: app P (inl A B aVar))) onLeft (L:
      let_ "R" (forall "b" B (bVar: app P (inr A B bVar))) onRight (R:
        app (app (app (app (app (app SumDT.elim A) B) P) L) R) scrut)));

    j = type: lhs: motive: base: rhs: eq_:
      { _htag = "j"; inherit type lhs motive base rhs; eq = eq_; };

    # Descriptions: types, constructors, and eliminators.
    #
    # `descI`, `retI`, `recI`, `piI`, `muI` build `Desc I` / `μ I D i`
    # directly. `desc`, `descRet`, `descRec`, `descPi`, `mu` are ⊤-slice
    # aliases: `desc = descI unitPrim`, `mu D i = muI unitPrim D i`, etc. —
    # type-level identities at the ⊤-slice. They pin the I slot to the
    # kernel-primitive unit via `unitPrim` (not the HOAS-surface `unit`,
    # which is itself a derived μ form).
    #
    # `descCon`, `descInd` match kernel arities exactly (3, 5): there is
    # no ⊤-slice alias. At I=⊤, call sites write `self.ttPrim` explicitly
    # at the index position.
    descI = I: { _htag = "desc"; inherit I; };
    desc = self.descI self.unitPrim;

    muI = I: D: i: { _htag = "mu"; inherit I D i; };
    mu = D: i: self.muI self.unitPrim D i;

    retI = j: { _htag = "desc-ret"; inherit j; };
    descRet = self.retI self.ttPrim;

    # descArg S (b: T b) — T is a Nix function, b binds a fresh variable.
    descArg = S: T: { _htag = "desc-arg"; inherit S; body = T; };

    recI = j: D: { _htag = "desc-rec"; inherit j D; };
    descRec = D: self.recI self.ttPrim D;

    piI = S: f: D: { _htag = "desc-pi"; inherit S f D; };
    # The kernel `desc-pi` infer rule recovers I from the codomain of
    # `tm.f`, so `f` must be inferable. A bare `lam` is checkable-only in
    # the bidirectional kernel; the ⊤-slice alias therefore ann-wraps the
    # constant index function against its explicit type `S → ⊤`, routing
    # synthesis through CHECK where bare canonical forms are accepted.
    descPi = S: D:
      self.piI S
        (self.ann (self.lam "_" S (_: self.ttPrim))
                  (self.forall "_" S (_: self.unitPrim)))
        D;

    descCon = D: i: d: { _htag = "desc-con"; inherit D i d; };

    descInd = D: motive: step: i: scrut:
      { _htag = "desc-ind"; inherit D motive step i scrut; };
    descElim = motive: onRet: onArg: onRec: onPi: onPlus: scrut:
      { _htag = "desc-elim"; inherit motive onRet onArg onRec onPi onPlus scrut; };

    # First-class binary coproduct of descriptions. `plusI A B : Desc I`
    # where A, B : Desc I share the same index type. Its `interp` reduces to
    # a sum of the summands' interpretations (`Sum (⟦A⟧ X i) (⟦B⟧ X i)`),
    # replacing the Bool-tag-dispatched `descArg bool (boolElim _ A B)`
    # encoding and eliminating the commuting-conv obligation on `interp ∘
    # bool-elim`. `plus` is the ⊤-slice alias; at any fixed I both are the
    # same kernel constructor since `plusI` infers I from A's inferred type.
    plusI = A: B: { _htag = "desc-plus"; inherit A B; };
    plus = A: B: self.plusI A B;

    # Nat-specific equality lemmas. Thin wrappers over `j` at type `Nat`;
    # consumed by `finElim` (J-transport on the ret-leaf `Eq Nat (succ m) n`)
    # and `absurdFin0` (no-confusion on `Eq Nat (succ m) zero`).
    symNat = a: b: e:
      self.j self.nat a
        (self.lam "x" self.nat (x: self.lam "_" (self.eq self.nat a x) (_:
          self.eq self.nat x a)))
        self.refl
        b e;

    transNat = a: b: c: eab: ebc:
      self.j self.nat b
        (self.lam "x" self.nat (x: self.lam "_" (self.eq self.nat b x) (_:
          self.eq self.nat a x)))
        eab
        c ebc;

    # `natDisc n` — discriminator with `natDisc zero ≡ ⊤` and `natDisc (succ _) ≡ ⊥`.
    # Used by `noConfSuccZero` below. Reified as an ann-wrapped HOAS lam so
    # `app natDisc x` is inferable in the bidirectional kernel (bare lam is
    # checkable-only; ann routes synthesis through the infer rule, matching
    # the `fin` / `descPi` precedent).
    #
    # The eliminator route is `descInd nat.D` directly, NOT through the HOAS
    # `ind` wrapper or `NatDT.elim`: both pin their motive codomain at `u 0`
    # via `piMotiveTy = forall _ nat (_: u 0)`, but `natDisc`'s motive body
    # is `u 0` itself — a type at `U(1)`, not `U(0)` — so neither pinned
    # wrapper accepts it. Kernel `desc-ind` accepts motives at any universe
    # level; descInd over `nat.D` with motive `(_i:Unit) → μ nat.D _i → U(0)`
    # is well-typed and produces a term whose value at `zero`/`succ _`
    # β-reduces to `unit`/`void`.
    #
    # The step dispatches on the plus summand via `sumElimPrim` on
    # `d : Sum (⟦descRet⟧ muFam iArg) (⟦descRec descRet⟧ muFam iArg)` —
    # the inl branch yields `unitPrim`, the inr branch yields `voidPrim`.
    # The IH is discarded — discrimination doesn't depend on recursion.
    natDisc =
      let
        inherit (self) ann lam forall app nat u unitPrim voidPrim
                        ttPrim mu descInd interpHoas allHoas
                        sumPrim sumElimPrim descRet descRec;
        D = nat.D;
        muFam = lam "_i" unitPrim (iArg: mu D iArg);
        motive = lam "_i" unitPrim (_: lam "_x" (mu D _) (_: u 0));
        lInterpAt = iArg_: interpHoas unitPrim descRet muFam iArg_;
        rInterpAt = iArg_: interpHoas unitPrim (descRec descRet) muFam iArg_;
        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoas unitPrim D muFam iArg) (d:
               lam "_ih" (allHoas unitPrim D D motive iArg d) (_:
                 let
                   lInterp = lInterpAt iArg;
                   rInterp = rInterpAt iArg;
                 in sumElimPrim lInterp rInterp
                      (lam "_s" (sumPrim lInterp rInterp) (_: u 0))
                      (lam "_" lInterp (_: unitPrim))
                      (lam "_" rInterp (_: voidPrim))
                      d)));
      in
      ann (lam "n" nat (n: descInd D motive step ttPrim n))
          (forall "_" nat (_: u 0));

    # noConfSuccZero : Π(m : Nat). Eq Nat (succ m) zero → Void
    # J-transports `tt : natDisc zero` along `sym e` to `_ : natDisc (succ m) ≡ ⊥`.
    noConfSuccZero = m: e:
      self.j self.nat self.zero
        (self.lam "x" self.nat (x: self.lam "_" (self.eq self.nat self.zero x) (_:
          self.app self.natDisc x)))
        self.ttPrim
        (self.succ m)
        (self.symNat (self.succ m) self.zero e);

    # Indexed description of the Fin family via the first-class `plus`
    # coproduct. Two summands sharing a `succ m` target-index pattern
    # with an explicit `Eq Nat (succ m) i` obligation at the ret-leaf.
    #   inl  → fzero m : Fin (succ m)    payload (m : Nat, refl)
    #   inr  → fsuc m k : Fin (succ m)   payload (m : Nat, k : Fin m, refl)
    # `interp (plus A B) X i` reduces STRUCTURALLY to kernel `Sum (⟦A⟧ X i)
    # (⟦B⟧ X i)`, eliminating the commuting-conv obligation on
    # `interp ∘ bool-elim` that the prior `descArg bool (b: …)` encoding
    # required. The `finDesc.T (fst d)` selector idiom and the
    # `finDescBody` sub-description lam are both retired.
    finDesc =
      let inherit (self) plus descArg retI recI nat succ; in
      plus (descArg nat (m: retI (succ m)))
           (descArg nat (m: recI m (retI (succ m))));

    # fin : Nat → U — the Fin family as a Hoas function term. Ann-wrapped
    # against its Π-type so `app fin <n>` is inferable in the bidirectional
    # kernel (bare `lam` is checkable-only, so `app`'s infer rule cannot
    # synthesise the codomain without the annotation).
    fin =
      let inherit (self) lam ann nat forall u muI finDesc; in
      ann (lam "n" nat (n: muI nat finDesc n))
          (forall "_" nat (_: u 0));

    # fzero : Π(m : Nat). Fin (succ m)
    # Payload at the inl summand: `pair m refl` — the summand's interp
    # at iArg = succ m is `Σ(m':Nat). Eq Nat (succ m') (succ m)`,
    # witnessed by `(m, refl)`. L/R are computed via `interpHoas` at
    # iArg = succ m.
    fzero = m:
      let
        inherit (self)
          descCon finDesc succ pair refl inlPrim
          interpHoas lam muI nat descArg retI recI;
        muFam = lam "i" nat (i: muI nat finDesc i);
        fzeroSum = descArg nat (m_: retI (succ m_));
        fsucSum  = descArg nat (m_: recI m_ (retI (succ m_)));
      in
      descCon finDesc (succ m)
        (inlPrim
          (interpHoas nat fzeroSum muFam (succ m))
          (interpHoas nat fsucSum  muFam (succ m))
          (pair m refl));

    # fsuc : Π(m : Nat)(k : Fin m). Fin (succ m)
    # Payload at the inr summand: `pair m (pair k refl)` — the summand's
    # interp at iArg = succ m is `Σ(m':Nat). Σ(_:μfin m'). Eq Nat
    # (succ m') (succ m)`, witnessed by `(m, k, refl)`.
    fsuc = m: k:
      let
        inherit (self)
          descCon finDesc succ pair refl inrPrim
          interpHoas lam muI nat descArg retI recI;
        muFam = lam "i" nat (i: muI nat finDesc i);
        fzeroSum = descArg nat (m_: retI (succ m_));
        fsucSum  = descArg nat (m_: recI m_ (retI (succ m_)));
      in
      descCon finDesc (succ m)
        (inrPrim
          (interpHoas nat fzeroSum muFam (succ m))
          (interpHoas nat fsucSum  muFam (succ m))
          (pair m (pair k refl)));

    # finElim : (P : (n : Nat) → Fin n → U)
    #         → (Π(m : Nat). P (succ m) (fzero m))
    #         → (Π(m : Nat)(k : Fin m). P m k → P (succ m) (fsuc m k))
    #         → (n : Nat) → (k : Fin n) → P n k
    #
    # Built as `descInd finDesc P step`; step dispatches on the plus
    # summand via `sumElimPrim` on `d : Sum (⟦fzeroSum⟧ muFam nArg)
    # (⟦fsucSum⟧ muFam nArg)` and J-transports each user-supplied case
    # across the ret-leaf equality witness `em : Eq (succ m) nArg`,
    # aligning the constructor's base index `succ m` with the result
    # index nArg. Per-summand interps are parametric in iArg, so the J
    # motive rebuilds them at each J-bound index.
    finElim = P: Pz: Ps:
      let
        inherit (self)
          lam forall app fst_ snd_ pair
          nat succ
          eq j
          muI descCon descInd interpHoas allHoas
          sumPrim sumElimPrim inlPrim inrPrim
          descArg retI recI
          finDesc;

        muFam = lam "i" nat (i: muI nat finDesc i);

        fzeroSum = descArg nat (m_: retI (succ m_));
        fsucSum  = descArg nat (m_: recI m_ (retI (succ m_)));
        lInterpAt = iArg_: interpHoas nat fzeroSum muFam iArg_;
        rInterpAt = iArg_: interpHoas nat fsucSum  muFam iArg_;

        step = lam "n" nat (nArg:
               lam "d" (interpHoas nat finDesc muFam nArg) (d:
               lam "ih" (allHoas nat finDesc finDesc P nArg d) (ih:
                 let
                   lInterp = lInterpAt nArg;
                   rInterp = rInterpAt nArg;

                   sumMot = lam "s" (sumPrim lInterp rInterp) (s:
                     app (app P nArg) (descCon finDesc nArg s));

                   onInl = lam "r" lInterp (r:
                     let
                       m  = fst_ r;
                       em = snd_ r;
                       jMot = lam "np" nat (np:
                              lam "e" (eq nat (succ m) np) (e:
                                app (app P np)
                                    (descCon finDesc np
                                      (inlPrim (lInterpAt np) (rInterpAt np)
                                        (pair m e)))));
                     in j nat (succ m) jMot (app Pz m) nArg em);

                   onInr = lam "r" rInterp (r:
                     let
                       m   = fst_ r;
                       kk  = fst_ (snd_ r);
                       em  = snd_ (snd_ r);
                       ihk = fst_ ih;
                       jMot = lam "np" nat (np:
                              lam "e" (eq nat (succ m) np) (e:
                                app (app P np)
                                    (descCon finDesc np
                                      (inrPrim (lInterpAt np) (rInterpAt np)
                                        (pair m (pair kk e))))));
                     in j nat (succ m) jMot
                          (app (app (app Ps m) kk) ihk) nArg em);
                 in sumElimPrim lInterp rInterp sumMot onInl onInr d)));
      in n: k: descInd finDesc P step n k;

    # absurdFin0 : (P : U) → Fin 0 → P
    # Fin 0 is vacuous: both constructor payloads carry an `em : Eq (succ m) n`
    # leaf, and at n = 0 combining with the outer `e0 : Eq n zero` gives
    # `Eq (succ m) zero`, which `noConfSuccZero` refutes.
    #
    # Dispatches via `sumElimPrim` on the plus-summand payload. Each
    # summand's ret-leaf carries `em : Eq (succ m) nArg`; J-transport
    # and `transNat` compose it with `e0` to yield `Eq (succ m) zero`,
    # which `noConfSuccZero` refutes.
    absurdFin0 = P: x:
      let
        inherit (self)
          lam forall app fst_ snd_
          nat zero succ absurdPrim
          eq refl
          muI descCon descInd interpHoas allHoas
          sumPrim sumElimPrim inlPrim inrPrim
          descArg retI recI
          finDesc transNat noConfSuccZero;

        muFam = lam "i" nat (i: muI nat finDesc i);

        fzeroSum = descArg nat (m_: retI (succ m_));
        fsucSum  = descArg nat (m_: recI m_ (retI (succ m_)));
        lInterpAt = iArg_: interpHoas nat fzeroSum muFam iArg_;
        rInterpAt = iArg_: interpHoas nat fsucSum  muFam iArg_;

        Q = lam "i" nat (iArg: lam "_" (muI nat finDesc iArg) (_:
              forall "_" (eq nat iArg zero) (_: P)));

        step = lam "n" nat (nArg:
               lam "d" (interpHoas nat finDesc muFam nArg) (d:
               lam "_ih" (allHoas nat finDesc finDesc Q nArg d) (_:
                 lam "e0" (eq nat nArg zero) (e0:
                   let
                     lInterp = lInterpAt nArg;
                     rInterp = rInterpAt nArg;
                     sumMot = lam "_s" (sumPrim lInterp rInterp) (_: P);
                     onInl = lam "r" lInterp (r:
                       let m = fst_ r;
                           em = snd_ r;
                           emz = transNat (succ m) nArg zero em e0;
                       in absurdPrim P (noConfSuccZero m emz));
                     onInr = lam "r" rInterp (r:
                       let m = fst_ r;
                           em = snd_ (snd_ r);
                           emz = transNat (succ m) nArg zero em e0;
                       in absurdPrim P (noConfSuccZero m emz));
                   in sumElimPrim lInterp rInterp sumMot onInl onInr d))));
      in app (descInd finDesc Q step zero x) refl;

    # natCaseU A B : Nat → U — `natCaseU A B zero ≡ A`;
    # `natCaseU A B (succ _) ≡ B`. Generalises `natDisc` to arbitrary
    # U-valued zero and succ cases; same `descInd nat.D` +
    # `sumElimPrim`-on-`d` template, with the two branches parameterised.
    # Used by `vhead` to dispatch the vecElim motive across the
    # vnil/vcons cases (`natCaseU unit A`: vnil target is `unit`,
    # inhabited by `tt`; vcons target is `A`, inhabited by the head
    # element). The IH is discarded — discrimination doesn't depend on
    # recursion.
    natCaseU = A: B:
      let
        inherit (self) ann lam forall app nat u unitPrim
                        ttPrim mu descInd interpHoas allHoas
                        sumPrim sumElimPrim descRet descRec;
        D = nat.D;
        muFam = lam "_i" unitPrim (iArg: mu D iArg);
        motive = lam "_i" unitPrim (_: lam "_x" (mu D _) (_: u 0));
        lInterpAt = iArg_: interpHoas unitPrim descRet muFam iArg_;
        rInterpAt = iArg_: interpHoas unitPrim (descRec descRet) muFam iArg_;
        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoas unitPrim D muFam iArg) (d:
               lam "_ih" (allHoas unitPrim D D motive iArg d) (_:
                 let
                   lInterp = lInterpAt iArg;
                   rInterp = rInterpAt iArg;
                 in sumElimPrim lInterp rInterp
                      (lam "_s" (sumPrim lInterp rInterp) (_: u 0))
                      (lam "_" lInterp (_: A))
                      (lam "_" rInterp (_: B))
                      d)));
      in
      ann (lam "n" nat (n: descInd D motive step ttPrim n))
          (forall "_" nat (_: u 0));

    # Indexed description of the Vec family: `Vec A : Nat → U`.
    # Via the first-class `plus` coproduct, two summands:
    #   inl  → vnil  : Vec A 0                    (retI zero — no data)
    #   inr  → vcons : Π(m:Nat). A → Vec A m → Vec A (succ m)
    # `interp (plus A B) X i` reduces structurally to `Sum (⟦A⟧ X i)
    # (⟦B⟧ X i)` — no bool-tag dispatch, no commuting-conv obligation,
    # and no `vecDescBody` selector lam.
    vecDesc = A:
      let inherit (self) plus descArg retI recI nat zero succ; in
      plus (retI zero)
           (descArg nat (m: descArg A (_: recI m (retI (succ m)))));

    # vec : (A : U) → Nat → U — the Vec family as a Nix-level function on
    # A producing an ann-wrapped HOAS lam on n, so `app (vec A) n` is
    # inferable in the bidirectional kernel. Matches the `fin` precedent.
    vec = A:
      let inherit (self) lam ann nat forall u muI vecDesc; in
      ann (lam "n" nat (n: muI nat (vecDesc A) n))
          (forall "_" nat (_: u 0));

    # vnil : (A : U) → Vec A zero.
    # Payload at the inl summand: just `refl`, witnessing
    # `Eq Nat zero zero` at the ret-leaf.
    vnil = A:
      let
        inherit (self)
          descCon vecDesc zero refl inlPrim
          interpHoas lam muI nat descArg retI recI succ;
        vD = vecDesc A;
        muFam = lam "i" nat (i: muI nat vD i);
        vnilSum  = retI zero;
        vconsSum = descArg nat (m: descArg A (_: recI m (retI (succ m))));
      in
      descCon vD zero
        (inlPrim
          (interpHoas nat vnilSum  muFam zero)
          (interpHoas nat vconsSum muFam zero)
          refl);

    # vcons : (A : U)(m : Nat)(x : A)(xs : Vec A m) → Vec A (succ m).
    # Payload at the inr summand: `(m, x, xs, refl)` — matches the
    # `descArg nat (m. descArg A (_. recI m (retI (succ m))))` spine's
    # interp Σ(m:Nat). Σ(x:A). Σ(xs:μ vec A m). Eq Nat (succ m) (succ m).
    vcons = A: m: x: xs:
      let
        inherit (self)
          descCon vecDesc succ pair refl inrPrim
          interpHoas lam muI nat descArg retI recI zero;
        vD = vecDesc A;
        muFam = lam "i" nat (i: muI nat vD i);
        vnilSum  = retI zero;
        vconsSum = descArg nat (m_: descArg A (_: recI m_ (retI (succ m_))));
      in
      descCon vD (succ m)
        (inrPrim
          (interpHoas nat vnilSum  muFam (succ m))
          (interpHoas nat vconsSum muFam (succ m))
          (pair m (pair x (pair xs refl))));

    # vecElim : (A : U)
    #         → (P : (n : Nat) → Vec A n → U)
    #         → P zero (vnil A)
    #         → ((m:Nat)(x:A)(xs:Vec A m) → P m xs → P (succ m) (vcons A m x xs))
    #         → (n : Nat) → (xs : Vec A n) → P n xs
    #
    # Built as `descInd (vecDesc A) P step`; step dispatches on the plus
    # summand via `sumElimPrim` and J-transports each branch's
    # user-supplied case across the ret-leaf equality witness, aligning
    # the constructor's base index (zero / succ m) with the result index
    # nArg. Identical shape to `finElim` modulo the vcons payload
    # carrying an extra A-field (x) alongside the recursive Vec A m
    # field (xs).
    vecElim = A: P: Pn: Pc:
      let
        inherit (self)
          lam forall app fst_ snd_ pair
          nat zero succ
          eq j
          muI descCon descInd interpHoas allHoas
          sumPrim sumElimPrim inlPrim inrPrim
          descArg retI recI
          vecDesc;

        vD  = vecDesc A;
        muFam = lam "i" nat (i: muI nat vD i);

        vnilSum  = retI zero;
        vconsSum = descArg nat (m_: descArg A (_: recI m_ (retI (succ m_))));
        lInterpAt = iArg_: interpHoas nat vnilSum  muFam iArg_;
        rInterpAt = iArg_: interpHoas nat vconsSum muFam iArg_;

        step = lam "n" nat (nArg:
               lam "d" (interpHoas nat vD muFam nArg) (d:
               lam "ih" (allHoas nat vD vD P nArg d) (ih:
                 let
                   lInterp = lInterpAt nArg;
                   rInterp = rInterpAt nArg;

                   sumMot = lam "s" (sumPrim lInterp rInterp) (s:
                     app (app P nArg) (descCon vD nArg s));

                   # onInl: vnil branch. r : Eq Nat zero nArg
                   # (retI zero has no payload data, only the equality).
                   # J-transport Pn : P zero (vnil A) along r to P nArg (…).
                   onInl = lam "r" lInterp (r:
                     let
                       em = r;
                       jMot = lam "np" nat (np:
                              lam "e" (eq nat zero np) (e:
                                app (app P np)
                                    (descCon vD np
                                      (inlPrim (lInterpAt np) (rInterpAt np) e))));
                     in j nat zero jMot Pn nArg em);

                   # onInr: vcons branch.
                   # r : Σ(m:Nat). Σ(x:A). Σ(xs:Vec A m). Eq Nat (succ m) nArg.
                   # ih's first Σ-component is P m xs (the recursive
                   # vecElim result at index m on the tail).
                   onInr = lam "r" rInterp (r:
                     let
                       m    = fst_ r;
                       x    = fst_ (snd_ r);
                       xs   = fst_ (snd_ (snd_ r));
                       em   = snd_ (snd_ (snd_ r));
                       ihxs = fst_ ih;
                       jMot = lam "np" nat (np:
                              lam "e" (eq nat (succ m) np) (e:
                                app (app P np)
                                    (descCon vD np
                                      (inrPrim (lInterpAt np) (rInterpAt np)
                                        (pair m (pair x (pair xs e)))))));
                     in j nat (succ m) jMot
                          (app (app (app (app Pc m) x) xs) ihxs) nArg em);
                 in sumElimPrim lInterp rInterp sumMot onInl onInr d)));
      in n: xs: descInd vD P step n xs;

    # natPredCase A : Nat → U —
    #   `natPredCase A zero ≡ unit`,
    #   `natPredCase A (succ m) ≡ vec A m`.
    # Case-split on Nat whose succ-case return type depends on the
    # predecessor (extracted as `fst_ r` from the plus summand's
    # payload via `sumElimPrim` dispatch). Used by `vtail` to build the
    # vecElim motive `P n xs = natPredCase A n` so the vnil branch
    # targets `unit` (filled by `tt`) and the vcons branch targets
    # `vec A m` (filled by the tail). Generalises the
    # `natCaseU`/`natDisc` pattern to payload-dependent succ cases.
    natPredCase = A:
      let
        inherit (self) ann lam forall app nat u unitPrim
                        fst_ ttPrim mu descInd interpHoas allHoas
                        sumPrim sumElimPrim descRet descRec vec;
        D = nat.D;
        muFam = lam "_i" unitPrim (iArg: mu D iArg);
        motive = lam "_i" unitPrim (_: lam "_x" (mu D _) (_: u 0));
        vA = vec A;
        lInterpAt = iArg_: interpHoas unitPrim descRet muFam iArg_;
        rInterpAt = iArg_: interpHoas unitPrim (descRec descRet) muFam iArg_;
        step = lam "_i" unitPrim (iArg:
               lam "d" (interpHoas unitPrim D muFam iArg) (d:
               lam "_ih" (allHoas unitPrim D D motive iArg d) (_:
                 let
                   lInterp = lInterpAt iArg;
                   rInterp = rInterpAt iArg;
                 in sumElimPrim lInterp rInterp
                      (lam "_s" (sumPrim lInterp rInterp) (_: u 0))
                      # zero case — target is `unit`.
                      (lam "_r" lInterp (_: unitPrim))
                      # succ case — r : Σ(pred:μnat tt) (_: Eq ⊤ tt iArg);
                      # target is `vec A pred`.
                      (lam "r" rInterp (r: app vA (fst_ r)))
                      d)));
      in
      ann (lam "n" nat (n: descInd D motive step ttPrim n))
          (forall "_" nat (_: u 0));

    # vtail : (A : U) → (n : Nat) → Vec A (succ n) → Vec A n.
    # Symmetric to `vhead`: uses vecElim with motive `P n xs = natPredCase A n`.
    # At the vnil case the target is `unit` (filled by `tt`, which conv-
    # reduces from `natPredCase A zero`); at the vcons case the target
    # is `vec A m` (conv-reducing from `natPredCase A (succ m)`),
    # inhabited by returning the tail `xs`.
    vtail = A:
      let
        inherit (self) lam app nat succ ttPrim vec vecElim natPredCase;
        vA  = vec A;
        P   = lam "n" nat (n: lam "_xs" (app vA n) (_:
                app (natPredCase A) n));
        Pn  = ttPrim;
        Pc  = lam "m" nat (mVar: lam "_x" A (_: lam "xs" (app vA mVar) (xsVar:
                lam "_ih" (app (natPredCase A) mVar) (_: xsVar))));
      in lam "n" nat (n: lam "xs" (app vA (succ n)) (xs:
           vecElim A P Pn Pc (succ n) xs));

    # vhead : (A : U) → (n : Nat) → Vec A (succ n) → A.
    # The motive `P n xs = natCaseU unit A n` dispatches on n: at the
    # vnil case (n=zero) the target is `unit` (filled by `tt`, which
    # conv-reduces from `natCaseU unit A zero`); at the vcons case
    # (n=succ m) the target is `A` (conv-reducing from
    # `natCaseU unit A (succ m)`), inhabited by returning the head
    # element x. The IH is unused.
    vhead = A:
      let
        inherit (self) lam app nat succ ttPrim unitPrim vec vecElim natCaseU;
        vA  = vec A;
        P   = lam "n" nat (n: lam "_xs" (app vA n) (_:
                app (natCaseU unitPrim A) n));
        Pn  = ttPrim;
        Pc  = lam "m" nat (mVar: lam "x" A (xVar: lam "_xs" (app vA mVar) (_:
                lam "_ih" (app (natCaseU unitPrim A) mVar) (_: xVar))));
      in lam "n" nat (n: lam "xs" (app vA (succ n)) (xs:
           vecElim A P Pn Pc (succ n) xs));

    # Eq-as-description. The kernel retains `Eq` as a primitive
    # (indexed descriptions need it at the ret-leaf's index-equality
    # obligation), but with indexed descriptions in place the same
    # propositional equality is expressible as an inductive family:
    # a single-constructor retI-only description whose inhabitants
    # are exactly the retI leaf's equality witnesses.
    #
    #   eqDesc A a : Desc A         — retI a
    #   eqDT   A a b : U            — μ A (eqDesc A a) b
    #   reflDT A a : eqDT A a a     — descCon (eqDesc A a) a refl
    #
    # The iso with the kernel primitive Eq is witnessed in user-space:
    # `eqToEqDT` via J transporting reflDT along the equality, and
    # `eqDTToEq` via descInd extracting the retI leaf's witness
    # directly (no bool-dispatch — the description has a single
    # constructor). `eqIsoFwd` / `eqIsoBwd` are the iso proofs: each
    # is an equality between the roundtrip and the identity,
    # discharged by J / descInd reducing both sides to the same
    # canonical form at the refl / descCon cases.
    eqDesc = A: a: self.retI a;

    eqDT = A: a: b: self.muI A (self.eqDesc A a) b;

    reflDT = A: a:
      self.descCon (self.eqDesc A a) a self.refl;

    eqToEqDT = A: a: b: e:
      let
        inherit (self) lam eq muI eqDesc reflDT j;
        motive = lam "b'" A (b': lam "_e" (eq A a b') (_:
                   muI A (eqDesc A a) b'));
      in j A a motive (reflDT A a) b e;

    # `eqDTToEq` routes through descInd with the motive
    # `Q i x = Eq A a i`; at the sole retI constructor the step's
    # payload `d : Eq A a i` IS the witness, so the step body
    # returns `d` directly. The IH is vacuous (`all` over a retI
    # description is `unit`).
    eqDTToEq = A: a: b: x:
      let
        inherit (self) lam eq muI descInd unitPrim eqDesc;
        eD = eqDesc A a;
        Q = lam "i" A (iArg: lam "_x" (muI A eD iArg) (_:
              eq A a iArg));
        step = lam "i" A (iArg:
               lam "d" (eq A a iArg) (d:
               lam "_ih" unitPrim (_: d)));
      in descInd eD Q step b x;

    # eqIsoFwd : Π(e : Eq A a b). Eq (Eq A a b) (eqDTToEq (eqToEqDT e)) e.
    # J on e with motive `λb' e'. Eq (Eq A a b') (eqDTToEq (eqToEqDT e')) e'`:
    # at e'=refl, both roundtrips β-reduce — eqToEqDT fires J's refl
    # case to reflDT = descCon eD a refl, then eqDTToEq fires descInd's
    # descCon case to refl — so the base-case goal reduces to
    # `Eq (Eq A a a) refl refl`, witnessed by refl.
    eqIsoFwd = A: a: b:
      let
        inherit (self) lam forall eq j refl eqToEqDT eqDTToEq;
        motive = lam "b'" A (b': lam "e'" (eq A a b') (e':
                   eq (eq A a b')
                      (eqDTToEq A a b' (eqToEqDT A a b' e'))
                      e'));
      in lam "e" (eq A a b) (e:
           j A a motive refl b e);

    # eqIsoBwd : Π(x : eqDT A a b). Eq (eqDT A a b) (eqToEqDT (eqDTToEq x)) x.
    # descInd on x with motive
    # `Q i x' = Eq (μ A eD i) (eqToEqDT (eqDTToEq x')) x'`. At the sole
    # descCon case, eqDTToEq reduces to the payload `d : Eq A a i`, so
    # the step's goal becomes `Eq (μ A eD i) (eqToEqDT d) (descCon eD i d)`;
    # J on d then transports the base case `d = refl` — where eqToEqDT
    # refl ≡ reflDT = descCon eD a refl — to the general i.
    eqIsoBwd = A: a: b:
      let
        inherit (self) lam forall eq j refl muI unitPrim
                       descCon descInd eqDesc eqToEqDT eqDTToEq;
        eD = eqDesc A a;
        Q = lam "i" A (iArg: lam "x'" (muI A eD iArg) (x':
              eq (muI A eD iArg)
                 (eqToEqDT A a iArg (eqDTToEq A a iArg x'))
                 x'));
        jMot = lam "b'" A (b': lam "d'" (eq A a b') (d':
                 eq (muI A eD b')
                    (eqToEqDT A a b' d')
                    (descCon eD b' d')));
        step = lam "i" A (iArg:
               lam "d" (eq A a iArg) (d:
               lam "_ih" unitPrim (_:
                 j A a jMot refl iArg d)));
      in lam "x" (muI A eD b) (x: descInd eD Q step b x);

    # Bool as a derived μ-form over a plus-based coproduct description.
    # `boolDesc = plus (retI ttPrim) (retI ttPrim) : Desc ⊤` — each summand
    # is a non-recursive `retI ttPrim` leaf whose interpretation is the
    # leaf-equality type `Eq ⊤ ttPrim iArg`. The plus interpretation
    # reduces structurally to kernel `Sum`, so `interp boolDesc X iArg =
    # Sum (Eq ⊤ ttPrim iArg) (Eq ⊤ ttPrim iArg)` — no bool-tag dispatch,
    # no commuting-conv obligation on `interp ∘ bool-elim`, no routing
    # through a dispatched sub-description selector.
    #
    # `true_` / `false_` pack `inlPrim` / `inrPrim` at the `Sum`
    # interpretation, with `refl` discharging the leaf-equality at the
    # canonical index `ttPrim`. `bool = muI ⊤ boolDesc ttPrim` — bare
    # μ-form whose inferability is carried by the kernel `mu`
    # type-formation rule routing D through the desc-* CHECK rules at
    # `check/check.nix:205-250`.
    #
    # `boolElim` follows the `finElim` template: `descInd` over
    # `boolDesc`, step body dispatching via `sumElimPrim` on
    # `d : Sum (Eq ⊤ ttPrim iArg) (Eq ⊤ ttPrim iArg)` (no longer on a
    # `boolPrim` tag), J-transporting each user-supplied branch across
    # the leaf-equality witness. The J-base is `refl` at `iArg = ttPrim`
    # and the motive never identifies distinct proofs, so J usage
    # requires no UIP. `sumElimPrim` is the kernel-primitive sum-elim
    # alias (mirrors `sumPrim` / `inlPrim` / `inrPrim`); routing through
    # it avoids the self-embedding divergence the derived `self.sumElim`
    # would trigger when `allHoas.onPlus` quotes stuck descInd scrutinees
    # under a binder.
    boolDesc =
      let inherit (self) ann plus retI ttPrim desc; in
      ann (plus (retI ttPrim) (retI ttPrim)) desc;

    bool =
      let inherit (self) muI unitPrim ttPrim boolDesc; in
      muI unitPrim boolDesc ttPrim;

    true_ =
      let
        inherit (self) descCon boolDesc ttPrim inlPrim eq unitPrim refl;
        leafTy = eq unitPrim ttPrim ttPrim;
      in
      descCon boolDesc ttPrim (inlPrim leafTy leafTy refl);

    false_ =
      let
        inherit (self) descCon boolDesc ttPrim inrPrim eq unitPrim refl;
        leafTy = eq unitPrim ttPrim ttPrim;
      in
      descCon boolDesc ttPrim (inrPrim leafTy leafTy refl);

    # boolElim : (k : Level) → (Q : bool → U(k)) → Q true_ → Q false_ → (b : bool) → Q b
    #
    # `k` is a Nix-meta level parameter. `piMotiveTy = forall "_" bool
    # (_: u k)` is the Π-type used to `let_`-bind the user's `Q`.
    # Materialising `Q` as a VAR routes every downstream `app Qv …`
    # through the var rule at `infer.nix:37-38` rather than hitting the
    # lam cascade (lambdas are checkable-only in the bidirectional
    # kernel, so a bare `app Q …` in an inference position fails with
    # `cannot infer type`). `onT` / `onF` flow directly to `j`'s base
    # argument.
    #
    # Built as `descInd boolDesc motive step ttPrim b`. The descInd
    # motive lifts `Qv : bool → U(k)` to
    # `(i : unitPrim) → μ boolDesc i → U(k)` by unit-η on `i` (at
    # `iArg` conv `ttPrim`, `muI unitPrim boolDesc iArg` conv `bool`,
    # so the inner `app Qv xArg` type-checks). The step receives
    # `d : Sum (Eq ⊤ ttPrim iArg) (Eq ⊤ ttPrim iArg)` directly from
    # the plus interpretation and dispatches via `sumElimPrim` —
    # `inl e` routes to `onT` J-transported across `e`, `inr e` to
    # `onF`. The J motive in each branch rebuilds the target
    # `descCon boolDesc y (inlPrim/inrPrim … e')` shape so that at the
    # canonical J-base (`y = ttPrim`, `e' = refl`) it collapses to
    # `Q true_` / `Q false_`.
    #
    # The IH `_ih` is discarded — both summands are non-recursive
    # `retI ttPrim` leaves, so the recursive hypothesis carries no
    # information.
    boolElim = k: Q: onT: onF: b:
      let
        inherit (self)
          lam forall app let_ u
          unitPrim ttPrim
          eq j
          sumPrim sumElimPrim inlPrim inrPrim
          muI descCon descInd interpHoas allHoas
          bool boolDesc;

        piMotiveTy = forall "_" bool (_: u k);
      in
      let_ "Q" piMotiveTy Q (Qv:
        let
          boolMuFam = lam "_i" unitPrim (iVar: muI unitPrim boolDesc iVar);

          motive = lam "_i" unitPrim (_: lam "x" bool (xArg: app Qv xArg));

          # Leaf-equality type at a given index. `interp (retI ttPrim) X i`
          # = `Eq ⊤ ttPrim i`, and both summands of `boolDesc` are
          # `retI ttPrim`, so this is both L and R of the Sum.
          leafTy = i_: eq unitPrim ttPrim i_;

          step = lam "_i" unitPrim (iArg:
                 lam "d" (interpHoas unitPrim boolDesc boolMuFam iArg) (d:
                 lam "_ih" (allHoas unitPrim boolDesc boolDesc motive iArg d) (_:
                   let
                     # Sum-elim motive: Q (descCon boolDesc iArg s) for
                     # each Sum inhabitant s. At s = inl/inr e, reduces
                     # to the J-motive's target at that e.
                     sumMot = lam "s" (sumPrim (leafTy iArg) (leafTy iArg)) (s:
                       app Qv (descCon boolDesc iArg s));

                     onInl = lam "e" (leafTy iArg) (e:
                       let
                         jMot = lam "y" unitPrim (y:
                                lam "e'" (eq unitPrim ttPrim y) (e':
                                  app Qv (descCon boolDesc y
                                    (inlPrim (leafTy y) (leafTy y) e'))));
                       in j unitPrim ttPrim jMot onT iArg e);

                     onInr = lam "e" (leafTy iArg) (e:
                       let
                         jMot = lam "y" unitPrim (y:
                                lam "e'" (eq unitPrim ttPrim y) (e':
                                  app Qv (descCon boolDesc y
                                    (inrPrim (leafTy y) (leafTy y) e'))));
                       in j unitPrim ttPrim jMot onF iArg e);
                   in sumElimPrim (leafTy iArg) (leafTy iArg)
                                  sumMot onInl onInr d)));
        in descInd boolDesc motive step ttPrim b);

    # `unit` and `tt` are the kernel bootstrap singleton — Unit is the
    # terminal object of the ambient theory, and the `VTt`/`VNe` unit-η
    # rule at `conv.nix:85-90` gives it a unique-inhabitant-up-to-conv
    # semantics. Retiring Unit would require a meta-level fixpoint
    # mechanism making `Unit = µ Unit unitDesc tt` expressible as a
    # finite Tm; no current phase schedules such a mechanism, so Unit
    # stays primitive, matching CDFM 2010 "Gentle Art of Levitation" §5
    # and every other levitated theory in the literature. The internal
    # `unitPrim` / `ttPrim` aliases above are retained because 142
    # internal references (⊤-slice aliases, description scaffolding)
    # depend on them; the surface names resolve to the same kernel Tm.
    unit = self.unitPrim;
    tt = self.ttPrim;

    # `void` reuses the `Fin 0` vacuous family. `absurdFin0` at
    # `combinators.nix` (Fin prelude above) serves as the void
    # eliminator; no separate `voidElim` is introduced. Bare μ-form:
    # `fin` reduces to a descArg-based `μ (Fin 0 desc) zero`, whose
    # inferability is carried by the kernel's `mu` rule routing
    # through desc-* CHECK rules.
    void =
      let inherit (self) app fin zero; in
      app fin zero;
  };
  tests = {};
}
