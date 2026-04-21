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
    # underlying Nix value layer. `bool` / `void` are defined further
    # down as derived μ-forms (via plus-coproduct and Fin 0); `unit`
    # remains a kernel primitive whose alias `unitPrim` pins the
    # ⊤-slice I parameter throughout the description machinery.
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

    # Intro forms and term combinators. `true_` / `false_` are derived
    # μ-form constructors (see the Bool/Unit/Void block below);
    # `tt` / `ttPrim` are two names for the kernel-primitive Unit intro.
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
    # Surface `absurd` routes through `absurdFin0`: the HOAS `void` is
    # `app fin zero` (a derived `μ (Fin 0 desc) zero`), and `absurdFin0`
    # discharges a witness of `Fin 0` by no-confusion on `Eq Nat (succ
    # m) zero` via a direct J-transport at motive `natCaseU P Unit`.
    absurd = type: term: self.absurdFin0 type term;
    ann = term: type: { _htag = "ann"; inherit term type; };
    app = fn: arg: { _htag = "app"; inherit fn arg; };
    fst_ = pair: { _htag = "fst"; inherit pair; };
    snd_ = pair: { _htag = "snd"; inherit pair; };

    # Eliminators. `ind`/`listElim`/`sumElim` wrap motive/base/step in
    # `let_`-bindings at their required types before the application spine,
    # making motive/step/base inferable (VAR via lookupType) and emitting a
    # `let_ P … let_ B … let_ S … <elim>` Tm shape. The user-facing
    # `boolElim` is derived in the Bool/Unit/Void block below via
    # `descInd` on the plus-coproduct `boolDesc`.
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

    # Stable aliases for the kernel-primitive Unit type and its intro.
    # Unit is the bootstrap singleton of the description machinery —
    # ⊤-slice I parameter, retI leaves, and various scaffolding sites
    # reference `unitPrim`/`ttPrim` directly. Bool/Void/Absurd are
    # derived further down: `bool = μ ⊤ boolDesc tt` with `boolDesc =
    # plus (retI tt) (retI tt)`, `void = app fin zero`, `absurd =
    # absurdFin0`.
    unitPrim   = { _htag = "unit"; };
    ttPrim     = { _htag = "tt"; };

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

    # Nat-specific equality lemma. Thin wrapper over `j` at type `Nat`;
    # consumed by `absurdFin0` to compose the ret-leaf `em : Eq Nat (succ
    # m) nArg` with `e0 : Eq Nat nArg zero` into `emz : Eq Nat (succ m)
    # zero`.
    transNat = a: b: c: eab: ebc:
      self.j self.nat b
        (self.lam "x" self.nat (x: self.lam "_" (self.eq self.nat b x) (_:
          self.eq self.nat a x)))
        eab
        c ebc;

    # Fin prelude forwarders onto `FinDT` (defined in
    # `hoas/datatype.nix` via `datatypeI "Fin" nat […]`). The
    # description, type family, constructors, and eliminator all
    # route through the macro-derived fields. Constructor / elim
    # forwarders η-expand to match the Nix-level arity the old
    # hand-written spellings exposed, so `absurdFin0` below and every
    # downstream consumer (`app fin n`, `fzero m`, `fsuc m k`,
    # `finElim P Pz Ps n k`) keeps its surface shape.
    finDesc = self.FinDT.D;
    fin     = self.FinDT.T;
    fzero   = m: self.app self.FinDT.fzero m;
    fsuc    = m: k: self.app (self.app self.FinDT.fsuc m) k;
    finElim = P: Pz: Ps: n: k:
      self.app (self.app (self.app (self.app (self.app self.FinDT.elim P) Pz) Ps) n) k;

    # absurdFin0 : (P : U) → Fin 0 → P
    # Fin 0 is vacuous: both constructor payloads carry an `em : Eq (succ m) n`
    # leaf, and at n = 0 combining with the outer `e0 : Eq n zero` gives
    # `emz : Eq (succ m) zero`. The no-confusion step J-transports `tt :
    # Unit` along `emz` at motive `λx _. natCaseU P Unit x`, landing at
    # `Unit` when x ≡ succ m (base case: `tt` inhabits `Unit`) and at `P`
    # when x ≡ zero (the goal). A single J targets `P` directly — no
    # `Void` intermediate is required.
    absurdFin0 = P: x:
      let
        inherit (self)
          lam forall app fst_ snd_
          nat zero succ j natCaseU
          eq refl
          muI descCon descInd interpHoas allHoas
          sumPrim sumElimPrim inlPrim inrPrim
          descArg retI recI
          finDesc transNat unitPrim ttPrim;

        muFam = lam "i" nat (i: muI nat finDesc i);

        fzeroSum = descArg nat (m_: retI (succ m_));
        fsucSum  = descArg nat (m_: recI m_ (retI (succ m_)));
        lInterpAt = iArg_: interpHoas nat fzeroSum muFam iArg_;
        rInterpAt = iArg_: interpHoas nat fsucSum  muFam iArg_;

        Q = lam "i" nat (iArg: lam "_" (muI nat finDesc iArg) (_:
              forall "_" (eq nat iArg zero) (_: P)));

        # noConf m emz : P given emz : Eq Nat (succ m) zero.
        # J at motive `λx _. natCaseU P Unit x` with base `tt : Unit`;
        # result `natCaseU P Unit zero ≡ P`.
        noConf = m: emz:
          j nat (succ m)
            (lam "x" nat (x: lam "_" (eq nat (succ m) x) (_:
              app (natCaseU P unitPrim) x)))
            ttPrim
            zero
            emz;

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
                       in noConf m emz);
                     onInr = lam "r" rInterp (r:
                       let m = fst_ r;
                           em = snd_ (snd_ r);
                           emz = transNat (succ m) nArg zero em e0;
                       in noConf m emz);
                   in sumElimPrim lInterp rInterp sumMot onInl onInr d))));
      in app (descInd finDesc Q step zero x) refl;

    # natCaseU A B : Nat → U — `natCaseU A B zero ≡ A`;
    # `natCaseU A B (succ _) ≡ B`. Implemented as `descInd nat.D` with
    # step dispatching via `sumElimPrim` on `d : Sum (⟦descRet⟧ muFam
    # iArg) (⟦descRec descRet⟧ muFam iArg)` — the inl branch yields A,
    # the inr branch yields B. Used by `vhead` to dispatch the vecElim
    # motive across vnil/vcons (`natCaseU unit A`: vnil target is `unit`,
    # inhabited by `tt`; vcons target is `A`, inhabited by the head
    # element) and by `absurdFin0` to target `P` at `zero` and `Unit` at
    # `succ _` in the no-confusion J-transport. The IH is discarded —
    # discrimination doesn't depend on recursion.
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

    # Vec prelude forwarders onto `VecDT` (defined in
    # `hoas/datatype.nix` via `datatypePI "Vec" [{A; U₀}] (_: nat) …`).
    # `natPredCase` / `vhead` / `vtail` below still reference
    # `vec` / `vecElim` by name and continue to work unchanged.
    vecDesc = A: self.app self.VecDT.D A;
    vec     = A: self.app self.VecDT.T A;
    vnil    = A: self.app self.VecDT.vnil A;
    vcons   = A: m: x: xs:
      self.app (self.app (self.app (self.app self.VecDT.vcons A) m) x) xs;
    vecElim = A: P: Pn: Pc: n: xs:
      self.app (self.app (self.app (self.app (self.app (self.app self.VecDT.elim A) P) Pn) Pc) n) xs;

    # natPredCase A : Nat → U —
    #   `natPredCase A zero ≡ unit`,
    #   `natPredCase A (succ m) ≡ vec A m`.
    # Case-split on Nat whose succ-case return type depends on the
    # predecessor (extracted as `fst_ r` from the plus summand's
    # payload via `sumElimPrim` dispatch). Used by `vtail` to build the
    # vecElim motive `P n xs = natPredCase A n` so the vnil branch
    # targets `unit` (filled by `tt`) and the vcons branch targets
    # `vec A m` (filled by the tail). Generalises the `natCaseU`
    # pattern to payload-dependent succ cases.
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
    # Eq-as-description forwarders onto `EqDT` (defined in
    # `hoas/datatype.nix` via `datatypePI "Eq" …`). The iso proofs
    # `eqToEqDT` / `eqDTToEq` / `eqIsoFwd` / `eqIsoBwd` below reference
    # `eqDesc` / `eqDT` / `reflDT` by name and continue to work
    # unchanged — they live in user space and are not macro-output.
    eqDesc = A: a: self.app (self.app self.EqDT.D A) a;
    eqDT   = A: a: b: self.app (self.app (self.app self.EqDT.T A) a) b;
    reflDT = A: a: self.app (self.app self.EqDT.refl A) a;

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
    # `d : Sum (Eq ⊤ ttPrim iArg) (Eq ⊤ ttPrim iArg)`, J-transporting
    # each user-supplied branch across the leaf-equality witness. The
    # J-base is `refl` at `iArg = ttPrim`
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
