# Type-checking kernel: Term constructors (Tm)
#
# Core term language with de Bruijn indices. All binding uses indices.
# Name annotations are cosmetic (for error messages only).
# Uses `tag` (not `_tag`) to distinguish from effect system nodes.
#
# Spec reference: kernel-spec.md §2
{ api, ... }:
let
  # Smart constructors — validate structure at construction time.
  # Each returns an attrset with `tag` field.

  # -- Variables and binding --
  mkVar = i: { tag = "var"; idx = i; };
  mkLet = name: type: val: body: { tag = "let"; inherit name type val body; };
  mkAnn = term: type: { tag = "ann"; inherit term type; };
  # `mkAnnTrusted` — kernel-internal annotation whose body is known to
  # have the annotated type by construction (the elaborator emits it
  # around encoded descriptions whose well-typedness follows from the
  # encoder lambdas' polymorphic types). Identical to `mkAnn` at eval/
  # conv/quote (a `trusted` field is invisible to the structural rules);
  # `infer` reads `tm.trusted` and skips the body re-check, which would
  # otherwise dominate per-layer cost in deep recursive-data CHECK
  # (5000-stress) where each layer's element-D inference fires once per
  # layer. The HOAS surface does not expose a path to this constructor
  # — only `hoas/datatype.nix` for the per-datatype `D` annotation.
  mkAnnTrusted = term: type: { tag = "ann"; inherit term type; trusted = true; };
  mkAnnTrustedWithDescRef = term: type: descRef:
    { tag = "ann"; inherit term type; _descRef = descRef; trusted = true; };
  # `mkAnnTrustedWithLabels` — vehicle for erasable presentation labels
  # that ride on a description-encoding term. Two orthogonal slots:
  #   - `field` : Maybe String — the per-node binding name. Propagates
  #     to `_label`. Set by `H.field`/`H.recField`/`H.piField`/
  #     `H.withDescLabel`.
  #   - `con`   : Maybe String — the surrounding constructor's name.
  #     Propagates to `_conLabel`. Set by `H.con` (via `H.withConLabel`).
  # The two are orthogonal because nesting a single `_label` slot would
  # cause the outer wrap (constructor) to overwrite the inner (first
  # field's name) when conDesc's first emission already carries a label.
  # Both are sidecar metadata: eval copies them onto the resulting value,
  # conv ignores them (operates structurally on `.D/.i/.d`), so
  # definitional equality stays label-irrelevant on both axes. The
  # elaborator emits this around `desc-{ret,arg,rec,pi,plus}-enc`
  # encoder application chains when the HOAS form carries `_label` or
  # `_conLabel` or both. The body is type-correct by construction
  # (closed encoder application), so `trusted = true` skips body re-check.
  mkAnnTrustedWithLabels = term: type: labels:
    let
      field = labels.field or null;
      con = labels.con   or null;
      base = { tag = "ann"; inherit term type; trusted = true; };
    in
    base
    // (if field != null then { _label = field; } else { })
    // (if con != null then { _conLabel = con; } else { });

  # -- Functions --
  mkPi = name: domain: codomain: { tag = "pi"; inherit name domain codomain; };
  mkLam = name: domain: body: { tag = "lam"; inherit name domain body; };
  mkApp = fn: arg: { tag = "app"; inherit fn arg; };

  # -- Pairs --
  mkSigma = name: fst: snd: { tag = "sigma"; inherit name fst snd; };
  mkPair = fst: snd: { tag = "pair"; inherit fst snd; };
  mkFst = pair: { tag = "fst"; inherit pair; };
  mkSnd = pair: { tag = "snd"; inherit pair; };

  # -- Unit --
  mkUnit = { tag = "unit"; };
  mkTt = { tag = "tt"; };

  # -- Empty --
  mkEmpty = { tag = "empty"; };
  mkAbsurd = type: term: { tag = "absurd"; inherit type term; };

  # -- Bootstrap coproduct for descPlus --
  mkBootSum = left: right: { tag = "boot-sum"; inherit left right; };
  mkBootInl = left: right: term: { tag = "boot-inl"; inherit left right term; };
  mkBootInr = left: right: term: { tag = "boot-inr"; inherit left right term; };
  mkBootSumElim = left: right: motive: onLeft: onRight: scrut:
    { tag = "boot-sum-elim"; inherit left right motive onLeft onRight scrut; };

  # -- Identity --
  mkBootEq = type: lhs: rhs: { tag = "boot-eq"; inherit type lhs rhs; };
  mkBootRefl = { tag = "boot-refl"; };
  mkBootJ = type: lhs: motive: base: rhs: eq:
    { tag = "boot-j"; inherit type lhs motive base rhs eq; };

  # -- Propositional truncation (Squash) --
  # `Squash A : U(l)` for `A : U(l)`. Inhabitants are definitionally
  # equal. `recTrunc A B f x : Squash B` for `f : A → Squash B`,
  # `x : Squash A`; the motive is restricted to `Squash _` at INFER
  # time so irrelevance cannot escape into a non-`Squash` position.
  mkSquash = A: { tag = "squash";       inherit A; };
  mkSquashIntro = a: { tag = "squash-intro"; inherit a; };
  mkSquashElim = A: B: f: x: { tag = "squash-elim";  inherit A B f x; };

  # -- Function extensionality postulate --
  # Atomic constant whose type is the closed 7-layer Π chain
  # `funextTypeTm` below. No reduction rule; inhabits
  # `Eq (Π(a:A). B a) f g` given a pointwise-equality witness.
  mkFunext = { tag = "funext"; };

  # Closed Π chain serving as the type of `funext`, heterogeneous in
  # the levels of the domain `A` and the codomain `B a`:
  #   Π(j : Level).
  #   Π(k : Level).
  #   Π(A : U(j)).
  #   Π(B : A → U(k)).
  #   Π(f : Π(a:A). B a).
  #   Π(g : Π(a:A). B a).
  #   Π(_ : Π(a:A). Eq (B a) (f a) (g a)).
  #     Eq (Π(a:A). B a) f g
  # De Bruijn depths — at the Pi-body introducing binder b (b = 0..6):
  #   b=0 (j bound): j=0.
  #   b=1 (k bound): k=0, j=1.
  #   b=2 (A bound): A=0, k=1, j=2.
  #   b=3 (B bound): B=0, A=1, k=2, j=3.
  #   b=4 (f bound): f=0, B=1, A=2, k=3, j=4.
  #   b=5 (g bound): g=0, f=1, B=2, A=3, k=4, j=5.
  #   b=6 (hyp bound): hyp=0, g=1, f=2, B=3, A=4, k=5, j=6.
  # B's domain `Π(_:A). U(k)` opens an `_:A` binder under which the
  # k-binder sits at index 2 (between A above and `_` below). The
  # innermost Eq type `Π(a:A). B a` opens another a-binder under
  # which a=0 and every outer var shifts by 1. The inner spine
  # references {A, B, f, g, hyp} only — never j or k — so the new
  # k-binder slotted between j and A leaves every inner-spine Var
  # index unchanged; only A's `U(?)` annotation references j and
  # shifts from index 0 to index 1.
  funextTypeTm =
    mkPi "j" mkLevel
      (mkPi "k" mkLevel
        (mkPi "A" (mkU (mkVar 1))
          (mkPi "B" (mkPi "_" (mkVar 0) (mkU (mkVar 2)))
            (mkPi "f" (mkPi "a" (mkVar 1) (mkApp (mkVar 1) (mkVar 0)))
              (mkPi "g" (mkPi "a" (mkVar 2) (mkApp (mkVar 2) (mkVar 0)))
                (mkPi "_"
                  (mkPi "a" (mkVar 3)
                    (mkBootEq
                      (mkApp (mkVar 3) (mkVar 0))
                      (mkApp (mkVar 2) (mkVar 0))
                      (mkApp (mkVar 1) (mkVar 0))))
                  (mkBootEq
                    (mkPi "a" (mkVar 4) (mkApp (mkVar 4) (mkVar 0)))
                    (mkVar 2)
                    (mkVar 1))))))));

  # -- Descriptions --
  # `desc^k I` carries an explicit universe level `k` (Level Tm).
  # Callers pass a Level Tm directly; integer literals must be
  # wrapped explicitly via `mkLevelLit n` (or `mkLevelZero` /
  # `mkLevelSuc mkLevelZero` for the common 0/1 cases).
  #
  # `iLev` records the universe of `I`. Defaults to `mkLevelZero` for
  # the ⊤-slice prelude (`I = Unit : U(0)`); user descriptions whose
  # index type lives at `U(n)` for `n > 0` emit `mkDescAt` directly.
  # The kernel's desc-formation rule synthesizes the result universe
  # as `U(suc (max k iLev))`.
  mkDescAt = iLev: k: I: { tag = "desc"; inherit k I iLev; };
  mkDesc = k: I: mkDescAt mkLevelZero k I;
  mkMu = I: D: i: { tag = "mu"; inherit I D i; };
  mkDescCon = D: i: d: { tag = "desc-con"; inherit D i d; };
  mkDescConWithCert = D: i: d: cert:
    { tag = "desc-con"; inherit D i d; _descConCert = cert; };
  # Flat-form linear-chain encoding of an N-deep mkDescCon. Bijective
  # dual of the chain-form Val (`_shape == "linearChain"`): chain-wide
  # outer fields on the head, per-layer `{ i; heads }` records in a
  # flat Nix-list (outer-first), `base = { D; i; d }` at the terminator.
  # libnix walks the list iteratively, so `forceValueDeep` depth is
  # O(1) regardless of N.
  mkDescConChain = args:
    { tag = "desc-con-chain";
      inherit (args) layers base outerD payloadTag payloadLeft payloadRight;
    };
  mkDescInd = D: motive: step: i: scrut:
    { tag = "desc-ind"; inherit D motive step i scrut; };
  # `interpD ℓ I D X i : U(ℓ)` — kernel-primitive interpretation of a
  # description. CDMM 2010 Table 6.2 classifies `⟦_⟧` as a meta-theory
  # primitive; making it a Tm constant (rather than a HOAS macro) keeps
  # eliminator-application Tms structurally identical between producer
  # and consumer paths and removes the meta-time Level-ascent recursion
  # that HOAS macros incur. Reduction rules pattern-match on D's outer
  # constructor:
  #   interpD ℓ I (descRet j)        X i ⇝ Lift 0 ℓ refl (Eq I j i)
  #   interpD ℓ I (descArg _ _ S T)  X i ⇝ Σ s:S. interpD ℓ I (T s) X i
  #   interpD ℓ I (descRec j D)      X i ⇝ Σ _:X j. interpD ℓ I D X i
  #   interpD ℓ I (descPi _ _ S f D) X i ⇝ Σ _:(Π s:S. X (f s)). interpD ℓ I D X i
  #   interpD ℓ I (descPlus A B)     X i ⇝ interpD ℓ I A X i ⊎ interpD ℓ I B X i
  mkInterpD = level: I: D: X: i:
    { tag = "interp-d"; inherit level I D X i; };

  # `allD ℓ I D K X M i d : U(K)` — kernel-primitive All-witness type
  # over a description. Mirrors the per-summand on-cases of CDMM `All`:
  #   allD ℓ I (descRet j)        K X M i d ⇝ Lift 0 K refl Unit
  #   allD ℓ I (descArg _ _ S T)  K X M i d ⇝ allD ℓ I (T (fst d)) K X M i (snd d)
  #   allD ℓ I (descRec j D)      K X M i d ⇝ Σ _:M j (fst d). allD ℓ I D K X M i (snd d)
  #   allD ℓ I (descPi _ _ S f D) K X M i d ⇝
  #     Σ _:Π(s:S). M (f s) ((fst d) s). allD ℓ I D K X M i (snd d)
  #   allD ℓ I (descPlus A B)     K X M i d ⇝
  #     case d of inl a → allD ℓ I A K X M i a | inr b → allD ℓ I B K X M i b
  mkAllD = level: I: D: K: X: M: i: d:
    { tag = "all-d"; inherit level I D K X M i d; };

  # `everywhereD ℓ I D K X M ih i d : allD ℓ I D K X M i d` — kernel-
  # primitive proof that every recursive subobject in `d` satisfies `M`,
  # given a witness `ih : Π(j:I)(x:X j). M j x`. Drives the `descInd`
  # iota:
  #   descInd D M m (descCon D' tt x) ⇝
  #     m i x (everywhereD ℓ I D K X (λj.λxv.M xv) ih i x)
  mkEverywhereD = level: I: D: K: X: M: ih: i: d:
    { tag = "everywhere-d"; inherit level I D K X M ih i d; };

  # `descDescApp iLev I L : μ⊤(descDesc iLev I (suc L)) tt` — identity-
  # tagged invocation of `descDesc` at parameters `(iLev, I, L)`. `iLev`
  # records the universe of `I`; the encoder's outer signature is
  # generalised to `λiLev:Level. λI:U(iLev). λL:Level. …`. The eval rule
  # stamps `_canonRef = { id = "descDesc"; params = [iLev, I, L]; }` on
  # the outer VDescCon so conv and quote can short-circuit on the tag.
  #
  # `mkDescDescApp I L` is the level-zero convenience form for the
  # ⊤-slice prelude where every `I` lives at `U(0)`.
  mkDescDescAppAt = iLev: I: L: { tag = "desc-desc-app"; inherit iLev I L; };
  mkDescDescApp = I: L: mkDescDescAppAt mkLevelZero I L;

  # `canonApp id params body : T`, where `T` is the type of
  # `body` applied to every param — generic counterpart of
  # `descDescApp` for user-registered canonical descriptions. The eval
  # rule applies `body` to each param in left-to-right order and stamps
  # the resulting `VDescCon` with `_canonRef = { id; params; }`, so conv
  # and quote short-circuit on the canonical identity instead of forcing
  # `.D`. `body` must reduce to a curried chain of `VLam`s that, after
  # consuming `params`, yields a `VDescCon`.
  mkCanonApp = id: params: body:
    { tag = "canon-app"; inherit id params body; };

  # -- Lift primitive --
  # Tarski + non-cumulative cross-level transport. `Lift l m eq A : U(m)`
  # is the type of values transported from `A : U(l)` up to `U(m)`,
  # given a bound witness `eq : Eq Level (max l m) m` proving `l ≤ m`
  # decidably via `convLevel`. Conv collapses `Lift l l _ A ≡ A`
  # (idempotent at equal levels), `lower _ (lift _ a) ≡ a` (β),
  # `lift _ (lower _ x) ≡ x` (η), composition of nested Lifts. The
  # `eq` slot is witness-irrelevant: two Lifts with matching levels and
  # underlying type are conv-equal regardless of the proof carried.
  mkLift = l: m: eq: A: { tag = "lift";       inherit l m eq A; };
  mkLiftIntro = l: m: eq: A: a: { tag = "lift-intro"; inherit l m eq A a; };
  mkLiftElim = l: m: eq: A: x: { tag = "lift-elim";  inherit l m eq A x; };

  # -- Level sort --
  # Tarski-style explicit universe levels. `Level` inhabits `U(0)`.
  # Level expressions are built from `zero`, `suc`, and `max`; conv
  # normalises them (idempotence of max, distribution of suc, zero
  # absorption, sorted spine) before comparing structurally.
  mkLevel = { tag = "level"; };
  mkLevelZero = { tag = "level-zero"; };
  mkLevelSuc = pred: { tag = "level-suc"; inherit pred; };
  mkLevelMax = lhs: rhs: { tag = "level-max"; inherit lhs rhs; };

  # Concrete-level literal: builds `suc^n zero` as a kernel Level term.
  mkLevelLit = n:
    if n <= 0 then mkLevelZero
    else mkLevelSuc (mkLevelLit (n - 1));

  # -- Universes --
  # `U` carries a Level-typed Tm. Callers pass a Level Tm directly;
  # integer literals must be wrapped explicitly via `mkLevelLit n`
  # (or `mkLevelZero` / `mkLevelSuc mkLevelZero` for the common 0/1
  # cases).
  mkU = level: { tag = "U"; inherit level; };

  # -- Axiomatized primitives --
  mkString = { tag = "string"; };
  mkInt = { tag = "int"; };
  mkFloat = { tag = "float"; };
  mkAttrs = { tag = "attrs"; };
  mkPath = { tag = "path"; };
  mkDerivation = { tag = "derivation"; };
  mkFunction = { tag = "function"; };
  mkAny = { tag = "any"; };

  # -- String operations --
  mkStrEq = lhs: rhs: { tag = "str-eq"; inherit lhs rhs; };

  # -- Int operations --
  mkIntLe = lhs: rhs: { tag = "int-le"; inherit lhs rhs; };
  mkIntEq = lhs: rhs: { tag = "int-eq"; inherit lhs rhs; };

  # -- Primitive literals --
  mkStringLit = s: { tag = "string-lit"; value = s; };
  mkIntLit = n: { tag = "int-lit"; value = n; };
  mkFloatLit = f: { tag = "float-lit"; value = f; };
  mkAttrsLit = { tag = "attrs-lit"; };
  mkPathLit = { tag = "path-lit"; };
  mkDerivationLit = { tag = "derivation-lit"; };
  mkFnLit = { tag = "fn-lit"; };
  mkAnyLit = { tag = "any-lit"; };

  # Opaque lambda: trust boundary for negative types (Pi).
  # Carries a Nix function opaquely — the kernel never inspects or applies it.
  # fnBox is a { _fn = nixFn; } attrset created once at the HOAS level and
  # propagated as-is through eval/quote/check. Nix attrset == uses thunk
  # identity for function-valued fields, so preserving the same fnBox object
  # ensures conv reflexivity. Direct function == always returns false.
  mkOpaqueLam = fnBox: piTy: { tag = "opaque-lam"; _fnBox = fnBox; inherit piTy; };

  # Closed-Val splice (two-level TT). `eval ρ (LitVal v) = v` independent
  # of ρ — sound iff v is closed. O(1) Val→Tm reflection.
  mkLitVal = val: { tag = "lit-val"; inherit val; };

in
api.namespace {
  description = "fx.tc.term: kernel term constructors (Pi, Sigma, U, Id, J, datatype/desc nodes) de-Bruijn indexed; each carries `tag` distinct from value-domain `_tag`.";
  doc = ''
    # fx.tc.term — Core Term Constructors (Tm)

    Syntax of the kernel's term language. All 48 constructors produce
    attrsets with a `tag` field (not `_tag`, to distinguish kernel terms
    from effect system nodes). Binding is de Bruijn indexed: `mkVar i`
    refers to the i-th enclosing binder (0 = innermost).

    Name annotations (`name` parameter on `mkPi`, `mkLam`, `mkSigma`,
    `mkLet`) are cosmetic — used only in error messages, never in
    equality checking.

    ## Constructors

    ### Variables and Binding
    - `mkVar : Int → Tm` — variable by de Bruijn index
    - `mkLet : String → Tm → Tm → Tm → Tm` — `let name : type = val in body`
    - `mkAnn : Tm → Tm → Tm` — type annotation `(term : type)`

    ### Functions
    - `mkPi : String → Tm → Tm → Tm` — dependent function type `Π(name : domain). codomain`
    - `mkLam : String → Tm → Tm → Tm` — lambda `λ(name : domain). body`
    - `mkApp : Tm → Tm → Tm` — application `fn arg`

    ### Pairs
    - `mkSigma : String → Tm → Tm → Tm` — dependent pair type `Σ(name : fst). snd`
    - `mkPair : Tm → Tm → Tm` — pair constructor `(fst, snd)`
    - `mkFst : Tm → Tm` — first projection
    - `mkSnd : Tm → Tm` — second projection

    ### Inductive Types
    - `mkUnit`, `mkTt` — unit type and value
    - `mkBootSum`, `mkBootInl`, `mkBootInr`, `mkBootSumElim` — bootstrap coproduct for `descPlus`
    - `mkBootEq`, `mkBootRefl`, `mkBootJ` — identity type with J eliminator

    ### Universes
    - `mkU : (Int | Tm) → Tm` — universe `U(level)`. Accepts either a
      concrete Int (wrapped via `mkLevelLit`) or a Level-typed Tm
      directly.
    - `mkLevelLit : Int → Tm` — builds `suc^n zero` as a Level term.

    ### Axiomatized Primitives
    - `mkString`, `mkInt`, `mkFloat`, `mkAttrs`, `mkPath`, `mkDerivation`, `mkFunction`, `mkAny` — type formers
    - `mkStringLit`, `mkIntLit`, `mkFloatLit`, `mkAttrsLit`, `mkPathLit`, `mkDerivationLit`, `mkFnLit`, `mkAnyLit` — literal values
  '';
  tests = {
    "var-tag" = { expr = (mkVar 0).tag; expected = "var"; };
    "var-idx" = { expr = (mkVar 3).idx; expected = 3; };
    "pi-tag" = { expr = (mkPi "x" mkUnit mkUnit).tag; expected = "pi"; };
    "lam-tag" = { expr = (mkLam "x" mkUnit (mkVar 0)).tag; expected = "lam"; };
    "app-tag" = { expr = (mkApp (mkVar 0) mkTt).tag; expected = "app"; };
    "sigma-tag" = { expr = (mkSigma "x" mkUnit mkUnit).tag; expected = "sigma"; };
    "pair-tag" = { expr = (mkPair mkTt mkTt).tag; expected = "pair"; };
    "fst-tag" = { expr = (mkFst (mkVar 0)).tag; expected = "fst"; };
    "snd-tag" = { expr = (mkSnd (mkVar 0)).tag; expected = "snd"; };
    "unit-tag" = { expr = mkUnit.tag; expected = "unit"; };
    "tt-tag" = { expr = mkTt.tag; expected = "tt"; };
    "boot-sum-tag" = { expr = (mkBootSum mkUnit mkUnit).tag; expected = "boot-sum"; };
    "boot-inl-tag" = { expr = (mkBootInl mkUnit mkUnit mkTt).tag; expected = "boot-inl"; };
    "boot-inr-tag" = { expr = (mkBootInr mkUnit mkUnit mkTt).tag; expected = "boot-inr"; };
    "boot-eq-tag" = { expr = (mkBootEq mkUnit mkTt mkTt).tag; expected = "boot-eq"; };
    "boot-refl-tag" = { expr = mkBootRefl.tag; expected = "boot-refl"; };
    "j-tag" = {
      expr = (mkBootJ mkUnit mkTt (mkVar 0) (mkVar 1) mkTt mkBootRefl).tag;
      expected = "boot-j";
    };
    "squash-tag" = { expr = (mkSquash mkUnit).tag; expected = "squash"; };
    "squash-A" = { expr = (mkSquash mkUnit).A.tag; expected = "unit"; };
    "squash-intro-tag" = { expr = (mkSquashIntro mkTt).tag; expected = "squash-intro"; };
    "squash-intro-a" = { expr = (mkSquashIntro mkTt).a.tag; expected = "tt"; };
    "squash-elim-tag" = {
      expr = (mkSquashElim mkUnit mkUnit
        (mkLam "_" mkUnit (mkSquashIntro mkTt))
        (mkSquashIntro mkTt)).tag;
      expected = "squash-elim";
    };
    "squash-elim-A" = {
      expr = (mkSquashElim mkUnit mkUnit
        (mkLam "_" mkUnit (mkSquashIntro mkTt))
        (mkSquashIntro mkTt)).A.tag;
      expected = "unit";
    };
    "U-tag" = { expr = (mkU mkLevelZero).tag; expected = "U"; };
    "U-level-zero" = { expr = (mkU mkLevelZero).level.tag; expected = "level-zero"; };
    "U-level-suc" = {
      expr = (mkU (mkLevelSuc mkLevelZero)).level.tag;
      expected = "level-suc";
    };
    "U-level-suc-pred" = {
      expr = (mkU (mkLevelSuc mkLevelZero)).level.pred.tag;
      expected = "level-zero";
    };
    "U-level-max" = {
      expr = (mkU (mkLevelMax mkLevelZero mkLevelZero)).level.tag;
      expected = "level-max";
    };
    "level-tag" = { expr = mkLevel.tag; expected = "level"; };
    "level-zero-tag" = { expr = mkLevelZero.tag; expected = "level-zero"; };
    "level-suc-tag" = { expr = (mkLevelSuc mkLevelZero).tag; expected = "level-suc"; };
    "level-suc-pred" = { expr = (mkLevelSuc mkLevelZero).pred.tag; expected = "level-zero"; };
    "level-max-tag" = { expr = (mkLevelMax mkLevelZero mkLevelZero).tag; expected = "level-max"; };
    "level-lit-0" = { expr = (mkLevelLit 0).tag; expected = "level-zero"; };
    "level-lit-1-tag" = { expr = (mkLevelLit 1).tag; expected = "level-suc"; };
    "level-lit-1-pred" = { expr = (mkLevelLit 1).pred.tag; expected = "level-zero"; };
    "level-lit-2-pred-tag" = { expr = (mkLevelLit 2).pred.tag; expected = "level-suc"; };
    "level-lit-negative-clamps-to-zero" = {
      expr = (mkLevelLit (-3)).tag;
      expected = "level-zero";
    };
    "let-tag" = { expr = (mkLet "x" mkUnit mkTt (mkVar 0)).tag; expected = "let"; };
    "ann-tag" = { expr = (mkAnn mkTt mkUnit).tag; expected = "ann"; };
    "string-tag" = { expr = mkString.tag; expected = "string"; };
    "int-tag" = { expr = mkInt.tag; expected = "int"; };
    "float-tag" = { expr = mkFloat.tag; expected = "float"; };
    "attrs-tag" = { expr = mkAttrs.tag; expected = "attrs"; };
    "path-tag" = { expr = mkPath.tag; expected = "path"; };
    "derivation-tag" = { expr = mkDerivation.tag; expected = "derivation"; };
    "function-tag" = { expr = mkFunction.tag; expected = "function"; };
    "any-tag" = { expr = mkAny.tag; expected = "any"; };
    "string-lit-tag" = { expr = (mkStringLit "hello").tag; expected = "string-lit"; };
    "string-lit-value" = { expr = (mkStringLit "hello").value; expected = "hello"; };
    "int-lit-tag" = { expr = (mkIntLit 42).tag; expected = "int-lit"; };
    "int-lit-value" = { expr = (mkIntLit 42).value; expected = 42; };
    "float-lit-tag" = { expr = (mkFloatLit 3.14).tag; expected = "float-lit"; };
    "float-lit-value" = { expr = (mkFloatLit 3.14).value; expected = 3.14; };
    "attrs-lit-tag" = { expr = mkAttrsLit.tag; expected = "attrs-lit"; };
    "path-lit-tag" = { expr = mkPathLit.tag; expected = "path-lit"; };
    "derivation-lit-tag" = { expr = mkDerivationLit.tag; expected = "derivation-lit"; };
    "fn-lit-tag" = { expr = mkFnLit.tag; expected = "fn-lit"; };
    "any-lit-tag" = { expr = mkAnyLit.tag; expected = "any-lit"; };
    "opaque-lam-tag" = { expr = (mkOpaqueLam { _fn = (x: x); } mkUnit).tag; expected = "opaque-lam"; };
    "opaque-lam-piTy" = { expr = (mkOpaqueLam { _fn = (x: x); } mkUnit).piTy.tag; expected = "unit"; };
    "opaque-lam-fnBox" = { expr = (mkOpaqueLam { _fn = (x: x); } mkUnit)._fnBox ? _fn; expected = true; };

    # Descriptions (indexed)
    "desc-tag" = { expr = (mkDesc mkLevelZero mkUnit).tag; expected = "desc"; };
    "desc-I" = { expr = (mkDesc mkLevelZero mkUnit).I.tag; expected = "unit"; };
    "desc-k-zero" = {
      expr = (mkDesc mkLevelZero mkUnit).k.tag;
      expected = "level-zero";
    };
    "desc-k-non-zero" = {
      expr = (mkDesc (mkLevelSuc mkLevelZero) mkUnit).k.tag;
      expected = "level-suc";
    };
    "mu-tag" = { expr = (mkMu mkUnit (mkVar 0) mkTt).tag; expected = "mu"; };
    "mu-I" = { expr = (mkMu mkUnit (mkVar 0) mkTt).I.tag; expected = "unit"; };
    "mu-D" = { expr = (mkMu mkUnit (mkVar 0) mkTt).D.tag; expected = "var"; };
    "mu-i" = { expr = (mkMu mkUnit (mkVar 0) mkTt).i.tag; expected = "tt"; };
    "desc-con-tag" = {
      expr = (mkDescCon (mkVar 0) mkTt mkBootRefl).tag;
      expected = "desc-con";
    };
    "desc-con-D" = {
      expr = (mkDescCon (mkVar 0) mkTt mkBootRefl).D.tag;
      expected = "var";
    };
    "desc-con-i" = {
      expr = (mkDescCon (mkVar 0) mkTt mkBootRefl).i.tag;
      expected = "tt";
    };
    "desc-ind-tag" = {
      expr = (mkDescInd (mkVar 0) (mkVar 1) (mkVar 2) mkTt (mkVar 3)).tag;
      expected = "desc-ind";
    };
    "desc-ind-i" = {
      expr = (mkDescInd (mkVar 0) (mkVar 1) (mkVar 2) mkTt (mkVar 3)).i.tag;
      expected = "tt";
    };

    # interpD / allD / everywhereD primitives
    "interp-d-tag" = {
      expr = (mkInterpD mkLevelZero mkUnit (mkVar 0) (mkVar 1) mkTt).tag;
      expected = "interp-d";
    };
    "interp-d-level" = {
      expr = (mkInterpD mkLevelZero mkUnit (mkVar 0) (mkVar 1) mkTt).level.tag;
      expected = "level-zero";
    };
    "interp-d-I" = {
      expr = (mkInterpD mkLevelZero mkUnit (mkVar 0) (mkVar 1) mkTt).I.tag;
      expected = "unit";
    };
    "interp-d-D" = {
      expr = (mkInterpD mkLevelZero mkUnit (mkVar 0) (mkVar 1) mkTt).D.tag;
      expected = "var";
    };
    "interp-d-i" = {
      expr = (mkInterpD mkLevelZero mkUnit (mkVar 0) (mkVar 1) mkTt).i.tag;
      expected = "tt";
    };
    "all-d-tag" = {
      expr = (mkAllD mkLevelZero mkUnit (mkVar 0) mkLevelZero
        (mkVar 0)
        (mkVar 1)
        mkTt
        mkBootRefl).tag;
      expected = "all-d";
    };
    "all-d-K" = {
      expr = (mkAllD mkLevelZero mkUnit (mkVar 0) (mkLevelSuc mkLevelZero)
        (mkVar 0)
        (mkVar 1)
        mkTt
        mkBootRefl).K.tag;
      expected = "level-suc";
    };
    "all-d-d" = {
      expr = (mkAllD mkLevelZero mkUnit (mkVar 0) mkLevelZero
        (mkVar 0)
        (mkVar 1)
        mkTt
        mkBootRefl).d.tag;
      expected = "boot-refl";
    };
    "everywhere-d-tag" = {
      expr = (mkEverywhereD mkLevelZero mkUnit (mkVar 0) mkLevelZero
        (mkVar 0)
        (mkVar 1)
        (mkVar 2)
        mkTt
        mkBootRefl).tag;
      expected = "everywhere-d";
    };
    "everywhere-d-ih" = {
      expr = (mkEverywhereD mkLevelZero mkUnit (mkVar 0) mkLevelZero
        (mkVar 0)
        (mkVar 1)
        (mkVar 7)
        mkTt
        mkBootRefl).ih.idx;
      expected = 7;
    };
    "desc-desc-app-tag" = {
      expr = (mkDescDescApp mkUnit mkLevelZero).tag;
      expected = "desc-desc-app";
    };
    "desc-desc-app-I" = {
      expr = (mkDescDescApp mkUnit mkLevelZero).I.tag;
      expected = "unit";
    };
    "desc-desc-app-L" = {
      expr = (mkDescDescApp mkUnit (mkLevelSuc mkLevelZero)).L.tag;
      expected = "level-suc";
    };

    # Lift primitive
    "lift-tag" = { expr = (mkLift mkLevelZero mkLevelZero mkBootRefl mkUnit).tag; expected = "lift"; };
    "lift-l-zero" = {
      expr = (mkLift mkLevelZero mkLevelZero mkBootRefl mkUnit).l.tag;
      expected = "level-zero";
    };
    "lift-m-suc" = {
      expr = (mkLift mkLevelZero (mkLevelSuc mkLevelZero) mkBootRefl mkUnit).m.tag;
      expected = "level-suc";
    };
    "lift-A" = { expr = (mkLift mkLevelZero mkLevelZero mkBootRefl mkUnit).A.tag; expected = "unit"; };
    "lift-eq-refl" = { expr = (mkLift mkLevelZero mkLevelZero mkBootRefl mkUnit).eq.tag; expected = "boot-refl"; };
    "lift-intro-tag" = {
      expr = (mkLiftIntro mkLevelZero mkLevelZero mkBootRefl mkUnit mkTt).tag;
      expected = "lift-intro";
    };
    "lift-intro-a" = {
      expr = (mkLiftIntro mkLevelZero mkLevelZero mkBootRefl mkUnit mkTt).a.tag;
      expected = "tt";
    };
    "lift-elim-tag" = {
      expr = (mkLiftElim mkLevelZero mkLevelZero mkBootRefl mkUnit (mkVar 0)).tag;
      expected = "lift-elim";
    };
    "lift-elim-x" = {
      expr = (mkLiftElim mkLevelZero mkLevelZero mkBootRefl mkUnit (mkVar 0)).x.tag;
      expected = "var";
    };

    # Function extensionality postulate
    "funext-tag" = { expr = mkFunext.tag; expected = "funext"; };
    "funext-type-tag" = { expr = funextTypeTm.tag; expected = "pi"; };
    "funext-type-outer-name" = { expr = funextTypeTm.name; expected = "j"; };
    "funext-type-outer-domain-tag" = {
      expr = funextTypeTm.domain.tag;
      expected = "level";
    };
    # The second binder is `k : Level`, sitting between `j` and `A`.
    "funext-type-second-binder-name" = {
      expr = funextTypeTm.codomain.name;
      expected = "k";
    };
    "funext-type-second-binder-domain-tag" = {
      expr = funextTypeTm.codomain.domain.tag;
      expected = "level";
    };
    # A's annotation is `U(j)` with `j = Var 1` (k sits between j and A).
    "funext-type-A-domain-is-U-of-j" = {
      expr = funextTypeTm.codomain.codomain.domain.tag;
      expected = "U";
    };
    "funext-type-A-domain-level-references-j" = {
      expr = funextTypeTm.codomain.codomain.domain.level.tag;
      expected = "var";
    };
    # B's domain is `Π(_:A). U(k)` — a Pi.
    "funext-type-b-domain-is-pi" = {
      expr = funextTypeTm.codomain.codomain.codomain.domain.tag;
      expected = "pi";
    };
    "funext-type-innermost-eq" = {
      # Walk into: j → k → A → B → f → g → hyp → body.
      # Body should be an Eq of (Pi a:A. B a) f g.
      expr = funextTypeTm.codomain   # after j
      .codomain   # after k
      .codomain   # after A
      .codomain   # after B
      .codomain   # after f
      .codomain   # after g
      .codomain   # after hyp (body of outermost Pi chain)
      .tag;
      expected = "boot-eq";
    };
  };

  value = {

    mkVar = api.leaf {
      value = mkVar;
      description = "mkVar: variable reference by de Bruijn index — `0` is the innermost binder; higher indices reach outer binders.";
      signature = "mkVar : Int -> Tm";
    };
    mkLet = api.leaf {
      value = mkLet;
      description = "mkLet: let-binding `let name : type = val in body` — `name` is cosmetic, the binder is introduced into body's de Bruijn context as index `0`.";
      signature = "mkLet : String -> Tm -> Tm -> Tm -> Tm  -- name, type, val, body";
    };
    mkAnn = api.leaf {
      value = mkAnn;
      description = "mkAnn: type annotation `(term : type)` — fixes the checking direction at the kernel level; consumed by `Sub` and elaboration.";
      signature = "mkAnn : Tm -> Tm -> Tm  -- term, type";
    };
    mkAnnTrusted = api.leaf {
      value = mkAnnTrusted;
      description = "mkAnnTrusted: type annotation marked as elaborator-trusted — `check` skips re-validation of `term` against `type` since elaboration has already proved well-typedness.";
      signature = "mkAnnTrusted : Tm -> Tm -> Tm  -- term, type";
    };
    mkAnnTrustedWithDescRef = api.leaf {
      value = mkAnnTrustedWithDescRef;
      description = "mkAnnTrustedWithDescRef: trusted annotation carrying a `_descRef` sidecar — used by the HOAS elaborator to retain levitated description provenance across eval/quote round-trips.";
      signature = "mkAnnTrustedWithDescRef : Tm -> Tm -> Any -> Tm  -- term, type, descRef";
    };
    mkAnnTrustedWithLabels = api.leaf {
      value = mkAnnTrustedWithLabels;
      description = "mkAnnTrustedWithLabels: trusted annotation carrying `_label` / `_conLabel` sidecars — used by `H.withDescLabel` / `H.withConLabel` to surface presentation labels on `descView`.";
      signature = "mkAnnTrustedWithLabels : Tm -> Tm -> { label?, conLabel? } -> Tm";
    };

    mkPi = api.leaf {
      value = mkPi;
      description = "mkPi: dependent function type `Π(name : domain). codomain` — `name` is cosmetic, the binder is introduced into codomain's de Bruijn context as index `0`.";
      signature = "mkPi : String -> Tm -> Tm -> Tm  -- name, domain, codomain";
    };
    mkLam = api.leaf {
      value = mkLam;
      description = "mkLam: lambda abstraction `λ(name : domain). body` — domain annotation is optional at check time (overridden by expected Π's domain).";
      signature = "mkLam : String -> Tm -> Tm -> Tm  -- name, domain, body";
    };
    mkApp = api.leaf {
      value = mkApp;
      description = "mkApp: function application `fn arg` — head `fn` is checked first to infer Π type, then `arg` is checked against the domain.";
      signature = "mkApp : Tm -> Tm -> Tm  -- fn, arg";
    };

    mkSigma = api.leaf {
      value = mkSigma;
      description = "mkSigma: dependent pair type `Σ(name : fst). snd` — `name` is cosmetic, the binder is introduced into snd's de Bruijn context as index `0`.";
      signature = "mkSigma : String -> Tm -> Tm -> Tm  -- name, fst, snd";
    };
    mkPair = api.leaf {
      value = mkPair;
      description = "mkPair: pair constructor `(fst, snd)` — both components are checked against the corresponding Σ slots at the expected type.";
      signature = "mkPair : Tm -> Tm -> Tm  -- fst, snd";
    };
    mkFst = api.leaf {
      value = mkFst;
      description = "mkFst: first-projection eliminator on a Σ-typed term — yields the dependent `fst` component; Σ-eta is exercised in `conv`.";
      signature = "mkFst : Tm -> Tm";
    };
    mkSnd = api.leaf {
      value = mkSnd;
      description = "mkSnd: second-projection eliminator on a Σ-typed term — yields the `snd` component with `fst` substituted; Σ-eta is exercised in `conv`.";
      signature = "mkSnd : Tm -> Tm";
    };

    mkUnit = api.leaf {
      value = mkUnit;
      description = "mkUnit: unit type `Unit` — terminal type with single inhabitant `tt`; backs `fx.types.Unit` at universe level 0.";
    };
    mkTt = api.leaf {
      value = mkTt;
      description = "mkTt: unit value `tt` — sole inhabitant of `mkUnit`; eta-converts every term of type `Unit` to itself.";
    };
    mkEmpty = api.leaf {
      value = mkEmpty;
      description = "mkEmpty: empty type `Empty` — initial type at universe level 0; no constructors.";
    };
    mkAbsurd = api.leaf {
      value = mkAbsurd;
      description = "mkAbsurd: empty-type eliminator — `absurd P x` discharges a stuck `x : Empty` to produce a value of any type `P`; well-typed only when `x` is a neutral (Empty has no canonical inhabitants).";
      signature = "mkAbsurd : Tm -> Tm -> Tm  -- type (P), term (x : Empty)";
    };

    mkBootSum = api.leaf {
      value = mkBootSum;
      description = "mkBootSum: bootstrap coproduct type `A + B` — used by `descPlus` to encode sum-of-descriptions before generic sums become available.";
      signature = "mkBootSum : Tm -> Tm -> Tm  -- left, right";
    };
    mkBootInl = api.leaf {
      value = mkBootInl;
      description = "mkBootInl: left-injection of `mkBootSum` — `inl(a) : A + B`; carries both `A` and `B` for elaboration shape recovery.";
      signature = "mkBootInl : Tm -> Tm -> Tm -> Tm  -- leftTy, rightTy, value";
    };
    mkBootInr = api.leaf {
      value = mkBootInr;
      description = "mkBootInr: right-injection of `mkBootSum` — `inr(b) : A + B`; carries both `A` and `B` for elaboration shape recovery.";
      signature = "mkBootInr : Tm -> Tm -> Tm -> Tm  -- leftTy, rightTy, value";
    };
    mkBootSumElim = api.leaf {
      value = mkBootSumElim;
      description = "mkBootSumElim: bootstrap sum eliminator — case-splits a `A + B` scrutinee through `onLeft`/`onRight` arms at motive `(_:A+B) -> Q _`.";
      signature = "mkBootSumElim : Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm  -- leftTy, rightTy, motive, onLeft, onRight, scrut";
    };

    mkBootEq = api.leaf {
      value = mkBootEq;
      description = "mkBootEq: bootstrap identity type `Eq(A, a, b)` — propositional equality used by `descRet`'s level transport and by the J eliminator.";
      signature = "mkBootEq : Tm -> Tm -> Tm -> Tm  -- A, a, b";
    };
    mkBootRefl = api.leaf {
      value = mkBootRefl;
      description = "mkBootRefl: bootstrap reflexivity `refl : Eq(A, a, a)` — the canonical inhabitant of every reflexive identity type; check-mode only at elaboration.";
    };
    mkBootJ = api.leaf {
      value = mkBootJ;
      description = "mkBootJ: J eliminator on `mkBootEq` — transports a property `motive` along a proof of equality, yielding a term at the other endpoint.";
      signature = "mkBootJ : Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm  -- A, a, motive, identity, b, eq";
    };

    mkSquash = api.leaf {
      value = mkSquash;
      description = "mkSquash: propositional truncation `Squash A` — quotient of `A` collapsing all inhabitants to one, used for proof-irrelevant fields.";
      signature = "mkSquash : Tm -> Tm";
    };
    mkSquashIntro = api.leaf {
      value = mkSquashIntro;
      description = "mkSquashIntro: introduction of `Squash A` — lifts any `a : A` to a single inhabitant of `Squash A`.";
      signature = "mkSquashIntro : Tm -> Tm";
    };
    mkSquashElim = api.leaf {
      value = mkSquashElim;
      description = "mkSquashElim: eliminator for `Squash` restricted to `Squash`-typed motives — preserves proof irrelevance by forbidding motives that distinguish inhabitants.";
      signature = "mkSquashElim : Tm -> Tm -> Tm -> Tm -> Tm  -- A, motive, fn, scrut";
    };

    mkFunext = api.leaf {
      value = mkFunext;
      description = "mkFunext: function-extensionality axiom — given pointwise-equal `f`, `g` at every argument, produces an equality proof `Eq (Π a:A. B a) f g`.";
      signature = "mkFunext : Tm -> Tm -> Tm -> Tm -> Tm -> Tm  -- A, B, f, g, hypothesis";
    };
    funextTypeTm = api.leaf {
      value = funextTypeTm;
      description = "funextTypeTm: pre-elaborated kernel term for the funext axiom's type `∀(j,k,A,B,f,g). (∀a. Eq (B a) (f a) (g a)) -> Eq (Π a:A. B a) f g`.";
    };

    mkDesc = api.leaf {
      value = mkDesc;
      description = "mkDesc: level-zero description type `Desc I k` at index sort `I : U(0)` and universe level `k` — the levitated algebra of constructors for datatypes.";
      signature = "mkDesc : Tm -> Tm -> Tm  -- k, I";
    };
    mkDescAt = api.leaf {
      value = mkDescAt;
      description = "mkDescAt: `Desc^k I` carrying an explicit `iLev` for the universe of `I`. The kernel synthesises the desc-formation level as `U(suc (max k iLev))`.";
      signature = "mkDescAt : Tm -> Tm -> Tm -> Tm  -- iLev, k, I";
    };
    mkMu = api.leaf {
      value = mkMu;
      description = "mkMu: levitated fixpoint `μ I D i` — carrier type of values whose constructors are described by `D : Desc I k` at index `i`.";
      signature = "mkMu : Tm -> Tm -> Tm -> Tm  -- I, D, i";
    };
    mkDescCon = api.leaf {
      value = mkDescCon;
      description = "mkDescCon: constructor introduction for `μ I D i` — takes a payload typed by `interpD D (μ I D) i` and returns the corresponding `μ` value.";
      signature = "mkDescCon : Tm -> Tm -> Tm -> Tm  -- D, i, payload";
    };
    mkDescConWithCert = api.leaf {
      value = mkDescConWithCert;
      description = "mkDescConWithCert: `mkDescCon` carrying a `Squash`-truncated guard certificate — used by `fx.types.Certified` to thread refinement proofs through the kernel.";
      signature = "mkDescConWithCert : Tm -> Tm -> Tm -> Tm -> Tm  -- D, i, payload, cert";
    };
    mkDescConChain = api.leaf {
      value = mkDescConChain;
      description = "mkDescConChain: flat-form linear-chain dual of an N-deep mkDescCon. `layers` is a flat outer-first Nix-list of `{ i; heads }` records; `base = { D; i; d }` at the terminator. The consumer pass-graph (evalF, conv, extract, quote) walks the list iteratively, so libnix `forceValueDeep` depth is O(1) regardless of N. Bijective dual of the chain-form Val (`_shape == \"linearChain\"`).";
      signature = "mkDescConChain : { layers : [{i:Tm; heads:[Tm]}]; base : {D:Tm; i:Tm; d:Tm}; outerD : Tm; payloadTag : String; payloadLeft : Tm; payloadRight : Tm; } -> Tm";
    };
    mkDescInd = api.leaf {
      value = mkDescInd;
      description = "mkDescInd: levitated induction principle on `μ I D` — given a motive and step function, produces a generic recursor over the data described by `D`.";
      signature = "mkDescInd : Tm -> Tm -> Tm -> Tm -> Tm -> Tm  -- I, D, motive, step, scrut";
    };

    mkInterpD = api.leaf {
      value = mkInterpD;
      description = "mkInterpD: interpret a description `D : Desc I k` against a recursive carrier `X : I -> U(k)` at index `i`, yielding the payload type `interpD D X i`.";
      signature = "mkInterpD : Tm -> Tm -> Tm -> Tm -> Tm  -- k, I, D, X, i";
    };
    mkAllD = api.leaf {
      value = mkAllD;
      description = "mkAllD: induction-hypothesis collector `All D X P i payload` — given motive `P : (i:I) -> X i -> U(k)`, threads `P` through every recursive child in the payload.";
      signature = "mkAllD : Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm  -- k, I, D, level, X, P, i, payload";
    };
    mkEverywhereD = api.leaf {
      value = mkEverywhereD;
      description = "mkEverywhereD: payload-traversal combinator over a description — applies a per-node `f` at every recursive position, producing a derived payload of the same shape.";
      signature = "mkEverywhereD : Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm -> Tm";
    };
    mkDescDescApp = api.leaf {
      value = mkDescDescApp;
      description = "mkDescDescApp: level-zero applied form of `descDesc` — `Desc^(suc L) ⊤` whose mu-fixpoint is `Desc^L I` for `I : U(0)`; bootstraps generic programming over descriptions themselves.";
      signature = "mkDescDescApp : Tm -> Tm -> Tm  -- I, L";
    };
    mkDescDescAppAt = api.leaf {
      value = mkDescDescAppAt;
      description = "mkDescDescAppAt: applied form of `descDesc` carrying an explicit `ℓ` for the universe of `I` — generalised outer signature `λℓ:Level. λI:U(ℓ). λL:Level. Desc^(suc (max L ℓ)) ⊤`.";
      signature = "mkDescDescAppAt : Tm -> Tm -> Tm -> Tm  -- ℓ, I, L";
    };
    mkCanonApp = api.leaf {
      value = mkCanonApp;
      description = "mkCanonApp: generic identity-tagged application — `canon-app id params body` evaluates by currying-applying `body` to `params` and stamps the result `VDescCon` with `_canonRef = { id; params; }`; conv/quote short-circuit on the canonical identity instead of forcing `.D`.";
      signature = "mkCanonApp : String -> [Tm] -> Tm -> Tm  -- id, params, body";
    };

    mkU = api.leaf {
      value = mkU;
      description = "mkU: universe type `U(level)` at the given level expression — accepts either a concrete `Int` (wrapped via `mkLevelLit`) or a Level-typed `Tm`.";
      signature = "mkU : (Int | Tm) -> Tm";
    };

    mkLift = api.leaf {
      value = mkLift;
      description = "mkLift: Tarski lift `LiftAt l m A : U(m)` with `l ≤ m` — non-cumulative cross-level transport of a type at level `l` into level `m`.";
      signature = "mkLift : Tm -> Tm -> Tm -> Tm  -- l, m, A";
    };
    mkLiftIntro = api.leaf {
      value = mkLiftIntro;
      description = "mkLiftIntro: introduction of `Lift l m A` — lifts a term `a : A` at level `l` to a term at level `m`; eq witness is auto-emitted via `mkBootRefl`.";
      signature = "mkLiftIntro : Tm -> Tm -> Tm -> Tm -> Tm  -- l, m, A, a";
    };
    mkLiftElim = api.leaf {
      value = mkLiftElim;
      description = "mkLiftElim: elimination of `Lift l m A` — lowers a lifted term back to its original level; the inverse pairing with `mkLiftIntro`.";
      signature = "mkLiftElim : Tm -> Tm -> Tm -> Tm -> Tm  -- l, m, A, x";
    };

    mkLevel = api.leaf {
      value = mkLevel;
      description = "mkLevel: universe-level sort `Level : U(0)` — the type former whose inhabitants are level expressions used in `mkU`.";
    };
    mkLevelZero = api.leaf {
      value = mkLevelZero;
      description = "mkLevelZero: level-zero literal `0 : Level` — base case of `Level`'s inductive structure.";
    };
    mkLevelSuc = api.leaf {
      value = mkLevelSuc;
      description = "mkLevelSuc: successor `suc(level) : Level` — increment a Level expression by one.";
      signature = "mkLevelSuc : Tm -> Tm";
    };
    mkLevelMax = api.leaf {
      value = mkLevelMax;
      description = "mkLevelMax: pointwise max of two levels `max(l, r) : Level` — used to compute the universe of `Σ` / `Π` types whose components inhabit distinct universes.";
      signature = "mkLevelMax : Tm -> Tm -> Tm  -- l, r";
    };
    mkLevelLit = api.leaf {
      value = mkLevelLit;
      description = "mkLevelLit: concrete Level literal from an `Int` — builds `suc^n zero` as a Level term; entry point for level-polymorphism-free code.";
      signature = "mkLevelLit : Int -> Tm";
    };

    mkString = api.leaf {
      value = mkString;
      description = "mkString: axiomatised primitive type `String` — type former at U(0) inhabited by Nix string values.";
    };
    mkInt = api.leaf {
      value = mkInt;
      description = "mkInt: axiomatised primitive type `Int` — type former at U(0) inhabited by Nix integers (excludes floats).";
    };
    mkFloat = api.leaf {
      value = mkFloat;
      description = "mkFloat: axiomatised primitive type `Float` — type former at U(0) inhabited by Nix floats (excludes integers).";
    };
    mkAttrs = api.leaf {
      value = mkAttrs;
      description = "mkAttrs: axiomatised primitive type `Attrs` — type former at U(0) inhabited by any Nix attribute set, including `{}`.";
    };
    mkPath = api.leaf {
      value = mkPath;
      description = "mkPath: axiomatised primitive type `Path` — type former at U(0) inhabited by Nix path values.";
    };
    mkDerivation = api.leaf {
      value = mkDerivation;
      description = "mkDerivation: axiomatised primitive type `Derivation` — type former at U(0) inhabited by Nix derivation values (attrsets with `type = \"derivation\"`); the irreducible Nix-store-producing value category.";
    };
    mkFunction = api.leaf {
      value = mkFunction;
      description = "mkFunction: axiomatised primitive type `Function` — type former at U(0) inhabited by opaque Nix-level functions wrapped via `mkOpaqueLam`.";
    };
    mkAny = api.leaf {
      value = mkAny;
      description = "mkAny: axiomatised top primitive type `Any` — accepts every Nix value; used as the lossy-fallback kernel for approximate types.";
    };

    mkStrEq = api.leaf {
      value = mkStrEq;
      description = "mkStrEq: decidable equality on `String` literals `strEq a b : Bool` — used by indexed datatypes whose constructor selection branches on string keys.";
      signature = "mkStrEq : Tm -> Tm -> Tm  -- a, b";
    };

    mkIntLe = api.leaf {
      value = mkIntLe;
      description = "mkIntLe: host `<=` on `Int` literals `intLe a b : Bool` (parallel to `mkStrEq`). Non-symmetric — operand order preserved on a neutral spine.";
      signature = "mkIntLe : Tm -> Tm -> Tm  -- a, b";
    };
    mkIntEq = api.leaf {
      value = mkIntEq;
      description = "mkIntEq: host `==` on `Int` literals `intEq a b : Bool` (parallel to `mkStrEq`).";
      signature = "mkIntEq : Tm -> Tm -> Tm  -- a, b";
    };

    mkStringLit = api.leaf {
      value = mkStringLit;
      description = "mkStringLit: kernel literal for a Nix string `s : String`.";
      signature = "mkStringLit : String -> Tm";
    };
    mkIntLit = api.leaf {
      value = mkIntLit;
      description = "mkIntLit: kernel literal for a Nix integer `n : Int`.";
      signature = "mkIntLit : Int -> Tm";
    };
    mkFloatLit = api.leaf {
      value = mkFloatLit;
      description = "mkFloatLit: kernel literal for a Nix float `x : Float`.";
      signature = "mkFloatLit : Float -> Tm";
    };
    mkAttrsLit = api.leaf {
      value = mkAttrsLit;
      description = "mkAttrsLit: kernel literal for a Nix attribute set `a : Attrs`; the attrs are carried opaquely (no per-field validation at the kernel level).";
      signature = "mkAttrsLit : Attrs -> Tm";
    };
    mkPathLit = api.leaf {
      value = mkPathLit;
      description = "mkPathLit: kernel literal for a Nix path `p : Path`.";
      signature = "mkPathLit : Path -> Tm";
    };
    mkDerivationLit = api.leaf {
      value = mkDerivationLit;
      description = "mkDerivationLit: kernel literal for a Nix derivation `d : Derivation`; the value is carried opaquely (kernel never inspects derivation attrs).";
      signature = "mkDerivationLit : Derivation -> Tm";
    };
    mkFnLit = api.leaf {
      value = mkFnLit;
      description = "mkFnLit: kernel literal for an opaque Nix function `f : Function` — wraps the function in an `fnBox` for thunk-identity-preserving conversion.";
      signature = "mkFnLit : Function -> Tm";
    };
    mkAnyLit = api.leaf {
      value = mkAnyLit;
      description = "mkAnyLit: kernel literal for an arbitrary Nix value `v : Any` — used by approximate types whose kernel slot is `mkAny`.";
      signature = "mkAnyLit : Any -> Tm";
    };

    mkOpaqueLam = api.leaf {
      value = mkOpaqueLam;
      description = "mkOpaqueLam: lambda over an opaque Nix function — kernel never inspects or applies it; `fnBox` thunk identity preserves conv reflexivity across eval/quote rounds.";
      signature = "mkOpaqueLam : FnBox -> Tm -> Tm  -- fnBox, piType";
    };

    mkLitVal = api.leaf {
      value = mkLitVal;
      description = "mkLitVal: closed-Val splice — opaque Val carrier whose eval is identity on the carried value. O(1) Val→Tm reflection; sound iff val is closed.";
      signature = "mkLitVal : Val -> Tm";
    };

  };
}
