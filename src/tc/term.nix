# Type-checking kernel: Term constructors (Tm)
#
# Core term language with de Bruijn indices. All binding uses indices.
# Name annotations are cosmetic (for error messages only).
# Uses `tag` (not `_tag`) to distinguish from effect system nodes.
#
# Spec reference: kernel-spec.md §2
{ api, ... }:

let
  inherit (api) mk;

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
  mkSquash      = A:          { tag = "squash";       inherit A; };
  mkSquashIntro = a:          { tag = "squash-intro"; inherit a; };
  mkSquashElim  = A: B: f: x: { tag = "squash-elim";  inherit A B f x; };

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
  mkDesc = k: I: { tag = "desc"; inherit k I; };
  mkMu = I: D: i: { tag = "mu"; inherit I D i; };
  mkDescCon = D: i: d: { tag = "desc-con"; inherit D i d; };
  mkDescConWithCert = D: i: d: cert:
    { tag = "desc-con"; inherit D i d; _descConCert = cert; };
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

  # `descDescApp I L : μ⊤(descDesc ⊤ (suc L)) tt` — identity-tagged
  # invocation of `descDesc` at parameters `(I, L)`. The eval rule
  # stamps `_canonRef = { id = "descDesc"; I; L; }` on the outer
  # VDescCon so conv and quote can short-circuit on the tag.
  mkDescDescApp = I: L: { tag = "desc-desc-app"; inherit I L; };

  # -- Lift primitive --
  # Tarski + non-cumulative cross-level transport. `Lift l m eq A : U(m)`
  # is the type of values transported from `A : U(l)` up to `U(m)`,
  # given a bound witness `eq : Eq Level (max l m) m` proving `l ≤ m`
  # decidably via `convLevel`. Conv collapses `Lift l l _ A ≡ A`
  # (idempotent at equal levels), `lower _ (lift _ a) ≡ a` (β),
  # `lift _ (lower _ x) ≡ x` (η), composition of nested Lifts. The
  # `eq` slot is witness-irrelevant: two Lifts with matching levels and
  # underlying type are conv-equal regardless of the proof carried.
  mkLift      = l: m: eq: A:    { tag = "lift";       inherit l m eq A; };
  mkLiftIntro = l: m: eq: A: a: { tag = "lift-intro"; inherit l m eq A a; };
  mkLiftElim  = l: m: eq: A: x: { tag = "lift-elim";  inherit l m eq A x; };

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
  mkFunction = { tag = "function"; };
  mkAny = { tag = "any"; };

  # -- String operations --
  mkStrEq = lhs: rhs: { tag = "str-eq"; inherit lhs rhs; };

  # -- Primitive literals --
  mkStringLit = s: { tag = "string-lit"; value = s; };
  mkIntLit = n: { tag = "int-lit"; value = n; };
  mkFloatLit = f: { tag = "float-lit"; value = f; };
  mkAttrsLit = { tag = "attrs-lit"; };
  mkPathLit = { tag = "path-lit"; };
  mkFnLit = { tag = "fn-lit"; };
  mkAnyLit = { tag = "any-lit"; };

  # Opaque lambda: trust boundary for negative types (Pi).
  # Carries a Nix function opaquely — the kernel never inspects or applies it.
  # fnBox is a { _fn = nixFn; } attrset created once at the HOAS level and
  # propagated as-is through eval/quote/check. Nix attrset == uses thunk
  # identity for function-valued fields, so preserving the same fnBox object
  # ensures conv reflexivity. Direct function == always returns false.
  mkOpaqueLam = fnBox: piTy: { tag = "opaque-lam"; _fnBox = fnBox; inherit piTy; };

in mk {
  doc = ''
    # fx.tc.term — Core Term Constructors (Tm)

    Syntax of the kernel's term language. All 48 constructors produce
    attrsets with a `tag` field (not `_tag`, to distinguish kernel terms
    from effect system nodes). Binding is de Bruijn indexed: `mkVar i`
    refers to the i-th enclosing binder (0 = innermost).

    Name annotations (`name` parameter on `mkPi`, `mkLam`, `mkSigma`,
    `mkLet`) are cosmetic — used only in error messages, never in
    equality checking.

    Spec reference: kernel-spec.md §2.

    ## Constructors

    ### Variables and Binding
    - `mkVar : Int → Tm` — variable by de Bruijn index
    - `mkLet : String → Tm → Tm → Tm → Tm` — `let name : type = val in body`
    - `mkAnn : Tm → Tm → Tm` — type annotation `(term : type)`

    ### Functions (§2.2)
    - `mkPi : String → Tm → Tm → Tm` — dependent function type `Π(name : domain). codomain`
    - `mkLam : String → Tm → Tm → Tm` — lambda `λ(name : domain). body`
    - `mkApp : Tm → Tm → Tm` — application `fn arg`

    ### Pairs (§2.3)
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

    ### Axiomatized Primitives (§2.1)
    - `mkString`, `mkInt`, `mkFloat`, `mkAttrs`, `mkPath`, `mkFunction`, `mkAny` — type formers
    - `mkStringLit`, `mkIntLit`, `mkFloatLit`, `mkAttrsLit`, `mkPathLit`, `mkFnLit`, `mkAnyLit` — literal values
  '';
  value = {
    inherit mkVar mkLet mkAnn mkAnnTrusted mkAnnTrustedWithDescRef;
    inherit mkPi mkLam mkApp;
    inherit mkSigma mkPair mkFst mkSnd;
    inherit mkUnit mkTt;
    inherit mkBootSum mkBootInl mkBootInr mkBootSumElim;
    inherit mkBootEq mkBootRefl mkBootJ;
    inherit mkSquash mkSquashIntro mkSquashElim;
    inherit mkFunext funextTypeTm;
    inherit mkDesc mkMu mkDescCon mkDescConWithCert mkDescInd;
    inherit mkInterpD mkAllD mkEverywhereD mkDescDescApp;
    inherit mkU;
    inherit mkLift mkLiftIntro mkLiftElim;
    inherit mkLevel mkLevelZero mkLevelSuc mkLevelMax mkLevelLit;
    inherit mkString mkInt mkFloat mkAttrs mkPath mkFunction mkAny;
    inherit mkStrEq;
    inherit mkStringLit mkIntLit mkFloatLit mkAttrsLit mkPathLit mkFnLit mkAnyLit;
    inherit mkOpaqueLam;
  };
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
                (mkVar 0) (mkVar 1) mkTt mkBootRefl).tag;
      expected = "all-d";
    };
    "all-d-K" = {
      expr = (mkAllD mkLevelZero mkUnit (mkVar 0) (mkLevelSuc mkLevelZero)
                (mkVar 0) (mkVar 1) mkTt mkBootRefl).K.tag;
      expected = "level-suc";
    };
    "all-d-d" = {
      expr = (mkAllD mkLevelZero mkUnit (mkVar 0) mkLevelZero
                (mkVar 0) (mkVar 1) mkTt mkBootRefl).d.tag;
      expected = "boot-refl";
    };
    "everywhere-d-tag" = {
      expr = (mkEverywhereD mkLevelZero mkUnit (mkVar 0) mkLevelZero
                (mkVar 0) (mkVar 1) (mkVar 2) mkTt mkBootRefl).tag;
      expected = "everywhere-d";
    };
    "everywhere-d-ih" = {
      expr = (mkEverywhereD mkLevelZero mkUnit (mkVar 0) mkLevelZero
                (mkVar 0) (mkVar 1) (mkVar 7) mkTt mkBootRefl).ih.idx;
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
      expr = funextTypeTm
        .codomain   # after j
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
}
