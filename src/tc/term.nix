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

  # -- Functions --
  mkPi = name: domain: codomain: { tag = "pi"; inherit name domain codomain; };
  mkLam = name: domain: body: { tag = "lam"; inherit name domain body; };
  mkApp = fn: arg: { tag = "app"; inherit fn arg; };

  # -- Pairs --
  mkSigma = name: fst: snd: { tag = "sigma"; inherit name fst snd; };
  mkPair = fst: snd: { tag = "pair"; inherit fst snd; };
  mkFst = pair: { tag = "fst"; inherit pair; };
  mkSnd = pair: { tag = "snd"; inherit pair; };

  # -- Natural numbers --
  mkNat = { tag = "nat"; };
  mkZero = { tag = "zero"; };
  mkSucc = pred: { tag = "succ"; inherit pred; };
  mkNatElim = motive: base: step: scrut:
    { tag = "nat-elim"; inherit motive base step scrut; };

  # -- Lists --
  mkList = elem: { tag = "list"; inherit elem; };
  mkNil = elem: { tag = "nil"; inherit elem; };
  mkCons = elem: head: tail: { tag = "cons"; inherit elem head tail; };
  mkListElim = elem: motive: nil: cons: scrut:
    { tag = "list-elim"; inherit elem motive nil cons scrut; };

  # -- Unit --
  mkUnit = { tag = "unit"; };
  mkTt = { tag = "tt"; };

  # -- Sum --
  mkSum = left: right: { tag = "sum"; inherit left right; };
  mkInl = left: right: term: { tag = "inl"; inherit left right term; };
  mkInr = left: right: term: { tag = "inr"; inherit left right term; };
  mkSumElim = left: right: motive: onLeft: onRight: scrut:
    { tag = "sum-elim"; inherit left right motive onLeft onRight scrut; };

  # -- Identity --
  mkEq = type: lhs: rhs: { tag = "eq"; inherit type lhs rhs; };
  mkRefl = { tag = "refl"; };
  mkJ = type: lhs: motive: base: rhs: eq:
    { tag = "j"; inherit type lhs motive base rhs eq; };

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
                    (mkEq
                      (mkApp (mkVar 3) (mkVar 0))
                      (mkApp (mkVar 2) (mkVar 0))
                      (mkApp (mkVar 1) (mkVar 0))))
                  (mkEq
                    (mkPi "a" (mkVar 4) (mkApp (mkVar 4) (mkVar 0)))
                    (mkVar 2)
                    (mkVar 1))))))));

  # -- Descriptions --
  # `desc^k I` carries an explicit universe level `k` (Level Tm).
  # Callers pass a Level Tm directly; integer literals must be
  # wrapped explicitly via `mkLevelLit n` (or `mkLevelZero` /
  # `mkLevelSuc mkLevelZero` for the common 0/1 cases).
  mkDesc = k: I: { tag = "desc"; inherit k I; };
  mkDescRet = j: { tag = "desc-ret"; inherit j; };
  # `arg` / `pi` carry a description level `k` and a per-summand
  # level `l`, both Level Tm. `S` inhabits `U(l)`; the bound witness
  # `eq : Eq Level (max l k) k` proves `l ≤ k`. Callers pass Level
  # Tms directly; integer literals must be wrapped explicitly. The
  # homogeneous default is `l = k` with `eq = mkRefl`.
  mkDescArg = k: l: S: eq: T: { tag = "desc-arg"; inherit k l S eq T; };
  mkDescRec = j: D: { tag = "desc-rec"; inherit j D; };
  mkDescPi = k: l: S: eq: f: D: { tag = "desc-pi"; inherit k l S eq f D; };
  mkDescPlus = A: B: { tag = "desc-plus"; inherit A B; };
  mkMu = I: D: i: { tag = "mu"; inherit I D i; };
  mkDescCon = D: i: d: { tag = "desc-con"; inherit D i d; };
  mkDescInd = D: motive: step: i: scrut:
    { tag = "desc-ind"; inherit D motive step i scrut; };
  # `descElim` carries a universe level `k` (Level Tm). Its `onArg` /
  # `onPi` cases bind their sort `S` at `U(k)`. Callers pass a Level
  # Tm directly; integer literals must be wrapped explicitly.
  mkDescElim = k: motive: onRet: onArg: onRec: onPi: onPlus: scrut: {
    tag = "desc-elim";
    inherit k motive onRet onArg onRec onPi onPlus scrut;
  };

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

  # Asymmetric Nat→Level bridge. `natToLevel n : Level` for `n : Nat`.
  # The opposite direction is intentionally absent — `Level` is
  # quantifiable but not destructible (no eliminator), so no term
  # recovers a `Nat` from a `Level`. Eval reduces structurally:
  # `natToLevel zero ≡ zero`, `natToLevel (suc n) ≡ suc (natToLevel n)`.
  mkNatToLevel = n: { tag = "nat-to-level"; inherit n; };

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
    - `mkNat`, `mkZero`, `mkSucc`, `mkNatElim` — natural numbers with eliminator
    - `mkList`, `mkNil`, `mkCons`, `mkListElim` — lists with eliminator
    - `mkUnit`, `mkTt` — unit type and value
    - `mkSum`, `mkInl`, `mkInr`, `mkSumElim` — disjoint sum with eliminator
    - `mkEq`, `mkRefl`, `mkJ` — identity type with J eliminator

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
    inherit mkVar mkLet mkAnn;
    inherit mkPi mkLam mkApp;
    inherit mkSigma mkPair mkFst mkSnd;
    inherit mkNat mkZero mkSucc mkNatElim;
    inherit mkList mkNil mkCons mkListElim;
    inherit mkUnit mkTt;
    inherit mkSum mkInl mkInr mkSumElim;
    inherit mkEq mkRefl mkJ;
    inherit mkFunext funextTypeTm;
    inherit mkDesc mkDescRet mkDescArg mkDescRec mkDescPi mkDescPlus mkMu mkDescCon mkDescInd mkDescElim;
    inherit mkU;
    inherit mkLift mkLiftIntro mkLiftElim;
    inherit mkLevel mkLevelZero mkLevelSuc mkLevelMax mkLevelLit mkNatToLevel;
    inherit mkString mkInt mkFloat mkAttrs mkPath mkFunction mkAny;
    inherit mkStrEq;
    inherit mkStringLit mkIntLit mkFloatLit mkAttrsLit mkPathLit mkFnLit mkAnyLit;
    inherit mkOpaqueLam;
  };
  tests = {
    "var-tag" = { expr = (mkVar 0).tag; expected = "var"; };
    "var-idx" = { expr = (mkVar 3).idx; expected = 3; };
    "pi-tag" = { expr = (mkPi "x" mkNat mkNat).tag; expected = "pi"; };
    "lam-tag" = { expr = (mkLam "x" mkNat (mkVar 0)).tag; expected = "lam"; };
    "app-tag" = { expr = (mkApp (mkVar 0) mkZero).tag; expected = "app"; };
    "sigma-tag" = { expr = (mkSigma "x" mkNat mkNat).tag; expected = "sigma"; };
    "pair-tag" = { expr = (mkPair mkZero mkTt).tag; expected = "pair"; };
    "fst-tag" = { expr = (mkFst (mkVar 0)).tag; expected = "fst"; };
    "snd-tag" = { expr = (mkSnd (mkVar 0)).tag; expected = "snd"; };
    "nat-tag" = { expr = mkNat.tag; expected = "nat"; };
    "zero-tag" = { expr = mkZero.tag; expected = "zero"; };
    "succ-tag" = { expr = (mkSucc mkZero).tag; expected = "succ"; };
    "succ-pred" = { expr = (mkSucc mkZero).pred.tag; expected = "zero"; };
    "nat-elim-tag" = {
      expr = (mkNatElim (mkVar 0) mkZero (mkVar 1) mkZero).tag;
      expected = "nat-elim";
    };
    "list-tag" = { expr = (mkList mkNat).tag; expected = "list"; };
    "nil-tag" = { expr = (mkNil mkNat).tag; expected = "nil"; };
    "cons-tag" = { expr = (mkCons mkNat mkZero (mkNil mkNat)).tag; expected = "cons"; };
    "unit-tag" = { expr = mkUnit.tag; expected = "unit"; };
    "tt-tag" = { expr = mkTt.tag; expected = "tt"; };
    "sum-tag" = { expr = (mkSum mkNat mkUnit).tag; expected = "sum"; };
    "inl-tag" = { expr = (mkInl mkNat mkUnit mkZero).tag; expected = "inl"; };
    "inr-tag" = { expr = (mkInr mkNat mkUnit mkTt).tag; expected = "inr"; };
    "eq-tag" = { expr = (mkEq mkNat mkZero mkZero).tag; expected = "eq"; };
    "refl-tag" = { expr = mkRefl.tag; expected = "refl"; };
    "j-tag" = {
      expr = (mkJ mkNat mkZero (mkVar 0) (mkVar 1) mkZero mkRefl).tag;
      expected = "j";
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
    "nat-to-level-tag" = { expr = (mkNatToLevel mkZero).tag; expected = "nat-to-level"; };
    "nat-to-level-n" = { expr = (mkNatToLevel mkZero).n.tag; expected = "zero"; };
    "let-tag" = { expr = (mkLet "x" mkNat mkZero (mkVar 0)).tag; expected = "let"; };
    "ann-tag" = { expr = (mkAnn mkZero mkNat).tag; expected = "ann"; };
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
    "opaque-lam-tag" = { expr = (mkOpaqueLam { _fn = (x: x); } mkNat).tag; expected = "opaque-lam"; };
    "opaque-lam-piTy" = { expr = (mkOpaqueLam { _fn = (x: x); } mkNat).piTy.tag; expected = "nat"; };
    "opaque-lam-fnBox" = { expr = (mkOpaqueLam { _fn = (x: x); } mkNat)._fnBox ? _fn; expected = true; };

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
    "desc-ret-tag" = { expr = (mkDescRet mkTt).tag; expected = "desc-ret"; };
    "desc-ret-j" = { expr = (mkDescRet mkTt).j.tag; expected = "tt"; };
    "desc-arg-tag" = { expr = (mkDescArg mkLevelZero mkLevelZero mkNat mkRefl (mkDescRet mkTt)).tag; expected = "desc-arg"; };
    "desc-arg-S" = { expr = (mkDescArg mkLevelZero mkLevelZero mkNat mkRefl (mkDescRet mkTt)).S.tag; expected = "nat"; };
    "desc-arg-k-zero" = {
      expr = (mkDescArg mkLevelZero mkLevelZero mkNat mkRefl (mkDescRet mkTt)).k.tag;
      expected = "level-zero";
    };
    "desc-arg-k-suc" = {
      expr = (mkDescArg (mkLevelSuc mkLevelZero) (mkLevelSuc mkLevelZero) mkNat mkRefl (mkDescRet mkTt)).k.tag;
      expected = "level-suc";
    };
    "desc-arg-k-max" = {
      expr = (mkDescArg (mkLevelMax mkLevelZero mkLevelZero)
              (mkLevelMax mkLevelZero mkLevelZero)
              mkNat mkRefl (mkDescRet mkTt)).k.tag;
      expected = "level-max";
    };
    "desc-arg-l-zero" = {
      expr = (mkDescArg mkLevelZero mkLevelZero mkNat mkRefl (mkDescRet mkTt)).l.tag;
      expected = "level-zero";
    };
    "desc-arg-eq-refl" = {
      expr = (mkDescArg mkLevelZero mkLevelZero mkNat mkRefl (mkDescRet mkTt)).eq.tag;
      expected = "refl";
    };
    "desc-rec-tag" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).tag; expected = "desc-rec"; };
    "desc-rec-j" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).j.tag; expected = "tt"; };
    "desc-rec-D" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).D.tag; expected = "desc-ret"; };
    "desc-pi-tag" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).tag;
      expected = "desc-pi";
    };
    "desc-pi-S" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).S.tag;
      expected = "nat";
    };
    "desc-pi-f" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).f.tag;
      expected = "lam";
    };
    "desc-pi-D" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).D.tag;
      expected = "desc-ret";
    };
    "desc-pi-k-zero" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).k.tag;
      expected = "level-zero";
    };
    "desc-pi-k-suc" = {
      expr = (mkDescPi (mkLevelSuc mkLevelZero) (mkLevelSuc mkLevelZero) mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).k.tag;
      expected = "level-suc";
    };
    "desc-pi-l-zero" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).l.tag;
      expected = "level-zero";
    };
    "desc-pi-eq-refl" = {
      expr = (mkDescPi mkLevelZero mkLevelZero mkNat mkRefl (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).eq.tag;
      expected = "refl";
    };
    "mu-tag" = { expr = (mkMu mkUnit (mkDescRet mkTt) mkTt).tag; expected = "mu"; };
    "mu-I" = { expr = (mkMu mkUnit (mkDescRet mkTt) mkTt).I.tag; expected = "unit"; };
    "mu-D" = { expr = (mkMu mkUnit (mkDescRet mkTt) mkTt).D.tag; expected = "desc-ret"; };
    "mu-i" = { expr = (mkMu mkUnit (mkDescRet mkTt) mkTt).i.tag; expected = "tt"; };
    "desc-con-tag" = {
      expr = (mkDescCon (mkDescRet mkTt) mkTt mkRefl).tag;
      expected = "desc-con";
    };
    "desc-con-D" = {
      expr = (mkDescCon (mkDescRet mkTt) mkTt mkRefl).D.tag;
      expected = "desc-ret";
    };
    "desc-con-i" = {
      expr = (mkDescCon (mkDescRet mkTt) mkTt mkRefl).i.tag;
      expected = "tt";
    };
    "desc-ind-tag" = {
      expr = (mkDescInd (mkDescRet mkTt) (mkVar 0) (mkVar 1) mkTt (mkVar 2)).tag;
      expected = "desc-ind";
    };
    "desc-ind-i" = {
      expr = (mkDescInd (mkDescRet mkTt) (mkVar 0) (mkVar 1) mkTt (mkVar 2)).i.tag;
      expected = "tt";
    };
    "desc-elim-tag" = {
      expr = (mkDescElim mkLevelZero (mkVar 0) (mkVar 1) (mkVar 2) (mkVar 3) (mkVar 4) (mkVar 5) (mkDescRet mkTt)).tag;
      expected = "desc-elim";
    };
    "desc-elim-scrut" = {
      expr = (mkDescElim mkLevelZero (mkVar 0) (mkVar 1) (mkVar 2) (mkVar 3) (mkVar 4) (mkVar 5) (mkDescRet mkTt)).scrut.tag;
      expected = "desc-ret";
    };
    "desc-elim-k-zero" = {
      expr = (mkDescElim mkLevelZero (mkVar 0) (mkVar 1) (mkVar 2) (mkVar 3) (mkVar 4) (mkVar 5) (mkDescRet mkTt)).k.tag;
      expected = "level-zero";
    };
    "desc-plus-tag" = {
      expr = (mkDescPlus (mkDescRet mkTt) (mkDescRet mkTt)).tag;
      expected = "desc-plus";
    };
    "desc-plus-A" = {
      expr = (mkDescPlus (mkDescRet mkTt) (mkDescRet mkTt)).A.tag;
      expected = "desc-ret";
    };
    "desc-plus-B" = {
      expr = (mkDescPlus (mkDescRet mkTt) (mkDescRet mkTt)).B.tag;
      expected = "desc-ret";
    };

    # Lift primitive
    "lift-tag" = { expr = (mkLift mkLevelZero mkLevelZero mkRefl mkUnit).tag; expected = "lift"; };
    "lift-l-zero" = {
      expr = (mkLift mkLevelZero mkLevelZero mkRefl mkUnit).l.tag;
      expected = "level-zero";
    };
    "lift-m-suc" = {
      expr = (mkLift mkLevelZero (mkLevelSuc mkLevelZero) mkRefl mkUnit).m.tag;
      expected = "level-suc";
    };
    "lift-A" = { expr = (mkLift mkLevelZero mkLevelZero mkRefl mkUnit).A.tag; expected = "unit"; };
    "lift-eq-refl" = { expr = (mkLift mkLevelZero mkLevelZero mkRefl mkUnit).eq.tag; expected = "refl"; };
    "lift-intro-tag" = {
      expr = (mkLiftIntro mkLevelZero mkLevelZero mkRefl mkUnit mkTt).tag;
      expected = "lift-intro";
    };
    "lift-intro-a" = {
      expr = (mkLiftIntro mkLevelZero mkLevelZero mkRefl mkUnit mkTt).a.tag;
      expected = "tt";
    };
    "lift-elim-tag" = {
      expr = (mkLiftElim mkLevelZero mkLevelZero mkRefl mkUnit (mkVar 0)).tag;
      expected = "lift-elim";
    };
    "lift-elim-x" = {
      expr = (mkLiftElim mkLevelZero mkLevelZero mkRefl mkUnit (mkVar 0)).x.tag;
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
      expected = "eq";
    };
  };
}
