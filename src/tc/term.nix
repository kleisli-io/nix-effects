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
  # Atomic constant whose type is the closed 5-layer Π chain
  # `funextTypeTm` below. No reduction rule; inhabits
  # `Eq (Π(a:A). B a) f g` given a pointwise-equality witness.
  mkFunext = { tag = "funext"; };

  # Closed Π chain serving as the type of `funext` at universe 0.
  # Equivalent to:
  #   Π(A : U 0).
  #   Π(B : A → U 0).
  #   Π(f : Π(a:A). B a).
  #   Π(g : Π(a:A). B a).
  #   Π(_ : Π(a:A). Eq (B a) (f a) (g a)).
  #     Eq (Π(a:A). B a) f g
  # De Bruijn depths — at the Pi-body introducing binder k (k = 0..4):
  #   k=0 (A bound): A=0.
  #   k=1 (B bound): B=0, A=1.
  #   k=2 (f bound): f=0, B=1, A=2.
  #   k=3 (g bound): g=0, f=1, B=2, A=3.
  #   k=4 (hyp bound): hyp=0, g=1, f=2, B=3, A=4.
  # The innermost Eq type `Π(a:A). B a` opens another a-binder, under
  # which a=0 and every outer var shifts by 1.
  funextTypeTm =
    mkPi "A" (mkU 0)
      (mkPi "B" (mkPi "_" (mkVar 0) (mkU 0))
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
                (mkVar 1))))));

  # -- Descriptions --
  mkDesc = I: { tag = "desc"; inherit I; };
  mkDescRet = j: { tag = "desc-ret"; inherit j; };
  mkDescArg = S: T: { tag = "desc-arg"; inherit S T; };
  mkDescRec = j: D: { tag = "desc-rec"; inherit j D; };
  mkDescPi = S: f: D: { tag = "desc-pi"; inherit S f D; };
  mkDescPlus = A: B: { tag = "desc-plus"; inherit A B; };
  mkMu = I: D: i: { tag = "mu"; inherit I D i; };
  mkDescCon = D: i: d: { tag = "desc-con"; inherit D i d; };
  mkDescInd = D: motive: step: i: scrut:
    { tag = "desc-ind"; inherit D motive step i scrut; };
  mkDescElim = motive: onRet: onArg: onRec: onPi: onPlus: scrut:
    { tag = "desc-elim"; inherit motive onRet onArg onRec onPi onPlus scrut; };

  # -- Universes --
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
    - `mkU : Int → Tm` — universe at level i

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
    "U-tag" = { expr = (mkU 0).tag; expected = "U"; };
    "U-level" = { expr = (mkU 1).level; expected = 1; };
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
    "desc-tag" = { expr = (mkDesc mkUnit).tag; expected = "desc"; };
    "desc-I" = { expr = (mkDesc mkUnit).I.tag; expected = "unit"; };
    "desc-ret-tag" = { expr = (mkDescRet mkTt).tag; expected = "desc-ret"; };
    "desc-ret-j" = { expr = (mkDescRet mkTt).j.tag; expected = "tt"; };
    "desc-arg-tag" = { expr = (mkDescArg mkNat (mkDescRet mkTt)).tag; expected = "desc-arg"; };
    "desc-arg-S" = { expr = (mkDescArg mkNat (mkDescRet mkTt)).S.tag; expected = "nat"; };
    "desc-rec-tag" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).tag; expected = "desc-rec"; };
    "desc-rec-j" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).j.tag; expected = "tt"; };
    "desc-rec-D" = { expr = (mkDescRec mkTt (mkDescRet mkTt)).D.tag; expected = "desc-ret"; };
    "desc-pi-tag" = {
      expr = (mkDescPi mkNat (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).tag;
      expected = "desc-pi";
    };
    "desc-pi-S" = {
      expr = (mkDescPi mkNat (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).S.tag;
      expected = "nat";
    };
    "desc-pi-f" = {
      expr = (mkDescPi mkNat (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).f.tag;
      expected = "lam";
    };
    "desc-pi-D" = {
      expr = (mkDescPi mkNat (mkLam "_" mkNat mkTt) (mkDescRet mkTt)).D.tag;
      expected = "desc-ret";
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
      expr = (mkDescElim (mkVar 0) (mkVar 1) (mkVar 2) (mkVar 3) (mkVar 4) (mkVar 5) (mkDescRet mkTt)).tag;
      expected = "desc-elim";
    };
    "desc-elim-scrut" = {
      expr = (mkDescElim (mkVar 0) (mkVar 1) (mkVar 2) (mkVar 3) (mkVar 4) (mkVar 5) (mkDescRet mkTt)).scrut.tag;
      expected = "desc-ret";
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

    # Function extensionality postulate
    "funext-tag" = { expr = mkFunext.tag; expected = "funext"; };
    "funext-type-tag" = { expr = funextTypeTm.tag; expected = "pi"; };
    "funext-type-outer-name" = { expr = funextTypeTm.name; expected = "A"; };
    "funext-type-outer-domain-tag" = { expr = funextTypeTm.domain.tag; expected = "U"; };
    "funext-type-outer-domain-level" = { expr = funextTypeTm.domain.level; expected = 0; };
    "funext-type-b-domain-is-pi" = {
      expr = funextTypeTm.codomain.domain.tag;
      expected = "pi";
    };
    "funext-type-innermost-eq" = {
      # Walk into: A → B → f → g → hyp → body.
      # Body should be an Eq of (Pi a:A. B a) f g.
      expr = funextTypeTm
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
