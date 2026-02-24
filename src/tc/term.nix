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
  mkPair = fst: snd: ann: { tag = "pair"; inherit fst snd ann; };
  mkFst = pair: { tag = "fst"; inherit pair; };
  mkSnd = pair: { tag = "snd"; inherit pair; };

  # -- Natural numbers --
  mkNat = { tag = "nat"; };
  mkZero = { tag = "zero"; };
  mkSucc = pred: { tag = "succ"; inherit pred; };
  mkNatElim = motive: base: step: scrut:
    { tag = "nat-elim"; inherit motive base step scrut; };

  # -- Booleans --
  mkBool = { tag = "bool"; };
  mkTrue = { tag = "true"; };
  mkFalse = { tag = "false"; };
  mkBoolElim = motive: onTrue: onFalse: scrut:
    { tag = "bool-elim"; inherit motive onTrue onFalse scrut; };

  # -- Lists --
  mkList = elem: { tag = "list"; inherit elem; };
  mkNil = elem: { tag = "nil"; inherit elem; };
  mkCons = elem: head: tail: { tag = "cons"; inherit elem head tail; };
  mkListElim = elem: motive: nil: cons: scrut:
    { tag = "list-elim"; inherit elem motive nil cons scrut; };

  # -- Unit --
  mkUnit = { tag = "unit"; };
  mkTt = { tag = "tt"; };

  # -- Void --
  mkVoid = { tag = "void"; };
  mkAbsurd = type: term: { tag = "absurd"; inherit type term; };

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
    - `mkPair : Tm → Tm → Tm → Tm` — pair constructor `(fst, snd) : ann`
    - `mkFst : Tm → Tm` — first projection
    - `mkSnd : Tm → Tm` — second projection

    ### Inductive Types
    - `mkNat`, `mkZero`, `mkSucc`, `mkNatElim` — natural numbers with eliminator
    - `mkBool`, `mkTrue`, `mkFalse`, `mkBoolElim` — booleans with eliminator
    - `mkList`, `mkNil`, `mkCons`, `mkListElim` — lists with eliminator
    - `mkUnit`, `mkTt` — unit type and value
    - `mkVoid`, `mkAbsurd` — empty type and ex falso
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
    inherit mkBool mkTrue mkFalse mkBoolElim;
    inherit mkList mkNil mkCons mkListElim;
    inherit mkUnit mkTt;
    inherit mkVoid mkAbsurd;
    inherit mkSum mkInl mkInr mkSumElim;
    inherit mkEq mkRefl mkJ;
    inherit mkU;
    inherit mkString mkInt mkFloat mkAttrs mkPath mkFunction mkAny;
    inherit mkStrEq;
    inherit mkStringLit mkIntLit mkFloatLit mkAttrsLit mkPathLit mkFnLit mkAnyLit;
  };
  tests = {
    "var-tag" = { expr = (mkVar 0).tag; expected = "var"; };
    "var-idx" = { expr = (mkVar 3).idx; expected = 3; };
    "pi-tag" = { expr = (mkPi "x" mkNat mkNat).tag; expected = "pi"; };
    "lam-tag" = { expr = (mkLam "x" mkNat (mkVar 0)).tag; expected = "lam"; };
    "app-tag" = { expr = (mkApp (mkVar 0) mkZero).tag; expected = "app"; };
    "sigma-tag" = { expr = (mkSigma "x" mkNat mkBool).tag; expected = "sigma"; };
    "pair-tag" = { expr = (mkPair mkZero mkTrue mkNat).tag; expected = "pair"; };
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
    "bool-tag" = { expr = mkBool.tag; expected = "bool"; };
    "true-tag" = { expr = mkTrue.tag; expected = "true"; };
    "false-tag" = { expr = mkFalse.tag; expected = "false"; };
    "list-tag" = { expr = (mkList mkNat).tag; expected = "list"; };
    "nil-tag" = { expr = (mkNil mkNat).tag; expected = "nil"; };
    "cons-tag" = { expr = (mkCons mkNat mkZero (mkNil mkNat)).tag; expected = "cons"; };
    "unit-tag" = { expr = mkUnit.tag; expected = "unit"; };
    "tt-tag" = { expr = mkTt.tag; expected = "tt"; };
    "void-tag" = { expr = mkVoid.tag; expected = "void"; };
    "absurd-tag" = { expr = (mkAbsurd mkNat (mkVar 0)).tag; expected = "absurd"; };
    "sum-tag" = { expr = (mkSum mkNat mkBool).tag; expected = "sum"; };
    "inl-tag" = { expr = (mkInl mkNat mkBool mkZero).tag; expected = "inl"; };
    "inr-tag" = { expr = (mkInr mkNat mkBool mkTrue).tag; expected = "inr"; };
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
  };
}
