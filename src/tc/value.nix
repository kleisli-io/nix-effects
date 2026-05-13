# Type-checking kernel: Value constructors (Val)
#
# Values are the result of evaluation. They use de Bruijn levels
# (counting outward from top of context) instead of indices.
# Closures are defunctionalized: { env, body } — no Nix lambdas in TCB.
# Neutrals use spine representation: { tag, level, spine }.
#
# Spec reference: kernel-spec.md §3
{ api, ... }:

let
  inherit (api) mk;

  # -- Closures --
  mkClosure = env: body: { inherit env body; };

  # Instantiate: eval(env ++ [arg], body) — caller provides eval function
  # This module only defines the data; eval.nix provides instantiation.

  # -- Value constructors --

  # Functions
  vLam = name: domain: closure: { tag = "VLam"; inherit name domain closure; };
  vPi = name: domain: closure: { tag = "VPi"; inherit name domain closure; };

  # Pairs
  vSigma = name: fst: closure: { tag = "VSigma"; inherit name fst closure; };
  vPair = fst: snd: { tag = "VPair"; inherit fst snd; };

  # Unit
  vUnit = { tag = "VUnit"; };
  vTt = { tag = "VTt"; };

  # Bootstrap coproduct
  vBootSum = left: right: { tag = "VBootSum"; inherit left right; };
  vBootInl = left: right: val: { tag = "VBootInl"; inherit left right val; };
  vBootInr = left: right: val: { tag = "VBootInr"; inherit left right val; };

  # Identity
  vBootEq = type: lhs: rhs: { tag = "VBootEq"; inherit type lhs rhs; };
  vBootRefl = { tag = "VBootRefl"; };

  # Propositional truncation. `Squash A : U(l)` for `A : U(l)`. Any two
  # inhabitants of `Squash A` are conv-equal — proof irrelevance is
  # definitional. Lives at the same universe as `A`; no separate SProp
  # sort. The `recTrunc` eliminator's motive is restricted to
  # `Squash`-typed targets so irrelevance does not leak into observable
  # positions.
  vSquash      = A: { tag = "VSquash";      inherit A; };
  vSquashIntro = a: { tag = "VSquashIntro"; inherit a; };

  # Function extensionality postulate — zero-payload atomic value.
  vFunext = { tag = "VFunext"; };

  # Descriptions
  # `desc^level I` carries an explicit universe level. The level is
  # `vLevelZero` for the prelude (no high-universe contents); higher
  # levels appear when encoded descriptions quantify over sorts at
  # strictly positive universes. Int-shim mirrors `vU`.
  vDesc = level: I: { tag = "VDesc"; inherit level I; };
  vMu = I: D: i: { tag = "VMu"; inherit I D i; };            # μ D i — the type at index i : I
  vDescCon = D: i: d: { tag = "VDescCon"; inherit D i d; };  # target index i carried alongside payload
  # Tagged variant of `vDescCon`. `_canonRef = { id; I; L }` stamps a
  # canonical identity on the outer VDescCon. Conv and quote
  # short-circuit on the tag instead of forcing `.D`, breaking the
  # universe-level descent that would otherwise loop when `descDesc`'s
  # own body encodes through itself.
  vDescConTagged = D: i: d: ref:
    { tag = "VDescCon"; inherit D i d; _canonRef = ref; };

  # `interpD` / `allD` / `everywhereD` — kernel-primitive interpretation
  # / All-witness / everywhere-recursion over Desc. Carry the same slots
  # as their Tm counterparts (mirroring `mkInterpD`/`mkAllD`/
  # `mkEverywhereD` in `term.nix`). Value-level reduction lives in
  # `eval/desc.nix`; these constructors are surface-form only — canonical
  # reductions return a different Val (Σ/Sum/Eq/Lift) per the on-cases,
  # never these tags themselves. They appear quoted only via the
  # corresponding `eInterpD`/`eAllD`/`eEverywhereD` spine frames on a
  # neutral D scrutinee.
  vInterpD = level: I: D: X: i:
    { tag = "VInterpD"; inherit level I D X i; };
  vAllD = level: I: D: K: X: M: i: d:
    { tag = "VAllD"; inherit level I D K X M i d; };
  vEverywhereD = level: I: D: K: X: M: ih: i: d:
    { tag = "VEverywhereD"; inherit level I D K X M ih i d; };

  # Lift primitive. `Lift l m eq A : U(m)` carries the bound witness
  # `eq : Eq Level (max l m) m` that proves `l ≤ m`. Conv collapses
  # `Lift l l _ A ≡ A`, `lower _ (lift _ a) ≡ a` (β), `lift _ (lower _
  # x) ≡ x` (η), and nested-Lift composition. The `eq` slot is
  # witness-irrelevant — two `vLift`s with matching `l`/`m`/`A` are
  # conv-equal regardless of the proof carried.
  vLift      = l: m: eq: A:    { tag = "VLift";      inherit l m eq A; };
  vLiftIntro = l: m: eq: A: a: { tag = "VLiftIntro"; inherit l m eq A a; };

  # Level sort (Tarski). `Level : U(0)`. Expressions built from
  # zero/suc/max; canonicalised at conv time.
  vLevel = { tag = "VLevel"; };
  vLevelZero = { tag = "VLevelZero"; };
  vLevelSuc = pred: { tag = "VLevelSuc"; inherit pred; };
  vLevelMax = lhs: rhs: { tag = "VLevelMax"; inherit lhs rhs; };

  # Concrete-level literal as a Level value.
  vLevelLit = n:
    if n <= 0 then vLevelZero
    else vLevelSuc (vLevelLit (n - 1));

  # Universes. Carries a Level value. Callers pass a Level Val
  # directly; integer literals must be wrapped explicitly via
  # `vLevelLit n` (or `vLevelZero` / `vLevelSuc vLevelZero` for the
  # common 0/1 cases).
  vU = level: { tag = "VU"; inherit level; };

  # Axiomatized primitives
  vString = { tag = "VString"; };
  vInt = { tag = "VInt"; };
  vFloat = { tag = "VFloat"; };
  vAttrs = { tag = "VAttrs"; };
  vPath = { tag = "VPath"; };
  vFunction = { tag = "VFunction"; };
  vAny = { tag = "VAny"; };

  # Primitive literals
  vStringLit = s: { tag = "VStringLit"; value = s; };
  vIntLit = n: { tag = "VIntLit"; value = n; };
  vFloatLit = f: { tag = "VFloatLit"; value = f; };
  vAttrsLit = { tag = "VAttrsLit"; };
  vPathLit = { tag = "VPathLit"; };
  vFnLit = { tag = "VFnLit"; };
  vAnyLit = { tag = "VAnyLit"; };

  # Opaque lambda value: axiomatized trust boundary for Pi.
  # fnBox is the { _fn = nixFn; } wrapper propagated from the HOAS level —
  # never reconstructed, preserving thunk identity for conv.
  # nixFn derived from fnBox for extractInner access. piTy is the evaluated VPi.
  vOpaqueLam = fnBox: piTy: { tag = "VOpaqueLam"; _fnBox = fnBox; nixFn = fnBox._fn; inherit piTy; };

  # -- Neutrals (stuck computations) --
  # A neutral is a variable (identified by level) applied to a spine of eliminators.
  vNe = level: spine: { tag = "VNe"; inherit level spine; };

  # Fresh variable at depth d: neutral with empty spine
  freshVar = depth: vNe depth [];

  # -- Elimination frames (spine entries) --
  eApp = arg: { tag = "EApp"; inherit arg; };
  eFst = { tag = "EFst"; };
  eSnd = { tag = "ESnd"; };
  eBootSumElim = left: right: motive: onLeft: onRight:
    { tag = "EBootSumElim"; inherit left right motive onLeft onRight; };
  eBootJ = type: lhs: motive: base: rhs:
    { tag = "EBootJ"; inherit type lhs motive base rhs; };
  eStrEq = arg: { tag = "EStrEq"; inherit arg; };
  eDescInd = D: motive: step: i:
    { tag = "EDescInd"; inherit D motive step i; };

  # `EInterpD` / `EAllD` / `EEverywhereD` — spine frames recording stuck
  # `interpD` / `allD` / `everywhereD` applications on a neutral D
  # scrutinee. The frame stores every slot OTHER than D (which is the
  # spine head). Quote round-trips a frame to the corresponding
  # `mkInterpD` / `mkAllD` / `mkEverywhereD` Tm. Conv compares frames
  # field-wise.
  eInterpD = level: I: X: i:
    { tag = "EInterpD"; inherit level I X i; };
  eAllD = level: I: K: X: M: i: d:
    { tag = "EAllD"; inherit level I K X M i d; };
  eEverywhereD = level: I: K: X: M: ih: i: d:
    { tag = "EEverywhereD"; inherit level I K X M ih i d; };

  # `ELiftElim` records a stuck `lower` on a neutral `Lift`-typed value.
  # The spine entry carries `l`, `m`, `eq`, `A` so a quoted spine round-
  # trips to `mkLiftElim l m eq A x`.
  eLiftElim = l: m: eq: A: { tag = "ELiftElim"; inherit l m eq A; };

  # `ESquashElim` records a stuck `recTrunc` on a neutral `Squash`-typed
  # value. Carries the motive shape (`A`, `B`) and the case function `f`
  # so a quoted spine round-trips to `mkSquashElim A B f x`.
  eSquashElim = A: B: f: { tag = "ESquashElim"; inherit A B f; };

in mk {
  doc = ''
    # fx.tc.value — Value Domain (Val)

    Values are the semantic domain produced by evaluation. They use
    de Bruijn *levels* (counting outward from the top of the context),
    not indices, which makes weakening trivial.

    Spec reference: kernel-spec.md §3.

    ## Closures

    `mkClosure : Env → Tm → Closure` — defunctionalized closure.
    No Nix lambdas in the TCB; a closure is `{ env, body }` where
    `body` is a kernel Tm evaluated by `eval.instantiate`.

    ## Value Constructors

    Each `v*` constructor mirrors a term constructor:

    - `vLam`, `vPi` — function values/types (carry name, domain, closure)
    - `vSigma`, `vPair` — pair types/values
    - `vUnit`, `vTt` — unit
    - `vBootSum`, `vBootInl`, `vBootInr` — bootstrap coproduct values
    - `vBootEq`, `vBootRefl` — identity values
    - `vU` — universe values
    - `vString`, `vInt`, `vFloat`, `vAttrs`, `vPath`, `vFunction`, `vAny` — primitive types
    - `vStringLit`, `vIntLit`, `vFloatLit`, `vAttrsLit`, `vPathLit`, `vFnLit`, `vAnyLit` — primitive literals

    ## Neutrals

    `vNe : Level → Spine → Val` — a stuck computation: a variable
    (identified by de Bruijn level) applied to a spine of eliminators.

    `freshVar : Depth → Val` — neutral with empty spine at the given depth.
    Used during type-checking to introduce fresh variables under binders.

    ## Elimination Frames (Spine Entries)

    - `eApp`, `eFst`, `eSnd` — function/pair eliminators
    - `eBootSumElim`, `eBootJ` — inductive eliminators
  '';
  value = {
    inherit mkClosure;
    inherit vLam vPi;
    inherit vSigma vPair;
    inherit vUnit vTt;
    inherit vBootSum vBootInl vBootInr;
    inherit vBootEq vBootRefl vFunext;
    inherit vSquash vSquashIntro;
    inherit vDesc vMu vDescCon vDescConTagged;
    inherit vInterpD vAllD vEverywhereD;
    inherit vU;
    inherit vLift vLiftIntro;
    inherit vLevel vLevelZero vLevelSuc vLevelMax vLevelLit;
    inherit vString vInt vFloat vAttrs vPath vFunction vAny;
    inherit vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit;
    inherit vOpaqueLam;
    inherit vNe freshVar;
    inherit eApp eFst eSnd eBootSumElim eBootJ eStrEq eDescInd eLiftElim;
    inherit eInterpD eAllD eEverywhereD;
    inherit eSquashElim;
  };
  tests = {
    # Closures
    "closure-env" = {
      expr = (mkClosure [ vTt ] { tag = "var"; idx = 0; }).env;
      expected = [ vTt ];
    };
    "closure-body" = {
      expr = (mkClosure [] { tag = "var"; idx = 0; }).body.tag;
      expected = "var";
    };

    # Values
    "vlam-tag" = { expr = (vLam "x" vUnit (mkClosure [] { tag = "var"; idx = 0; })).tag; expected = "VLam"; };
    "vpi-tag" = { expr = (vPi "x" vUnit (mkClosure [] { tag = "unit"; })).tag; expected = "VPi"; };
    "vsigma-tag" = { expr = (vSigma "x" vUnit (mkClosure [] { tag = "unit"; })).tag; expected = "VSigma"; };
    "vpair-tag" = { expr = (vPair vTt vTt).tag; expected = "VPair"; };
    "vunit-tag" = { expr = vUnit.tag; expected = "VUnit"; };
    "vtt-tag" = { expr = vTt.tag; expected = "VTt"; };
    "vboot-sum-tag" = { expr = (vBootSum vUnit vUnit).tag; expected = "VBootSum"; };
    "vboot-inl-tag" = { expr = (vBootInl vUnit vUnit vTt).tag; expected = "VBootInl"; };
    "vboot-inr-tag" = { expr = (vBootInr vUnit vUnit vTt).tag; expected = "VBootInr"; };
    "veq-tag" = { expr = (vBootEq vUnit vTt vTt).tag; expected = "VBootEq"; };
    "vrefl-tag" = { expr = vBootRefl.tag; expected = "VBootRefl"; };
    "vfunext-tag" = { expr = vFunext.tag; expected = "VFunext"; };
    "vsquash-tag" = { expr = (vSquash vUnit).tag; expected = "VSquash"; };
    "vsquash-A" = { expr = (vSquash vUnit).A.tag; expected = "VUnit"; };
    "vsquashintro-tag" = { expr = (vSquashIntro vTt).tag; expected = "VSquashIntro"; };
    "vsquashintro-a" = { expr = (vSquashIntro vTt).a.tag; expected = "VTt"; };
    "esquashelim-tag" = {
      expr = (eSquashElim vUnit vUnit
                (vLam "a" vUnit (mkClosure [] { tag = "tt"; }))).tag;
      expected = "ESquashElim";
    };
    "vu-tag" = { expr = (vU vLevelZero).tag; expected = "VU"; };
    "vu-level-zero" = { expr = (vU vLevelZero).level.tag; expected = "VLevelZero"; };
    "vu-level-suc" = { expr = (vU (vLevelSuc vLevelZero)).level.tag; expected = "VLevelSuc"; };
    "vu-level-suc-pred" = {
      expr = (vU (vLevelSuc vLevelZero)).level.pred.tag;
      expected = "VLevelZero";
    };
    "vu-level-max" = {
      expr = (vU (vLevelMax vLevelZero vLevelZero)).level.tag;
      expected = "VLevelMax";
    };
    "vlevel-tag" = { expr = vLevel.tag; expected = "VLevel"; };
    "vlevel-zero-tag" = { expr = vLevelZero.tag; expected = "VLevelZero"; };
    "vlevel-suc-tag" = { expr = (vLevelSuc vLevelZero).tag; expected = "VLevelSuc"; };
    "vlevel-suc-pred" = { expr = (vLevelSuc vLevelZero).pred.tag; expected = "VLevelZero"; };
    "vlevel-max-tag" = { expr = (vLevelMax vLevelZero vLevelZero).tag; expected = "VLevelMax"; };
    "vlevel-lit-0-tag" = { expr = (vLevelLit 0).tag; expected = "VLevelZero"; };
    "vlevel-lit-2-tag" = { expr = (vLevelLit 2).tag; expected = "VLevelSuc"; };
    "vstring-tag" = { expr = vString.tag; expected = "VString"; };
    "vint-tag" = { expr = vInt.tag; expected = "VInt"; };
    "vfloat-tag" = { expr = vFloat.tag; expected = "VFloat"; };
    "vattrs-tag" = { expr = vAttrs.tag; expected = "VAttrs"; };
    "vpath-tag" = { expr = vPath.tag; expected = "VPath"; };
    "vfunction-tag" = { expr = vFunction.tag; expected = "VFunction"; };
    "vany-tag" = { expr = vAny.tag; expected = "VAny"; };
    "vstringlit-tag" = { expr = (vStringLit "hi").tag; expected = "VStringLit"; };
    "vstringlit-value" = { expr = (vStringLit "hi").value; expected = "hi"; };
    "vintlit-tag" = { expr = (vIntLit 7).tag; expected = "VIntLit"; };
    "vintlit-value" = { expr = (vIntLit 7).value; expected = 7; };
    "vfloatlit-tag" = { expr = (vFloatLit 2.5).tag; expected = "VFloatLit"; };
    "vfloatlit-value" = { expr = (vFloatLit 2.5).value; expected = 2.5; };
    "vattrslit-tag" = { expr = vAttrsLit.tag; expected = "VAttrsLit"; };
    "vpathlit-tag" = { expr = vPathLit.tag; expected = "VPathLit"; };
    "vfnlit-tag" = { expr = vFnLit.tag; expected = "VFnLit"; };
    "vanylit-tag" = { expr = vAnyLit.tag; expected = "VAnyLit"; };
    "vopaquelam-tag" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).tag; expected = "VOpaqueLam"; };
    "vopaquelam-piTy" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).piTy.tag; expected = "VUnit"; };
    "vopaquelam-nixFn" = { expr = builtins.isFunction (vOpaqueLam { _fn = (x: x); } vUnit).nixFn; expected = true; };
    "vopaquelam-fnBox" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit)._fnBox ? _fn; expected = true; };

    # Neutrals
    "vne-tag" = { expr = (vNe 0 []).tag; expected = "VNe"; };
    "vne-level" = { expr = (vNe 3 []).level; expected = 3; };
    "vne-empty-spine" = { expr = (vNe 0 []).spine; expected = []; };
    "freshvar-is-neutral" = { expr = (freshVar 5).tag; expected = "VNe"; };
    "freshvar-level" = { expr = (freshVar 5).level; expected = 5; };
    "freshvar-empty-spine" = { expr = (freshVar 5).spine; expected = []; };

    # Elimination frames
    "eapp-tag" = { expr = (eApp vTt).tag; expected = "EApp"; };
    "efst-tag" = { expr = eFst.tag; expected = "EFst"; };
    "esnd-tag" = { expr = eSnd.tag; expected = "ESnd"; };
    "eboot-sum-elim-tag" = { expr = (eBootSumElim vUnit vUnit vUnit vTt vTt).tag; expected = "EBootSumElim"; };
    "ej-tag" = { expr = (eBootJ vUnit vTt vUnit vTt vTt).tag; expected = "EBootJ"; };

    # Descriptions (indexed)
    "vdesc-tag" = { expr = (vDesc vLevelZero vUnit).tag; expected = "VDesc"; };
    "vdesc-I" = { expr = (vDesc vLevelZero vUnit).I.tag; expected = "VUnit"; };
    "vdesc-level" = { expr = (vDesc vLevelZero vUnit).level.tag; expected = "VLevelZero"; };
    "vdesc-level-non-zero" = {
      expr = (vDesc (vLevelSuc vLevelZero) vUnit).level.tag;
      expected = "VLevelSuc";
    };
    "vmu-tag" = { expr = (vMu vUnit (freshVar 0) vTt).tag; expected = "VMu"; };
    "vmu-I" = { expr = (vMu vUnit (freshVar 0) vTt).I.tag; expected = "VUnit"; };
    "vmu-D" = { expr = (vMu vUnit (freshVar 0) vTt).D.tag; expected = "VNe"; };
    "vmu-i" = { expr = (vMu vUnit (freshVar 0) vTt).i.tag; expected = "VTt"; };
    "vdesccon-tag" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).tag;
      expected = "VDescCon";
    };
    "vdesccon-D" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).D.tag;
      expected = "VNe";
    };
    "vdesccon-i" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).i.tag;
      expected = "VTt";
    };
    "vdesccon-tagged-tag" = {
      expr = (vDescConTagged (freshVar 0) vTt vBootRefl
                { id = "descDesc"; I = vUnit; L = vLevelZero; }).tag;
      expected = "VDescCon";
    };
    "vdesccon-tagged-canonref-id" = {
      expr = (vDescConTagged (freshVar 0) vTt vBootRefl
                { id = "descDesc"; I = vUnit; L = vLevelZero; })._canonRef.id;
      expected = "descDesc";
    };
    "vdesccon-untagged-has-no-canonref" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl) ? _canonRef;
      expected = false;
    };
    "edescind-tag" = { expr = (eDescInd (freshVar 0) vUnit vTt vTt).tag; expected = "EDescInd"; };
    "edescind-i" = { expr = (eDescInd (freshVar 0) vUnit vTt vTt).i.tag; expected = "VTt"; };
    # Lift primitive
    "vlift-tag" = { expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).tag; expected = "VLift"; };
    "vlift-l-zero" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).l.tag;
      expected = "VLevelZero";
    };
    "vlift-m-suc" = {
      expr = (vLift vLevelZero (vLevelSuc vLevelZero) vBootRefl vUnit).m.tag;
      expected = "VLevelSuc";
    };
    "vlift-A" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).A.tag;
      expected = "VUnit";
    };
    "vlift-eq-refl" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).eq.tag;
      expected = "VBootRefl";
    };
    "vliftintro-tag" = {
      expr = (vLiftIntro vLevelZero vLevelZero vBootRefl vUnit vTt).tag;
      expected = "VLiftIntro";
    };
    "vliftintro-a" = {
      expr = (vLiftIntro vLevelZero vLevelZero vBootRefl vUnit vTt).a.tag;
      expected = "VTt";
    };
    "eliftelim-tag" = { expr = (eLiftElim vLevelZero vLevelZero vBootRefl vUnit).tag; expected = "ELiftElim"; };
    "eliftelim-l" = { expr = (eLiftElim vLevelZero vLevelZero vBootRefl vUnit).l.tag; expected = "VLevelZero"; };
    # interpD / allD / everywhereD value forms
    "vinterpd-tag" = {
      expr = (vInterpD vLevelZero vUnit (freshVar 0) vUnit vTt).tag;
      expected = "VInterpD";
    };
    "vinterpd-D" = {
      expr = (vInterpD vLevelZero vUnit (freshVar 0) vUnit vTt).D.tag;
      expected = "VNe";
    };
    "valld-tag" = {
      expr = (vAllD vLevelZero vUnit (freshVar 0) vLevelZero vUnit vUnit vTt vBootRefl).tag;
      expected = "VAllD";
    };
    "valld-K" = {
      expr = (vAllD vLevelZero vUnit (freshVar 0)
                (vLevelSuc vLevelZero) vUnit vUnit vTt vBootRefl).K.tag;
      expected = "VLevelSuc";
    };
    "veverywhered-tag" = {
      expr = (vEverywhereD vLevelZero vUnit (freshVar 0) vLevelZero
                vUnit vUnit vUnit vTt vBootRefl).tag;
      expected = "VEverywhereD";
    };
    "einterpd-tag" = {
      expr = (eInterpD vLevelZero vUnit vUnit vTt).tag;
      expected = "EInterpD";
    };
    "einterpd-level" = {
      expr = (eInterpD vLevelZero vUnit vUnit vTt).level.tag;
      expected = "VLevelZero";
    };
    "ealld-tag" = {
      expr = (eAllD vLevelZero vUnit vLevelZero vUnit vUnit vTt vBootRefl).tag;
      expected = "EAllD";
    };
    "eeverywhered-tag" = {
      expr = (eEverywhereD vLevelZero vUnit vLevelZero vUnit vUnit vUnit vTt vBootRefl).tag;
      expected = "EEverywhereD";
    };
  };
}
