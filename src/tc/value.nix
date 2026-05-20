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

  # Empty
  vEmpty = { tag = "VEmpty"; };

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
  vSquash = A: { tag = "VSquash";      inherit A; };
  vSquashIntro = a: { tag = "VSquashIntro"; inherit a; };

  # Function extensionality postulate — zero-payload atomic value.
  vFunext = { tag = "VFunext"; };

  # Descriptions
  # `desc^level I` carries an explicit universe level. The level is
  # `vLevelZero` for the prelude (no high-universe contents); higher
  # levels appear when encoded descriptions quantify over sorts at
  # strictly positive universes. Int-shim mirrors `vU`.
  #
  # `iLev` records the universe of `I` (the index sort). Defaults to
  # `vLevelZero` for the ⊤-slice prelude (`I = Unit : U(0)`). The
  # `vDesc ↔ vMu` conv unfolding at `tc/conv.nix:306-317` reads `iLev`
  # to construct `expectedD = mkDescDescAppV iLev I level`; conv has no
  # `typeOf` access, so `iLev` must travel on VDesc itself.
  vDescAt = level: iLev: I: { tag = "VDesc"; inherit level I iLev; };
  vDesc = level: I: vDescAt level vLevelZero I;
  vMu = I: D: i: { tag = "VMu"; inherit I D i; }; # μ D i — the type at index i : I
  vDescCon = D: i: d: { tag = "VDescCon"; inherit D i d; }; # target index i carried alongside payload
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
  vLift = l: m: eq: A: { tag = "VLift";      inherit l m eq A; };
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
  vDerivation = { tag = "VDerivation"; };
  vFunction = { tag = "VFunction"; };
  vAny = { tag = "VAny"; };

  # Primitive literals
  vStringLit = s: { tag = "VStringLit"; value = s; };
  vIntLit = n: { tag = "VIntLit"; value = n; };
  vFloatLit = f: { tag = "VFloatLit"; value = f; };
  vAttrsLit = { tag = "VAttrsLit"; };
  vPathLit = { tag = "VPathLit"; };
  vDerivationLit = { tag = "VDerivationLit"; };
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
  freshVar = depth: vNe depth [ ];

  # -- Elimination frames (spine entries) --
  eApp = arg: { tag = "EApp"; inherit arg; };
  eFst = { tag = "EFst"; };
  eSnd = { tag = "ESnd"; };
  eBootSumElim = left: right: motive: onLeft: onRight:
    { tag = "EBootSumElim"; inherit left right motive onLeft onRight; };
  eBootJ = type: lhs: motive: base: rhs:
    { tag = "EBootJ"; inherit type lhs motive base rhs; };
  eStrEq = arg: { tag = "EStrEq"; inherit arg; };
  eAbsurd = type: { tag = "EAbsurd"; inherit type; };
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

in
api.namespace {
  description = "fx.tc.value: semantic domain produced by evaluation; values use de Bruijn LEVELS (counting outward) so substitution under binders stays unproblematic.";
  doc = ''
    # fx.tc.value — Value Domain (Val)

    Values are the semantic domain produced by evaluation. They use
    de Bruijn *levels* (counting outward from the top of the context),
    not indices, which makes weakening trivial.

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
    - `vString`, `vInt`, `vFloat`, `vAttrs`, `vPath`, `vDerivation`, `vFunction`, `vAny` — primitive types
    - `vStringLit`, `vIntLit`, `vFloatLit`, `vAttrsLit`, `vPathLit`, `vDerivationLit`, `vFnLit`, `vAnyLit` — primitive literals

    ## Neutrals

    `vNe : Level → Spine → Val` — a stuck computation: a variable
    (identified by de Bruijn level) applied to a spine of eliminators.

    `freshVar : Depth → Val` — neutral with empty spine at the given depth.
    Used during type-checking to introduce fresh variables under binders.

    ## Elimination Frames (Spine Entries)

    - `eApp`, `eFst`, `eSnd` — function/pair eliminators
    - `eBootSumElim`, `eBootJ` — inductive eliminators
  '';
  tests = {
    # Closures
    "closure-env" = {
      expr = (mkClosure [ vTt ] { tag = "var"; idx = 0; }).env;
      expected = [ vTt ];
    };
    "closure-body" = {
      expr = (mkClosure [ ] { tag = "var"; idx = 0; }).body.tag;
      expected = "var";
    };

    # Values
    "vlam-tag" = { expr = (vLam "x" vUnit (mkClosure [ ] { tag = "var"; idx = 0; })).tag; expected = "VLam"; };
    "vpi-tag" = { expr = (vPi "x" vUnit (mkClosure [ ] { tag = "unit"; })).tag; expected = "VPi"; };
    "vsigma-tag" = { expr = (vSigma "x" vUnit (mkClosure [ ] { tag = "unit"; })).tag; expected = "VSigma"; };
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
        (vLam "a" vUnit (mkClosure [ ] { tag = "tt"; }))).tag;
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
    "vderivation-tag" = { expr = vDerivation.tag; expected = "VDerivation"; };
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
    "vderivationlit-tag" = { expr = vDerivationLit.tag; expected = "VDerivationLit"; };
    "vfnlit-tag" = { expr = vFnLit.tag; expected = "VFnLit"; };
    "vanylit-tag" = { expr = vAnyLit.tag; expected = "VAnyLit"; };
    "vopaquelam-tag" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).tag; expected = "VOpaqueLam"; };
    "vopaquelam-piTy" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).piTy.tag; expected = "VUnit"; };
    "vopaquelam-nixFn" = { expr = builtins.isFunction (vOpaqueLam { _fn = (x: x); } vUnit).nixFn; expected = true; };
    "vopaquelam-fnBox" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit)._fnBox ? _fn; expected = true; };

    # Neutrals
    "vne-tag" = { expr = (vNe 0 [ ]).tag; expected = "VNe"; };
    "vne-level" = { expr = (vNe 3 [ ]).level; expected = 3; };
    "vne-empty-spine" = { expr = (vNe 0 [ ]).spine; expected = [ ]; };
    "freshvar-is-neutral" = { expr = (freshVar 5).tag; expected = "VNe"; };
    "freshvar-level" = { expr = (freshVar 5).level; expected = 5; };
    "freshvar-empty-spine" = { expr = (freshVar 5).spine; expected = [ ]; };

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
        {
          id = "descDesc";
          params = [ vLevelZero vUnit vLevelZero ];
        }).tag;
      expected = "VDescCon";
    };
    "vdesccon-tagged-canonref-id" = {
      expr = (vDescConTagged (freshVar 0) vTt vBootRefl
        {
          id = "descDesc";
          params = [ vLevelZero vUnit vLevelZero ];
        })._canonRef.id;
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
        (vLevelSuc vLevelZero)
        vUnit
        vUnit
        vTt
        vBootRefl).K.tag;
      expected = "VLevelSuc";
    };
    "veverywhered-tag" = {
      expr = (vEverywhereD vLevelZero vUnit (freshVar 0) vLevelZero
        vUnit
        vUnit
        vUnit
        vTt
        vBootRefl).tag;
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
  value = {

    mkClosure = api.leaf {
      value = mkClosure;
      description = "mkClosure: defunctionalised closure `{ env, body }` — captures the evaluation environment and the kernel `Tm` body; instantiated by `eval.instantiate` without Nix lambdas in the TCB.";
      signature = "mkClosure : Env -> Tm -> Closure";
    };

    vLam = api.leaf {
      value = vLam;
      description = "vLam: value-domain lambda `λ(name : domain). body` — carries a defunctionalised closure rather than a Nix function, keeping the TCB Nix-lambda-free.";
      signature = "vLam : String -> Val -> Closure -> Val";
    };
    vPi = api.leaf {
      value = vPi;
      description = "vPi: value-domain dependent function type `Π(name : domain). codomain` — carries a closure for the codomain to permit semantic substitution.";
      signature = "vPi : String -> Val -> Closure -> Val";
    };

    vSigma = api.leaf {
      value = vSigma;
      description = "vSigma: value-domain dependent pair type `Σ(name : fst). snd` — carries a closure for the snd component to permit semantic substitution.";
      signature = "vSigma : String -> Val -> Closure -> Val";
    };
    vPair = api.leaf {
      value = vPair;
      description = "vPair: value-domain pair `(fst, snd)` — components held in WHNF, projected by `eFst` / `eSnd` spine frames.";
      signature = "vPair : Val -> Val -> Val";
    };

    vUnit = api.leaf {
      value = vUnit;
      description = "vUnit: value-domain unit type — terminal type with single inhabitant `vTt`; eta-converted in `conv`.";
    };
    vTt = api.leaf {
      value = vTt;
      description = "vTt: value-domain unit value `tt` — sole inhabitant of `vUnit`; conv collapses all Unit-typed values to this.";
    };
    vEmpty = api.leaf {
      value = vEmpty;
      description = "vEmpty: value-domain empty type — initial type with no inhabitants; conv-equal in one step by tag identity.";
    };

    vBootSum = api.leaf {
      value = vBootSum;
      description = "vBootSum: value-domain bootstrap coproduct type `A + B` — used by `descPlus`'s sum-of-descriptions before generic sums become available.";
      signature = "vBootSum : Val -> Val -> Val";
    };
    vBootInl = api.leaf {
      value = vBootInl;
      description = "vBootInl: value-domain left-injection `inl(a) : A + B` — carries `leftTy` and `rightTy` for elaboration shape recovery.";
      signature = "vBootInl : Val -> Val -> Val -> Val  -- leftTy, rightTy, value";
    };
    vBootInr = api.leaf {
      value = vBootInr;
      description = "vBootInr: value-domain right-injection `inr(b) : A + B` — carries `leftTy` and `rightTy` for elaboration shape recovery.";
      signature = "vBootInr : Val -> Val -> Val -> Val  -- leftTy, rightTy, value";
    };

    vBootEq = api.leaf {
      value = vBootEq;
      description = "vBootEq: value-domain bootstrap identity type `Eq(A, a, b)` — propositional equality used by `descRet`'s level transport and by the J eliminator.";
      signature = "vBootEq : Val -> Val -> Val -> Val  -- A, a, b";
    };
    vBootRefl = api.leaf {
      value = vBootRefl;
      description = "vBootRefl: value-domain reflexivity `refl : Eq(A, a, a)` — canonical inhabitant of every reflexive identity; conv collapses all proofs of refl to this.";
    };
    vFunext = api.leaf {
      value = vFunext;
      description = "vFunext: value-domain funext axiom — given pointwise equality, produces equality of functions at `Π(a:A). B a`.";
      signature = "vFunext : Val -> Val -> Val -> Val -> Val -> Val";
    };

    vSquash = api.leaf {
      value = vSquash;
      description = "vSquash: value-domain propositional truncation `Squash A` — quotient of `A` collapsing all inhabitants to one for proof-irrelevant fields.";
      signature = "vSquash : Val -> Val";
    };
    vSquashIntro = api.leaf {
      value = vSquashIntro;
      description = "vSquashIntro: value-domain introduction of `Squash A` — lifts any inhabitant of `A` to the sole inhabitant of `Squash A`.";
      signature = "vSquashIntro : Val -> Val";
    };

    vDesc = api.leaf {
      value = vDesc;
      description = "vDesc: value-domain level-zero description type `Desc I k` at index sort `I : U(0)` and universe level `k`.";
      signature = "vDesc : Val -> Val -> Val  -- level, I";
    };
    vDescAt = api.leaf {
      value = vDescAt;
      description = "vDescAt: value-domain `Desc^k I` carrying an explicit `iLev` for the universe of `I`. The conv unfolding rule reads `iLev` to construct the expected `mkDescDescAppV` D-slot.";
      signature = "vDescAt : Val -> Val -> Val -> Val  -- level, iLev, I";
    };
    vMu = api.leaf {
      value = vMu;
      description = "vMu: value-domain levitated fixpoint `μ I D i` — carrier type of values whose constructors are described by `D` at index `i`.";
      signature = "vMu : Val -> Val -> Val -> Val  -- I, D, i";
    };
    vDescCon = api.leaf {
      value = vDescCon;
      description = "vDescCon: value-domain constructor `descCon(D, i, payload)` — the canonical introducer for `μ I D i` values.";
      signature = "vDescCon : Val -> Val -> Val -> Val  -- D, i, payload";
    };
    vDescConTagged = api.leaf {
      value = vDescConTagged;
      description = "vDescConTagged: value-domain `descCon` carrying a `Squash`-truncated guard certificate — surfaces refinement proofs on `fx.types.Certified` values.";
      signature = "vDescConTagged : Val -> Val -> Val -> Val -> Val  -- D, i, payload, cert";
    };

    vInterpD = api.leaf {
      value = vInterpD;
      description = "vInterpD: value-domain interpretation `interpD D X i` — yields the payload type for a constructor described by `D` against carrier `X`.";
      signature = "vInterpD : Val -> Val -> Val -> Val -> Val -> Val  -- k, I, D, X, i";
    };
    vAllD = api.leaf {
      value = vAllD;
      description = "vAllD: value-domain induction-hypothesis collector — threads motive `P` through every recursive position in a payload.";
      signature = "vAllD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val";
    };
    vEverywhereD = api.leaf {
      value = vEverywhereD;
      description = "vEverywhereD: value-domain payload-traversal combinator — applies per-node `f` at every recursive position, producing a same-shape derived payload.";
      signature = "vEverywhereD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val";
    };

    vU = api.leaf {
      value = vU;
      description = "vU: value-domain universe `U(level)` — the type of types at a given Level value.";
      signature = "vU : Val -> Val";
    };

    vLift = api.leaf {
      value = vLift;
      description = "vLift: value-domain Tarski lift `Lift l m A` — non-cumulative cross-level transport of type `A : U(l)` into `U(m)` with `l ≤ m`.";
      signature = "vLift : Val -> Val -> Val -> Val  -- l, m, A";
    };
    vLiftIntro = api.leaf {
      value = vLiftIntro;
      description = "vLiftIntro: value-domain introduction of `Lift l m A` — lifts a term `a : A` at level `l` to a term at level `m`.";
      signature = "vLiftIntro : Val -> Val -> Val -> Val -> Val  -- l, m, A, a";
    };

    vLevel = api.leaf {
      value = vLevel;
      description = "vLevel: value-domain Level type `Level : U(0)`.";
    };
    vLevelZero = api.leaf {
      value = vLevelZero;
      description = "vLevelZero: value-domain level-zero literal `0 : Level`.";
    };
    vLevelSuc = api.leaf {
      value = vLevelSuc;
      description = "vLevelSuc: value-domain successor of a Level expression `suc(l) : Level`.";
      signature = "vLevelSuc : Val -> Val";
    };
    vLevelMax = api.leaf {
      value = vLevelMax;
      description = "vLevelMax: value-domain pointwise max `max(l, r) : Level` — used for universes of dependent products / pairs across distinct levels.";
      signature = "vLevelMax : Val -> Val -> Val  -- l, r";
    };
    vLevelLit = api.leaf {
      value = vLevelLit;
      description = "vLevelLit: value-domain concrete Level literal `n : Level` — derived from a Nix integer at evaluation time.";
      signature = "vLevelLit : Int -> Val";
    };

    vString = api.leaf {
      value = vString;
      description = "vString: value-domain axiomatised primitive `String : U(0)`.";
    };
    vInt = api.leaf {
      value = vInt;
      description = "vInt: value-domain axiomatised primitive `Int : U(0)`.";
    };
    vFloat = api.leaf {
      value = vFloat;
      description = "vFloat: value-domain axiomatised primitive `Float : U(0)`.";
    };
    vAttrs = api.leaf {
      value = vAttrs;
      description = "vAttrs: value-domain axiomatised primitive `Attrs : U(0)` — inhabited by any Nix attrset.";
    };
    vPath = api.leaf {
      value = vPath;
      description = "vPath: value-domain axiomatised primitive `Path : U(0)`.";
    };
    vDerivation = api.leaf {
      value = vDerivation;
      description = "vDerivation: value-domain axiomatised primitive `Derivation : U(0)` — Nix derivation values; the store-producing irreducible value category.";
    };
    vFunction = api.leaf {
      value = vFunction;
      description = "vFunction: value-domain axiomatised primitive `Function : U(0)` — opaque-function carrier.";
    };
    vAny = api.leaf {
      value = vAny;
      description = "vAny: value-domain axiomatised top primitive `Any : U(0)` — accepts every Nix value.";
    };

    vStringLit = api.leaf {
      value = vStringLit;
      description = "vStringLit: value-domain literal carrying a Nix string `s : String`.";
      signature = "vStringLit : String -> Val";
    };
    vIntLit = api.leaf {
      value = vIntLit;
      description = "vIntLit: value-domain literal carrying a Nix integer `n : Int`.";
      signature = "vIntLit : Int -> Val";
    };
    vFloatLit = api.leaf {
      value = vFloatLit;
      description = "vFloatLit: value-domain literal carrying a Nix float `x : Float`.";
      signature = "vFloatLit : Float -> Val";
    };
    vAttrsLit = api.leaf {
      value = vAttrsLit;
      description = "vAttrsLit: value-domain literal carrying an opaque Nix attrset `a : Attrs`.";
      signature = "vAttrsLit : Attrs -> Val";
    };
    vPathLit = api.leaf {
      value = vPathLit;
      description = "vPathLit: value-domain literal carrying a Nix path `p : Path`.";
      signature = "vPathLit : Path -> Val";
    };
    vDerivationLit = api.leaf {
      value = vDerivationLit;
      description = "vDerivationLit: value-domain literal carrying a Nix derivation `d : Derivation` opaquely.";
      signature = "vDerivationLit : Derivation -> Val";
    };
    vFnLit = api.leaf {
      value = vFnLit;
      description = "vFnLit: value-domain literal carrying an opaque Nix function — `fnBox` preserves thunk identity for conv reflexivity.";
      signature = "vFnLit : FnBox -> Val";
    };
    vAnyLit = api.leaf {
      value = vAnyLit;
      description = "vAnyLit: value-domain literal carrying an arbitrary Nix value `v : Any` — used by approximate types whose kernel slot is `vAny`.";
      signature = "vAnyLit : Any -> Val";
    };

    vOpaqueLam = api.leaf {
      value = vOpaqueLam;
      description = "vOpaqueLam: value-domain opaque lambda over a Nix function — kernel never inspects it; `fnBox` thunk identity preserves conv reflexivity.";
      signature = "vOpaqueLam : FnBox -> Val -> Val  -- fnBox, piType";
    };

    vNe = api.leaf {
      value = vNe;
      description = "vNe: neutral value — stuck computation `var^lvl <spine>`; head is a de Bruijn level, spine is a list of elimination frames awaiting reduction.";
      signature = "vNe : Int -> Spine -> Val  -- level, spine";
    };
    freshVar = api.leaf {
      value = freshVar;
      description = "freshVar: introduce a fresh neutral variable at the given depth — used during type-checking to bind a fresh witness under Π / Σ / let binders.";
      signature = "freshVar : Int -> Val  -- depth";
    };

    eApp = api.leaf {
      value = eApp;
      description = "eApp: elimination frame for function application — pushes an argument onto a neutral spine.";
      signature = "eApp : Val -> SpineEntry";
    };
    eFst = api.leaf {
      value = eFst;
      description = "eFst: elimination frame for first-projection on a Σ neutral.";
    };
    eSnd = api.leaf {
      value = eSnd;
      description = "eSnd: elimination frame for second-projection on a Σ neutral.";
    };
    eBootSumElim = api.leaf {
      value = eBootSumElim;
      description = "eBootSumElim: elimination frame for `bootSumElim` on a neutral sum scrutinee — carries motive and case arms.";
      signature = "eBootSumElim : Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eBootJ = api.leaf {
      value = eBootJ;
      description = "eBootJ: elimination frame for the J eliminator on a neutral identity proof — carries A, a, motive, refl-case, b.";
      signature = "eBootJ : Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eStrEq = api.leaf {
      value = eStrEq;
      description = "eStrEq: elimination frame for `strEq` on a neutral string operand — carries the other operand for completion when the neutral resolves.";
      signature = "eStrEq : Val -> Val -> SpineEntry";
    };
    eAbsurd = api.leaf {
      value = eAbsurd;
      description = "eAbsurd: elimination frame for `absurd` on a neutral `Empty`-typed scrutinee — carries the target type `P`; sound because `Empty` has no canonical inhabitants, so this frame can only arise on a stuck spine.";
      signature = "eAbsurd : Val -> SpineEntry  -- type P";
    };
    eDescInd = api.leaf {
      value = eDescInd;
      description = "eDescInd: elimination frame for `descInd` on a neutral `μ`-typed scrutinee — carries `I`, `D`, motive, step.";
      signature = "eDescInd : Val -> Val -> Val -> Val -> SpineEntry";
    };
    eLiftElim = api.leaf {
      value = eLiftElim;
      description = "eLiftElim: elimination frame for `liftElim` on a neutral `Lift l m A` — carries `l`, `m`, `A` for level lowering.";
      signature = "eLiftElim : Val -> Val -> Val -> SpineEntry";
    };

    eInterpD = api.leaf {
      value = eInterpD;
      description = "eInterpD: elimination frame for `interpD` on a neutral description — carries `k`, `I`, `X`, `i` for completion when the neutral resolves.";
      signature = "eInterpD : Val -> Val -> Val -> Val -> SpineEntry";
    };
    eAllD = api.leaf {
      value = eAllD;
      description = "eAllD: elimination frame for `allD` on a neutral description — carries motive `P` plus shape parameters.";
      signature = "eAllD : Val -> Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eEverywhereD = api.leaf {
      value = eEverywhereD;
      description = "eEverywhereD: elimination frame for `everywhereD` on a neutral description — carries per-node `f` plus shape parameters.";
      signature = "eEverywhereD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };

    eSquashElim = api.leaf {
      value = eSquashElim;
      description = "eSquashElim: elimination frame for `squashElim` on a neutral `Squash`-typed scrutinee — carries motive shape (`A`, `B`) and case function `f`.";
      signature = "eSquashElim : Val -> Val -> Val -> SpineEntry";
    };

  };
}
