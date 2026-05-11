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

  # Natural numbers
  vNat = { tag = "VNat"; };
  vZero = { tag = "VZero"; };
  vSucc = pred: { tag = "VSucc"; inherit pred; };

  # Lists
  vList = elem: { tag = "VList"; inherit elem; };
  vNil = elem: { tag = "VNil"; inherit elem; };
  vCons = elem: head: tail: { tag = "VCons"; inherit elem head tail; };

  # Unit
  vUnit = { tag = "VUnit"; };
  vTt = { tag = "VTt"; };

  # Sum
  vSum = left: right: { tag = "VSum"; inherit left right; };
  vInl = left: right: val: { tag = "VInl"; inherit left right val; };
  vInr = left: right: val: { tag = "VInr"; inherit left right val; };

  # Identity
  vEq = type: lhs: rhs: { tag = "VEq"; inherit type lhs rhs; };
  vRefl = { tag = "VRefl"; };

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
  # levels appear when contained `descArg`/`descPi` quantify over
  # sorts at strictly positive universes. Int-shim mirrors `vU`.
  vDesc = level: I: { tag = "VDesc"; inherit level I; };
  vDescRet = j: { tag = "VDescRet"; inherit j; };            # j : I (target index of ret-leaf)
  # `arg` / `pi` carry a description level `k` and a per-summand
  # level `l` (both Level Val) alongside `S : U(l)`. The bound witness
  # `eq : Eq Level (max l k) k` is stored as a value (typically
  # `vRefl`). Callers pass Level Vals directly; integer literals must
  # be wrapped explicitly via `vLevelLit n` (or `vLevelZero` /
  # `vLevelSuc vLevelZero` for the common 0/1 cases). The homogeneous
  # default is `l = k` with `eq = vRefl`.
  vDescArg = k: l: S: eq: T: { tag = "VDescArg"; inherit k l S eq T; };  # T is a closure S → Desc I
  vDescRec = j: D: { tag = "VDescRec"; inherit j D; };       # j : I (index of recursive child)
  vDescPi = k: l: S: eq: f: D: {                              # f : S → I (index of each child), stored as Val
    tag = "VDescPi";
    inherit k l S eq f D;
  };
  vDescPlus = A: B: { tag = "VDescPlus"; inherit A B; };     # A, B : Desc I — first-class binary coproduct
  vMu = I: D: i: { tag = "VMu"; inherit I D i; };            # μ D i — the type at index i : I
  vDescCon = D: i: d: { tag = "VDescCon"; inherit D i d; };  # target index i carried alongside payload

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
  eNatElim = motive: base: step: { tag = "ENatElim"; inherit motive base step; };
  eListElim = elem: motive: onNil: onCons:
    { tag = "EListElim"; inherit elem motive onNil onCons; };
  eSumElim = left: right: motive: onLeft: onRight:
    { tag = "ESumElim"; inherit left right motive onLeft onRight; };
  eJ = type: lhs: motive: base: rhs:
    { tag = "EJ"; inherit type lhs motive base rhs; };
  eStrEq = arg: { tag = "EStrEq"; inherit arg; };
  eDescInd = D: motive: step: i:
    { tag = "EDescInd"; inherit D motive step i; };
  # `EDescElim` carries a Level value `k` matching `mkDescElim`'s slot,
  # so a quoted spine roundtrips back to the same `mkDescElim k …` term
  # and conv compares descElim frames field-wise.
  eDescElim = k: motive: onRet: onArg: onRec: onPi: onPlus:
    { tag = "EDescElim"; inherit k motive onRet onArg onRec onPi onPlus; };

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

  # `ENatToLevel` records a stuck `natToLevel` on a Nat-typed neutral.
  # No payload: the frame is nullary, mirroring `EFst`/`ESnd`.
  eNatToLevel = { tag = "ENatToLevel"; };

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
    - `vNat`, `vZero`, `vSucc` — natural number values
    - `vList`, `vNil`, `vCons` — list values
    - `vUnit`, `vTt` — unit
    - `vSum`, `vInl`, `vInr` — sum values
    - `vEq`, `vRefl` — identity values
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
    - `eNatElim`, `eListElim`, `eSumElim`, `eJ` — inductive eliminators
  '';
  value = {
    inherit mkClosure;
    inherit vLam vPi;
    inherit vSigma vPair;
    inherit vNat vZero vSucc;
    inherit vList vNil vCons;
    inherit vUnit vTt;
    inherit vSum vInl vInr;
    inherit vEq vRefl vFunext;
    inherit vSquash vSquashIntro;
    inherit vDesc vDescRet vDescArg vDescRec vDescPi vDescPlus vMu vDescCon;
    inherit vInterpD vAllD vEverywhereD;
    inherit vU;
    inherit vLift vLiftIntro;
    inherit vLevel vLevelZero vLevelSuc vLevelMax vLevelLit;
    inherit vString vInt vFloat vAttrs vPath vFunction vAny;
    inherit vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit;
    inherit vOpaqueLam;
    inherit vNe freshVar;
    inherit eApp eFst eSnd eNatElim eListElim eSumElim eJ eStrEq eDescInd eDescElim eLiftElim eNatToLevel;
    inherit eInterpD eAllD eEverywhereD;
    inherit eSquashElim;
  };
  tests = {
    # Closures
    "closure-env" = {
      expr = (mkClosure [ vZero ] { tag = "var"; idx = 0; }).env;
      expected = [ vZero ];
    };
    "closure-body" = {
      expr = (mkClosure [] { tag = "var"; idx = 0; }).body.tag;
      expected = "var";
    };

    # Values
    "vlam-tag" = { expr = (vLam "x" vNat (mkClosure [] { tag = "var"; idx = 0; })).tag; expected = "VLam"; };
    "vpi-tag" = { expr = (vPi "x" vNat (mkClosure [] { tag = "nat"; })).tag; expected = "VPi"; };
    "vsigma-tag" = { expr = (vSigma "x" vNat (mkClosure [] { tag = "nat"; })).tag; expected = "VSigma"; };
    "vpair-tag" = { expr = (vPair vZero vTt).tag; expected = "VPair"; };
    "vnat-tag" = { expr = vNat.tag; expected = "VNat"; };
    "vzero-tag" = { expr = vZero.tag; expected = "VZero"; };
    "vsucc-tag" = { expr = (vSucc vZero).tag; expected = "VSucc"; };
    "vsucc-pred" = { expr = (vSucc vZero).pred.tag; expected = "VZero"; };
    "vlist-tag" = { expr = (vList vNat).tag; expected = "VList"; };
    "vnil-tag" = { expr = (vNil vNat).tag; expected = "VNil"; };
    "vcons-tag" = { expr = (vCons vNat vZero (vNil vNat)).tag; expected = "VCons"; };
    "vunit-tag" = { expr = vUnit.tag; expected = "VUnit"; };
    "vtt-tag" = { expr = vTt.tag; expected = "VTt"; };
    "vsum-tag" = { expr = (vSum vNat vUnit).tag; expected = "VSum"; };
    "vinl-tag" = { expr = (vInl vNat vUnit vZero).tag; expected = "VInl"; };
    "vinr-tag" = { expr = (vInr vNat vUnit vTt).tag; expected = "VInr"; };
    "veq-tag" = { expr = (vEq vNat vZero vZero).tag; expected = "VEq"; };
    "vrefl-tag" = { expr = vRefl.tag; expected = "VRefl"; };
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
    "vopaquelam-tag" = { expr = (vOpaqueLam { _fn = (x: x); } vNat).tag; expected = "VOpaqueLam"; };
    "vopaquelam-piTy" = { expr = (vOpaqueLam { _fn = (x: x); } vNat).piTy.tag; expected = "VNat"; };
    "vopaquelam-nixFn" = { expr = builtins.isFunction (vOpaqueLam { _fn = (x: x); } vNat).nixFn; expected = true; };
    "vopaquelam-fnBox" = { expr = (vOpaqueLam { _fn = (x: x); } vNat)._fnBox ? _fn; expected = true; };

    # Neutrals
    "vne-tag" = { expr = (vNe 0 []).tag; expected = "VNe"; };
    "vne-level" = { expr = (vNe 3 []).level; expected = 3; };
    "vne-empty-spine" = { expr = (vNe 0 []).spine; expected = []; };
    "freshvar-is-neutral" = { expr = (freshVar 5).tag; expected = "VNe"; };
    "freshvar-level" = { expr = (freshVar 5).level; expected = 5; };
    "freshvar-empty-spine" = { expr = (freshVar 5).spine; expected = []; };

    # Elimination frames
    "eapp-tag" = { expr = (eApp vZero).tag; expected = "EApp"; };
    "efst-tag" = { expr = eFst.tag; expected = "EFst"; };
    "esnd-tag" = { expr = eSnd.tag; expected = "ESnd"; };
    "enat-elim-tag" = { expr = (eNatElim vNat vZero vZero).tag; expected = "ENatElim"; };
    "elist-elim-tag" = { expr = (eListElim vNat vNat vZero vZero).tag; expected = "EListElim"; };
    "esum-elim-tag" = { expr = (eSumElim vNat vUnit vNat vZero vZero).tag; expected = "ESumElim"; };
    "ej-tag" = { expr = (eJ vNat vZero vNat vZero vZero).tag; expected = "EJ"; };

    # Descriptions (indexed)
    "vdesc-tag" = { expr = (vDesc vLevelZero vUnit).tag; expected = "VDesc"; };
    "vdesc-I" = { expr = (vDesc vLevelZero vUnit).I.tag; expected = "VUnit"; };
    "vdesc-level" = { expr = (vDesc vLevelZero vUnit).level.tag; expected = "VLevelZero"; };
    "vdesc-level-non-zero" = {
      expr = (vDesc (vLevelSuc vLevelZero) vUnit).level.tag;
      expected = "VLevelSuc";
    };
    "vdescret-tag" = { expr = (vDescRet vTt).tag; expected = "VDescRet"; };
    "vdescret-j" = { expr = (vDescRet vTt).j.tag; expected = "VTt"; };
    "vdescarg-tag" = {
      expr = (vDescArg vLevelZero vLevelZero vNat vRefl (mkClosure [] { tag = "desc-ret"; j = { tag = "tt"; }; })).tag;
      expected = "VDescArg";
    };
    "vdescarg-k-zero" = {
      expr = (vDescArg vLevelZero vLevelZero vNat vRefl (mkClosure [] { tag = "desc-ret"; j = { tag = "tt"; }; })).k.tag;
      expected = "VLevelZero";
    };
    "vdescarg-k-suc" = {
      expr = (vDescArg (vLevelSuc vLevelZero) (vLevelSuc vLevelZero) vNat vRefl (mkClosure [] { tag = "desc-ret"; j = { tag = "tt"; }; })).k.tag;
      expected = "VLevelSuc";
    };
    "vdescarg-l-zero" = {
      expr = (vDescArg vLevelZero vLevelZero vNat vRefl (mkClosure [] { tag = "desc-ret"; j = { tag = "tt"; }; })).l.tag;
      expected = "VLevelZero";
    };
    "vdescarg-eq-refl" = {
      expr = (vDescArg vLevelZero vLevelZero vNat vRefl (mkClosure [] { tag = "desc-ret"; j = { tag = "tt"; }; })).eq.tag;
      expected = "VRefl";
    };
    "vdescrec-tag" = { expr = (vDescRec vTt (vDescRet vTt)).tag; expected = "VDescRec"; };
    "vdescrec-j" = { expr = (vDescRec vTt (vDescRet vTt)).j.tag; expected = "VTt"; };
    "vdescrec-D" = { expr = (vDescRec vTt (vDescRet vTt)).D.tag; expected = "VDescRet"; };
    "vdescpi-tag" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).tag;
      expected = "VDescPi";
    };
    "vdescpi-S" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).S.tag;
      expected = "VNat";
    };
    "vdescpi-f" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).f.tag;
      expected = "VLam";
    };
    "vdescpi-D" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).D.tag;
      expected = "VDescRet";
    };
    "vdescpi-k-zero" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).k.tag;
      expected = "VLevelZero";
    };
    "vdescpi-l-zero" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).l.tag;
      expected = "VLevelZero";
    };
    "vdescpi-eq-refl" = {
      expr = (vDescPi vLevelZero vLevelZero vNat vRefl (vLam "_" vNat (mkClosure [] { tag = "tt"; })) (vDescRet vTt)).eq.tag;
      expected = "VRefl";
    };
    "vmu-tag" = { expr = (vMu vUnit (vDescRet vTt) vTt).tag; expected = "VMu"; };
    "vmu-I" = { expr = (vMu vUnit (vDescRet vTt) vTt).I.tag; expected = "VUnit"; };
    "vmu-D" = { expr = (vMu vUnit (vDescRet vTt) vTt).D.tag; expected = "VDescRet"; };
    "vmu-i" = { expr = (vMu vUnit (vDescRet vTt) vTt).i.tag; expected = "VTt"; };
    "vdesccon-tag" = {
      expr = (vDescCon (vDescRet vTt) vTt vRefl).tag;
      expected = "VDescCon";
    };
    "vdesccon-D" = {
      expr = (vDescCon (vDescRet vTt) vTt vRefl).D.tag;
      expected = "VDescRet";
    };
    "vdesccon-i" = {
      expr = (vDescCon (vDescRet vTt) vTt vRefl).i.tag;
      expected = "VTt";
    };
    "edescind-tag" = { expr = (eDescInd (vDescRet vTt) vNat vZero vTt).tag; expected = "EDescInd"; };
    "edescind-i" = { expr = (eDescInd (vDescRet vTt) vNat vZero vTt).i.tag; expected = "VTt"; };
    "edescelim-tag" = { expr = (eDescElim vLevelZero vNat vZero vZero vZero vZero vZero).tag; expected = "EDescElim"; };
    "edescelim-k" = { expr = (eDescElim vLevelZero vNat vZero vZero vZero vZero vZero).k.tag; expected = "VLevelZero"; };

    # Lift primitive
    "vlift-tag" = { expr = (vLift vLevelZero vLevelZero vRefl vUnit).tag; expected = "VLift"; };
    "vlift-l-zero" = {
      expr = (vLift vLevelZero vLevelZero vRefl vUnit).l.tag;
      expected = "VLevelZero";
    };
    "vlift-m-suc" = {
      expr = (vLift vLevelZero (vLevelSuc vLevelZero) vRefl vUnit).m.tag;
      expected = "VLevelSuc";
    };
    "vlift-A" = {
      expr = (vLift vLevelZero vLevelZero vRefl vUnit).A.tag;
      expected = "VUnit";
    };
    "vlift-eq-refl" = {
      expr = (vLift vLevelZero vLevelZero vRefl vUnit).eq.tag;
      expected = "VRefl";
    };
    "vliftintro-tag" = {
      expr = (vLiftIntro vLevelZero vLevelZero vRefl vUnit vTt).tag;
      expected = "VLiftIntro";
    };
    "vliftintro-a" = {
      expr = (vLiftIntro vLevelZero vLevelZero vRefl vUnit vTt).a.tag;
      expected = "VTt";
    };
    "eliftelim-tag" = { expr = (eLiftElim vLevelZero vLevelZero vRefl vUnit).tag; expected = "ELiftElim"; };
    "eliftelim-l" = { expr = (eLiftElim vLevelZero vLevelZero vRefl vUnit).l.tag; expected = "VLevelZero"; };
    "enattolevel-tag" = { expr = eNatToLevel.tag; expected = "ENatToLevel"; };
    "vdescplus-tag" = { expr = (vDescPlus (vDescRet vTt) (vDescRet vTt)).tag; expected = "VDescPlus"; };
    "vdescplus-A" = { expr = (vDescPlus (vDescRet vTt) (vDescRet vTt)).A.tag; expected = "VDescRet"; };
    "vdescplus-B" = { expr = (vDescPlus (vDescRet vTt) (vDescRet vTt)).B.tag; expected = "VDescRet"; };

    # interpD / allD / everywhereD value forms
    "vinterpd-tag" = {
      expr = (vInterpD vLevelZero vUnit (vDescRet vTt) vNat vTt).tag;
      expected = "VInterpD";
    };
    "vinterpd-D" = {
      expr = (vInterpD vLevelZero vUnit (vDescRet vTt) vNat vTt).D.tag;
      expected = "VDescRet";
    };
    "valld-tag" = {
      expr = (vAllD vLevelZero vUnit (vDescRet vTt) vLevelZero vNat vNat vTt vRefl).tag;
      expected = "VAllD";
    };
    "valld-K" = {
      expr = (vAllD vLevelZero vUnit (vDescRet vTt)
                (vLevelSuc vLevelZero) vNat vNat vTt vRefl).K.tag;
      expected = "VLevelSuc";
    };
    "veverywhered-tag" = {
      expr = (vEverywhereD vLevelZero vUnit (vDescRet vTt) vLevelZero
                vNat vNat vNat vTt vRefl).tag;
      expected = "VEverywhereD";
    };
    "einterpd-tag" = {
      expr = (eInterpD vLevelZero vUnit vNat vTt).tag;
      expected = "EInterpD";
    };
    "einterpd-level" = {
      expr = (eInterpD vLevelZero vUnit vNat vTt).level.tag;
      expected = "VLevelZero";
    };
    "ealld-tag" = {
      expr = (eAllD vLevelZero vUnit vLevelZero vNat vNat vTt vRefl).tag;
      expected = "EAllD";
    };
    "eeverywhered-tag" = {
      expr = (eEverywhereD vLevelZero vUnit vLevelZero vNat vNat vNat vTt vRefl).tag;
      expected = "EEverywhereD";
    };
  };
}
