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

  # Booleans
  vBool = { tag = "VBool"; };
  vTrue = { tag = "VTrue"; };
  vFalse = { tag = "VFalse"; };

  # Lists
  vList = elem: { tag = "VList"; inherit elem; };
  vNil = elem: { tag = "VNil"; inherit elem; };
  vCons = elem: head: tail: { tag = "VCons"; inherit elem head tail; };

  # Unit
  vUnit = { tag = "VUnit"; };
  vTt = { tag = "VTt"; };

  # Void
  vVoid = { tag = "VVoid"; };

  # Sum
  vSum = left: right: { tag = "VSum"; inherit left right; };
  vInl = left: right: val: { tag = "VInl"; inherit left right val; };
  vInr = left: right: val: { tag = "VInr"; inherit left right val; };

  # Identity
  vEq = type: lhs: rhs: { tag = "VEq"; inherit type lhs rhs; };
  vRefl = { tag = "VRefl"; };

  # Universes
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
  eBoolElim = motive: onTrue: onFalse: { tag = "EBoolElim"; inherit motive onTrue onFalse; };
  eListElim = elem: motive: onNil: onCons:
    { tag = "EListElim"; inherit elem motive onNil onCons; };
  eAbsurd = type: { tag = "EAbsurd"; inherit type; };
  eSumElim = left: right: motive: onLeft: onRight:
    { tag = "ESumElim"; inherit left right motive onLeft onRight; };
  eJ = type: lhs: motive: base: rhs:
    { tag = "EJ"; inherit type lhs motive base rhs; };
  eStrEq = arg: { tag = "EStrEq"; inherit arg; };

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
    - `vBool`, `vTrue`, `vFalse` — boolean values
    - `vList`, `vNil`, `vCons` — list values
    - `vUnit`, `vTt` — unit
    - `vVoid` — empty type
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
    - `eNatElim`, `eBoolElim`, `eListElim`, `eAbsurd`, `eSumElim`, `eJ` — inductive eliminators
  '';
  value = {
    inherit mkClosure;
    inherit vLam vPi;
    inherit vSigma vPair;
    inherit vNat vZero vSucc;
    inherit vBool vTrue vFalse;
    inherit vList vNil vCons;
    inherit vUnit vTt;
    inherit vVoid;
    inherit vSum vInl vInr;
    inherit vEq vRefl;
    inherit vU;
    inherit vString vInt vFloat vAttrs vPath vFunction vAny;
    inherit vStringLit vIntLit vFloatLit vAttrsLit vPathLit vFnLit vAnyLit;
    inherit vNe freshVar;
    inherit eApp eFst eSnd eNatElim eBoolElim eListElim eAbsurd eSumElim eJ eStrEq;
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
    "vsigma-tag" = { expr = (vSigma "x" vNat (mkClosure [] { tag = "bool"; })).tag; expected = "VSigma"; };
    "vpair-tag" = { expr = (vPair vZero vTrue).tag; expected = "VPair"; };
    "vnat-tag" = { expr = vNat.tag; expected = "VNat"; };
    "vzero-tag" = { expr = vZero.tag; expected = "VZero"; };
    "vsucc-tag" = { expr = (vSucc vZero).tag; expected = "VSucc"; };
    "vsucc-pred" = { expr = (vSucc vZero).pred.tag; expected = "VZero"; };
    "vbool-tag" = { expr = vBool.tag; expected = "VBool"; };
    "vtrue-tag" = { expr = vTrue.tag; expected = "VTrue"; };
    "vfalse-tag" = { expr = vFalse.tag; expected = "VFalse"; };
    "vlist-tag" = { expr = (vList vNat).tag; expected = "VList"; };
    "vnil-tag" = { expr = (vNil vNat).tag; expected = "VNil"; };
    "vcons-tag" = { expr = (vCons vNat vZero (vNil vNat)).tag; expected = "VCons"; };
    "vunit-tag" = { expr = vUnit.tag; expected = "VUnit"; };
    "vtt-tag" = { expr = vTt.tag; expected = "VTt"; };
    "vvoid-tag" = { expr = vVoid.tag; expected = "VVoid"; };
    "vsum-tag" = { expr = (vSum vNat vBool).tag; expected = "VSum"; };
    "vinl-tag" = { expr = (vInl vNat vBool vZero).tag; expected = "VInl"; };
    "vinr-tag" = { expr = (vInr vNat vBool vTrue).tag; expected = "VInr"; };
    "veq-tag" = { expr = (vEq vNat vZero vZero).tag; expected = "VEq"; };
    "vrefl-tag" = { expr = vRefl.tag; expected = "VRefl"; };
    "vu-tag" = { expr = (vU 0).tag; expected = "VU"; };
    "vu-level" = { expr = (vU 1).level; expected = 1; };
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
    "ebool-elim-tag" = { expr = (eBoolElim vBool vZero vZero).tag; expected = "EBoolElim"; };
    "elist-elim-tag" = { expr = (eListElim vNat vNat vZero vZero).tag; expected = "EListElim"; };
    "eabsurd-tag" = { expr = (eAbsurd vNat).tag; expected = "EAbsurd"; };
    "esum-elim-tag" = { expr = (eSumElim vNat vBool vNat vZero vZero).tag; expected = "ESumElim"; };
    "ej-tag" = { expr = (eJ vNat vZero vNat vZero vZero).tag; expected = "EJ"; };
  };
}
