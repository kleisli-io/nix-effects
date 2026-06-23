# DiagError — the kernel transcription of the diagnostic Error ADT — plus the
# Failure of a rejected check, encoded as a dependent Sigma-chain.
#
# A code's carrier beta(ktp) : U_0 is the typed base of the rejected witness, so
# the Failure of a check is
#
#   FailureTy = Sigma ktp:KType. Sigma x:(beta ktp). Sigma ctx:String.
#               Sigma rsn:String. Sigma pth:(List String). DiagError      : U_1
#
# well-formed at the single universe U_1. A record over the U_1 field ktp is not:
# a level-1 record field routes through the level-0 desc-arg slot, which cannot
# hold a U_1 value, and the level-1 record former is not reachable. The Sigma-chain
# carries the mixed universe (KType : U_1, the rest U_0) directly. mkFailure nests
# pairs; the projections are the fst_/snd_ spine. The base-only theory is
#
#   FailureTheory = Sigma ktp:KType. Sigma x:(beta ktp). Unit
#
# DiagError is a mono-constructor record datatype over U_0 fields: Layer and
# Detail (variants discriminating the checker stage), msg (String), an optional
# Hint, and children. The diagnostic child tree is arbitrary host data with no
# kernel form, so children : Unit is the checkable opaque slot — the runtime
# payload carries the verbatim Error tree. The arbitrary-host Detail slots are
# `maybe any`: a valid type whose only kernel-checkable inhabitant is `nothing`,
# since no rule checks a term against `any`. That absence-only check is the honest
# substrate boundary for the slots holding raw Nix values.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  V = fx.tc.verified;

  inherit (self.ktype) KType beta iota;

  string = H.string;
  any = H.any;
  unit = H.unit;
  int_ = H.int_;
  maybe = H.maybe;
  listOf = H.listOf;
  nothing = H.nothing;
  fst_ = H.fst_;
  snd_ = H.snd_;

  # The diagnostic Layer: which checker stage rejected the term. The tag carries
  # the discriminator, so each arm's payload is Unit.
  Layer = H.variant [
    { tag = "Kernel"; type = unit; }
    { tag = "Generic"; type = unit; }
    { tag = "Contract"; type = unit; }
  ];

  # A resolved rendering hint.
  Hint = H.record [
    { name = "text"; type = string; }
    { name = "category"; type = string; }
    { name = "severity"; type = string; }
    { name = "docLink"; type = maybe string; }
  ];

  # Per-layer detail records. Slots holding arbitrary host values are `maybe any`
  # (checkable only at absence); the typed slots keep their type.
  KernelDetail = H.record [
    { name = "rule"; type = maybe string; }
    { name = "expected"; type = maybe any; }
    { name = "got"; type = maybe any; }
    { name = "ctx_depth"; type = maybe int_; }
    { name = "term"; type = maybe any; }
    { name = "frame"; type = maybe any; }
    { name = "trace"; type = listOf unit; }
  ];
  GenericDetail = H.record [
    { name = "type"; type = maybe any; }
    { name = "desc"; type = maybe any; }
    { name = "value"; type = maybe any; }
    { name = "context"; type = maybe string; }
    { name = "index"; type = maybe any; }
    { name = "guard"; type = maybe any; }
  ];
  ContractDetail = H.record [
    { name = "type"; type = maybe any; }
    { name = "value"; type = maybe any; }
    { name = "guard"; type = maybe any; }
    { name = "context"; type = maybe string; }
  ];
  Detail = H.variant [
    { tag = "Kernel"; type = KernelDetail; }
    { tag = "Generic"; type = GenericDetail; }
    { tag = "Contract"; type = ContractDetail; }
  ];

  # The diagnostic record. children is the opaque Unit placeholder for the host's
  # recursive Error tree, which has no kernel form.
  DiagError = (H.datatype "DiagError" [
    (H.con "mkErr" [
      (H.field "layer" Layer)
      (H.field "detail" Detail)
      (H.field "msg" string)
      (H.field "hint" (maybe Hint))
      (H.field "children" unit)
    ])
  ]).T;

  # The Failure of a rejected check and its base-only theory.
  FailureTy = H.sigma "ktp" KType (ktp:
    H.sigma "x" (beta ktp) (_:
      H.sigma "ctx" string (_:
        H.sigma "rsn" string (_:
          H.sigma "pth" (listOf string) (_: DiagError)))));
  FailureTheory = H.sigma "ktp" KType (ktp: H.sigma "x" (beta ktp) (_: unit));

  # A Layer / Detail value: the discriminator lives in the variant tag.
  layerOf = tag: H.variantInject Layer tag H.tt;
  detailOf = tag: detailVal: H.variantInject Detail tag detailVal;

  # A DiagError value from its field values.
  mkDiag = { layer, detail, msg, hint, children }:
    V.makeRecord DiagError { inherit layer detail msg hint children; };

  # A Failure value: the nested-pair witness of the Sigma-chain.
  mkFailure = ktp: x: ctx: rsn: pth: de:
    H.pair ktp (H.pair x (H.pair ctx (H.pair rsn (H.pair pth de))));

  # Failure projections: the fst_/snd_ spine of the Sigma-chain.
  failKType = fst_;
  failX = f: fst_ (snd_ f);
  failContext = f: fst_ (snd_ (snd_ f));
  failReason = f: fst_ (snd_ (snd_ (snd_ f)));
  failPath = f: fst_ (snd_ (snd_ (snd_ (snd_ f))));
  failDiag = f: snd_ (snd_ (snd_ (snd_ (snd_ f))));

  # DiagError projections by field name.
  diagLayer = de: V.field DiagError "layer" de;
  diagDetail = de: V.field DiagError "detail" de;
  diagMsg = de: V.field DiagError "msg" de;
  diagHint = de: V.field DiagError "hint" de;
  diagChildren = de: V.field DiagError "children" de;
in
{
  scope = {
    failure = api.namespace {
      description = "fx.tc.kernel.failure: the kernel transcription of the diagnostic Error ADT (DiagError — a mono-constructor record over Layer/Detail/msg/hint and an opaque Unit children slot) and the Failure of a rejected check as a dependent Sigma-chain (FailureTy = Sigma ktp:KType. Sigma x:(beta ktp). Sigma ctx. Sigma rsn. Sigma pth. DiagError; FailureTheory the base-only Sigma). Layer/Detail sub-shapes, the layerOf/detailOf/mkDiag/mkFailure constructors, the fst_/snd_-spine Failure projections, and the named DiagError field projections.";
      value = {
        inherit
          Layer Hint KernelDetail GenericDetail ContractDetail Detail DiagError
          FailureTy FailureTheory
          layerOf detailOf mkDiag mkFailure
          failKType failX failContext failReason failPath failDiag
          diagLayer diagDetail diagMsg diagHint diagChildren;
      };
    };
  };

  tests =
    let
      ev = h: fx.tc.eval.eval [ ] (H.elab h);
      conv = a: b: fx.tc.conv.conv 0 (ev a) (ev b);
      chk = ty: h: !((H.checkHoas ty h) ? error);

      genDetailVal = V.makeRecord GenericDetail {
        type = nothing any;
        desc = nothing any;
        value = nothing any;
        context = nothing string;
        index = nothing any;
        guard = nothing any;
      };
      layerVal = layerOf "Generic";
      detailVal = detailOf "Generic" genDetailVal;
      deVal = mkDiag {
        layer = layerVal;
        detail = detailVal;
        msg = H.stringLit "boom";
        hint = nothing Hint;
        children = H.tt;
      };

      ktp0 = iota H.nat;
      x0 = H.zero;
      # A bare cons/nil has no element type to elaborate outside a checking
      # position; the standalone path literal is annotated so it stands as a
      # conv right-hand side.
      pthA = H.ann (H.cons (H.stringLit "root") H.nil) (listOf string);
      fVal = mkFailure ktp0 x0 (H.stringLit "ctx") (H.stringLit "rsn") pthA deVal;

      # Alpha-renamed copy of the base-only theory, to witness the conv.
      FailureTheoryAlpha = H.sigma "n" KType (n: H.sigma "y" (beta n) (_: unit));
    in
    {
      # Each DiagError sub-shape is a well-formed U_0 type.
      "failure-layer-wf" = { expr = chk (H.u 0) Layer; expected = true; };
      "failure-hint-wf" = { expr = chk (H.u 0) Hint; expected = true; };
      "failure-kernel-detail-wf" = { expr = chk (H.u 0) KernelDetail; expected = true; };
      "failure-generic-detail-wf" = { expr = chk (H.u 0) GenericDetail; expected = true; };
      "failure-contract-detail-wf" = { expr = chk (H.u 0) ContractDetail; expected = true; };
      "failure-detail-wf" = { expr = chk (H.u 0) Detail; expected = true; };
      "failure-diagerror-wf" = { expr = chk (H.u 0) DiagError; expected = true; };

      # The Failure type and its base-only theory are well-formed at U_1.
      "failure-ty-wf" = { expr = chk (H.u 1) FailureTy; expected = true; };
      "failure-theory-wf" = { expr = chk (H.u 1) FailureTheory; expected = true; };

      # The base-only theory is exactly Sigma ktp:KType. Sigma x:(beta ktp). Unit.
      "failure-theory-conv-sigma" = { expr = conv FailureTheory FailureTheoryAlpha; expected = true; };

      # A DiagError value checks, and its five fields project back.
      "failure-generic-detail-value-checks" = { expr = chk GenericDetail genDetailVal; expected = true; };
      "failure-diagerror-value-checks" = { expr = chk DiagError deVal; expected = true; };
      "failure-diag-layer-proj" = { expr = conv (diagLayer deVal) layerVal; expected = true; };
      "failure-diag-detail-proj" = { expr = conv (diagDetail deVal) detailVal; expected = true; };
      "failure-diag-msg-proj" = { expr = conv (diagMsg deVal) (H.stringLit "boom"); expected = true; };
      "failure-diag-hint-proj" = { expr = conv (diagHint deVal) (nothing Hint); expected = true; };
      "failure-diag-children-proj" = { expr = conv (diagChildren deVal) H.tt; expected = true; };

      # A Failure value checks, and its six components project back.
      "failure-value-checks" = { expr = chk FailureTy fVal; expected = true; };
      "failure-proj-ktype" = { expr = conv (failKType fVal) ktp0; expected = true; };
      "failure-proj-x" = { expr = conv (failX fVal) x0; expected = true; };
      "failure-proj-context" = { expr = conv (failContext fVal) (H.stringLit "ctx"); expected = true; };
      "failure-proj-reason" = { expr = conv (failReason fVal) (H.stringLit "rsn"); expected = true; };
      "failure-proj-path" = { expr = conv (failPath fVal) pthA; expected = true; };
      "failure-proj-diag" = { expr = conv (failDiag fVal) deVal; expected = true; };

      # The opaque boundary: no term checks against `any`, so a required `any`
      # slot would make the witness uncheckable — children is Unit instead.
      "failure-any-uncheckable" = { expr = chk H.any (H.stringLit "x"); expected = false; };
    };
}
