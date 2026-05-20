# fx.tc.elaborate — elaboration-bridge module head.
#
# Public export assembly for the elaboration bridge. `self` is the
# disjoint-union fixpoint of every sibling part; `partTests` is the
# aggregated test map.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.elaborate: bridge between `fx.types` and the kernel — `elaborateType`/`elaborateValue`/`extract`/`decide` translate values to kernel terms and back.";
  doc = ''
    # fx.tc.elaborate — Elaboration Bridge

    Bridges the fx.types layer to the kernel's term representation
    via the HOAS combinator layer. Provides the Nix ↔ kernel boundary.

    ## Type Elaboration

    - `elaborateType : FxType → Hoas` — convert an fx.types type descriptor
      to an HOAS tree. Dispatches on: (1) `_kernel` annotation, (2) structural
      fields (Pi: domain/codomain, Sigma: fstType/sndFamily), (3) name
      convention (Bool, Nat, String, Int, Float, ...).
      Dependent Pi/Sigma require explicit `_kernel` annotation.

    ## Value Elaboration

    - `elaborateValue : Hoas → NixVal → Hoas` — convert a Nix value to
      an HOAS term tree given its HOAS type. Bool→true_/false_, Int→natLit,
      List→cons chain, Sum→inl/inr, Sigma→pair. Trampolined for large lists.

    ## Structural Validation

    - `validateValue : Path → Hoas → NixVal → [{ type; context; value; path; reason; }]` —
      collecting-handler bridge over `fx.tc.generic.check.deriveCheck`.
      Accumulates every `typeCheck` effect emission from the canonical
      structural validator into a list of typed error records carrying
      structured `Path` (Position-list) descents to each failure site.
      Empty list ↔ `elaborateValue` would succeed (soundness invariant).

    ## Value Extraction

    - `extract : Hoas → Val → NixValue` — reverse of `elaborateValue`.
      Converts kernel values back to Nix values. Generated Nat/List
      `VDescCon` chains become Nix ints/lists; generated sums become tagged unions.
      Pi extraction wraps the VLam as a Nix function with boundary conversion.
      Opaque types (Attrs, Path, Function, Any) throw — kernel discards payloads.
    - `extractInner : Hoas → Val → Val → NixValue` — three-argument extraction
      with kernel type value threading. Supports dependent Pi/Sigma via closure
      instantiation instead of sentinel tests.
    - `reifyType : Val → Hoas` — converts a kernel type value back to HOAS.
      Fallback for when HOAS body application fails (dependent types).
      Loses sugar (VSigma→sigma, not record).

    ## Decision Procedure

    - `decide : Hoas → NixVal → Bool` — returns true iff elaboration
      and kernel type-checking both succeed. Uses `tryEval` for safety.
    - `decideType : FxType → NixVal → Bool` — elaborate type then decide.

    ## Full Pipeline

    - `verifyAndExtract : Hoas → Hoas → NixValue` — type-check an HOAS
      implementation against an HOAS type, evaluate, extract to Nix value.
      Throws on type error.

    ## Value Embedding

    - `embedVal : Val → Hoas` — lift a kernel value back into HOAS.
      `quote 0` reads the value to a closed `Tm`; `H.embedTm` wraps it
      via the `pre-elab` rule. Use when a Val produced by kernel
      evaluation (e.g. an effect handler's response) needs to flow into
      a surrounding HOAS expression that is itself about to be
      elaborated and re-evaluated.
  '';
  value = {
    inherit (self)
      elaborateType elaborateValue validateValue
      extract extractInner reifyType
      verifyAndExtract embedVal decide decideType
      instantiateOverlayF instantiateOverlay
      evalOverlayF evalOverlay;

    meta = api.namespace {
      description = "fx.tc.elaborate.meta: meta-aware overlay — `VMeta`, overlay check/infer, overlay eliminators, quote, `elabConv`, five scoped meta-effects (force/getMetas/assignMeta/emitConstraint/getConstraints), `runElab` handler.";
      value = {
        inherit (self)
          mkVMeta isVMeta coerce
          elabCheck elabCheckTm
          elabInfer elabInferTm elabInferApp
          elabConv
          elabAppF
          elabFst elabSnd
          elabBootSumElimF
          elabBootJ
          elabSquashElimF
          elabLiftElimF
          elabDescIndF
          elabInterpDF
          elabAllDF
          elabEverywhereDF
          mkMeta quote quoteSp quoteElim nf
          insertImplicits descendImplicitPi plicityAwait isImplicitPi isVMetaTy
          mkHole mkSolved isHole isSolved freshMetaInState
          lookupMeta extendMeta solveMeta reawakenMentions forceMeta
          mkConstraint addConstraint updateConstraint markConstraint registerMentions
          metaIdsVal mentionsOf occurs patternSpine levelsVal simplifyConstraint
          addAndSimplifyConstraint processActiveConstraints sigmaFlatten
          zonkTm evalElab
          metaEff metaResp
          force getMetas assignMeta emitConstraint getConstraints freshMeta
          handle_Meta handle_MetaTy
          emptyState dispatchMeta runElab;
      };
    };

    _internal = api.namespace {
      description = "fx.tc.elaborate._internal: cross-part elaboration helpers reachable from sibling parts via the self-fixpoint; not part of the stable consumer surface.";
      value = {
        inherit (self) reifyDesc;
      };
    };
  };
  tests = partTests // (self.meta.tests or { });
}
