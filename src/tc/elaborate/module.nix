# fx.tc.elaborate — elaboration-bridge module head.
#
# Public export assembly for the elaboration bridge. `self` is the
# disjoint-union fixpoint of `core.nix` and `extract.nix`; `partTests`
# is the aggregated test map from both parts.
{ self, partTests, api, ... }:

api.mk {
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

    - `validateValue : String → Hoas → NixVal → [{ path; msg; }]` —
      applicative structural validator. Mirrors `elaborateValue`'s recursion
      but accumulates all errors instead of throwing on the first.
      Path accumulator threads structural context (Reader effect).
      Error list is the free monoid (Writer effect).
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
  '';
  value = {
    inherit (self)
      elaborateType elaborateValue validateValue
      extract extractInner reifyType
      verifyAndExtract decide decideType;
  };
  tests = partTests;
}
