# fx.tc.check — bidirectional type checker module head.
#
# Public export assembly. `self` is the disjoint-union fixpoint of
# `ctx.nix` (contexts + helpers), `check.nix` (check + checkMotive),
# `infer.nix` (infer), `type.nix` (checkType/checkTypeLevel); `partTests`
# is the aggregated test map.
{ self, partTests, api, ... }:

api.mk {
  doc = ''
    # fx.tc.check — Bidirectional Type Checker

    Semi-trusted (Layer 1): uses the TCB (eval/quote/conv) and reports
    type errors via `send "typeError"`. Bugs here may produce wrong
    error messages but cannot cause unsoundness.

    Spec reference: kernel-spec.md §7–§9.

    ## Core Functions

    - `check : Ctx → Tm → Val → Computation Tm` — checking mode (§7.4).
      Verifies that `tm` has type `ty` and returns an elaborated term.
    - `infer : Ctx → Tm → Computation { term; type; }` — synthesis mode (§7.3).
      Infers the type of `tm` and returns the elaborated term with its type.
    - `checkType : Ctx → Tm → Computation Tm` — verify a term is a type (§7.5).
    - `checkTypeLevel : Ctx → Tm → Computation { term; level; }` — like
      `checkType` but also returns the universe level (§8.2).

    ## Context Operations (§7.1)

    - `emptyCtx` — empty typing context `{ env = []; types = []; depth = 0; }`
    - `extend : Ctx → String → Val → Ctx` — add a binding (index 0 = most recent)
    - `lookupType : Ctx → Int → Val` — look up a variable's type by index

    ## Test Helpers

    - `runCheck : Computation → Value` — run a computation through the
      trampoline handler, aborting on `typeError` effects.
    - `checkTm : Ctx → Tm → Val → Tm|Error` — check and unwrap.
    - `inferTm : Ctx → Tm → { term; type; }|Error` — infer and unwrap.

    ## Key Behaviors

    - **Sub rule**: when checking mode doesn't match (e.g., checking a
      variable), falls through to `infer` and uses `conv` to compare.
    - **Cumulativity**: `U(i) ≤ U(j)` when `i ≤ j` (§8.3).
    - **Large elimination**: motives may return any universe, enabling
      type-computing eliminators (`checkMotive`).
    - **Trampolining**: Succ and Cons chains checked iteratively (§11.3).
  '';
  value = {
    inherit (self)
      check infer checkType checkTypeLevel
      emptyCtx extend lookupType
      runCheck checkTm inferTm
      bindP bindPChain
      diag;
  };
  tests = partTests;
}
