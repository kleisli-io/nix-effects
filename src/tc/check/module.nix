# fx.tc.check — bidirectional type checker module head.
#
# Public export assembly. `self` is the disjoint-union fixpoint of
# `ctx.nix` (contexts + helpers), `check.nix` (check + checkMotive),
# `infer.nix` (infer), `type.nix` (checkType/checkTypeLevel); `partTests`
# is the aggregated test map.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.check: bidirectional type checker with check/infer/checkType/checkTypeLevel, non-cumulative universes, and trampolined succ/cons chains.";
  doc = ''
    # fx.tc.check — Bidirectional Type Checker

    Semi-trusted (Layer 1): uses the TCB (eval/quote/conv) and reports
    type errors via `send "typeError"`. Bugs here may produce wrong
    error messages but cannot cause unsoundness.

    ## Core Functions

    - `check : Ctx → Tm → Val → Computation Tm` — checking mode.
      Verifies that `tm` has type `ty` and returns an elaborated term.
    - `infer : Ctx → Tm → Computation { term; type; }` — synthesis mode.
      Infers the type of `tm` and returns the elaborated term with its type.
    - `checkType : Ctx → Tm → Computation Tm` — verify a term is a type.
    - `checkTypeLevel : Ctx → Tm → Computation { term; level; }` — like
      `checkType` but also returns the universe level.

    ## Context Operations

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
    - **Non-cumulative universes**: Tarski-style, exact-level — `U(i)` does
      not subsume into `U(j)` for `i < j`; conv compares levels by
      `convLevel` with no cumulativity coercion.
    - **Large elimination**: motives may return any universe, enabling
      type-computing eliminators (`checkMotive`).
    - **Trampolining**: Succ and Cons chains checked iteratively.
  '';
  value = {
    inherit (self)
      check infer checkType checkTypeLevel
      emptyCtx extend lookupType
      runCheck checkTm inferTm
      bindP bindPR bindPChain
      _blame _yield
      diag;

    _internal = api.namespace {
      description = "fx.tc.check._internal: cross-part checker helpers reachable from sibling parts via the self-fixpoint; not part of the stable consumer surface.";
      value = {
        inherit (self) checkMotive checkDescAtAnyLevel singleton;
      };
    };
  };
  tests = partTests;
}
