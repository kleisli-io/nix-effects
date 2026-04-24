# fx.tc.check.diag — kernel diagnostic shell module head.
#
# Thin shell around the trusted core (`fx.tc.check.{check, infer,
# runCheck}`). Exposes:
#
#   sourceMap   — parallel SourceMap data type and back-mapping helpers
#                 (see `source_map.nix`).
#   checkD      — `check` that decorates failures with hint + surface.
#   inferD      — `infer` that decorates failures with hint + surface.
#   runCheckD   — raw post-processor used by checkD/inferD.
#
# The shell does NOT replace the trusted core's `typeError` handler.
# It is a value-level transform on `runCheck`'s success/failure result,
# attaching a resolved hint (via `fx.diag.hints.resolve`) and a surface
# back-map (via `sourceMap.hoasAtError`) on the failure branch. The set
# of accepted terms is unchanged; diagnostic data is additive.
{ self, partTests, api, ... }:

api.mk {
  doc = ''
    # fx.tc.check.diag — Kernel Diagnostic Shell

    Outside the trust boundary. Routes kernel check/infer results
    through the trusted core and decorates failures with a resolved
    hint + a SourceMap-sourced surface origin. No new effects.

    ## API

    - `sourceMap` — SourceMap data type and combinators. See the
      module's own doc for the full surface.
    - `checkD   : Ctx -> Tm -> Val -> SourceMap -> Any`
    - `inferD   : Ctx -> Tm -> SourceMap -> Any`
    - `runCheckD : SourceMap -> Computation -> Any`
    - `runCheckDLazy : (Unit -> SourceMap) -> Computation -> Any`

    On success, these return what the trusted core returned (the
    elaborated Tm for checkD, `{term; type;}` for inferD). On failure,
    they return `{ error; msg; expected; got; hint; surface; }`.

    `runCheckDLazy` defers `mkSm null` into the failure branch, so the
    success path pays one closure allocation instead of the full SM
    walker. Kernel HOAS entry points (`checkHoas`/`inferHoas`) use this
    variant.

    `hint` is a string from `fx.diag.hints.resolve` or null.
    `surface` is the SourceMap's hoas payload at the blame chain's
    leaf, or null when the chain exits the mapped region.

    Soundness audit: this module contains no kernel rule logic. A bug
    here can produce wrong hint text or an incorrect surface back-map;
    it cannot cause an ill-typed term to be accepted.
  '';
  value = {
    inherit (self)
      sourceMap
      checkD inferD runCheckD runCheckDLazy;
  };
  tests = partTests;
}
