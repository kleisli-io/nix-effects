# DerivationThunk: deepSeq-safe carrier for Nix derivations in handler state.
#
# Handler state threaded through `fx.run` / `fx.handle` is `builtins.deepSeq`-
# forced at each trampoline step (see `src/trampoline.nix:20-22,124`) to break
# thunk chains that would stack-overflow on the final force. Real Nix
# derivations have circular `passthru`/`all`/`outputs` references that send
# `deepSeq` into infinite recursion; `tryEval` cannot recover.
#
# The carrier wraps a drv as `{ _tag = "DerivationThunk"; _force = _: drv; }`.
# Nix never recurses into a closure's captured environment, so `deepSeq` sees
# only the `_tag` string and the `_force` closure itself — both inert. The
# `_tag` also halts `api.extractValue` (`src/api.nix:17-21`), shielding the
# carrier against both the trampoline's deepSeq AND the module walker.
#
# Discipline:
#   - Wrap with `mkDerivationThunk` BEFORE storing in handler state.
#   - Unwrap with `forceDerivationThunk` AFTER `fx.run` / `fx.handle` returns.
#   - Never unwrap inside a handler — the recovered drv would re-enter state
#     on the next handler return and re-trigger the deepSeq hang.
{ api, ... }:

let
  inherit (api) mk;

  isDrv = v: builtins.isAttrs v && (v.type or null) == "derivation";

  mkDerivationThunk = drv:
    if !(isDrv drv)
    then throw "mkDerivationThunk: expected a Nix derivation, got ${builtins.typeOf drv}"
    else { _tag = "DerivationThunk"; _force = _: drv; };

  forceDerivationThunk = t:
    if !(builtins.isAttrs t && (t._tag or null) == "DerivationThunk")
    then throw "forceDerivationThunk: expected a DerivationThunk carrier"
    else t._force null;

  isDerivationThunk = v:
    builtins.isAttrs v && (v._tag or null) == "DerivationThunk";

  # Fake-drv attrset shapes used by tests. Acyclic so equality checks work;
  # the cyclic-survival test builds its own self-referential value.
  fakeDrv = { type = "derivation"; name = "fake"; outPath = "/nix/store/x-fake"; };

in mk {
  description = "DerivationThunk: deepSeq-safe carrier for transporting Nix derivations through trampoline-threaded handler state via a closure that hides the drv from `builtins.deepSeq`.";
  signature = "mkDerivationThunk : Derivation -> DerivationThunk";
  doc = ''
    Runtime carrier module. Three exports:

      mkDerivationThunk    : Derivation      -> DerivationThunk
      forceDerivationThunk : DerivationThunk -> Derivation
      isDerivationThunk    : Value           -> Bool

    A `DerivationThunk` is `{ _tag = "DerivationThunk"; _force = _: drv; }`.
    The drv is captured in the closure's environment, where `builtins.deepSeq`
    cannot reach it. The companion type `fx.types.DerivationThunk` provides
    the membership predicate for effect-system validation.

    See `docs/kernel-spec.md` for the full rationale and the trampoline
    contract this carrier satisfies.
  '';
  value = { inherit mkDerivationThunk forceDerivationThunk isDerivationThunk; };
  tests = {
    "deepSeq-survives-cyclic-drv" = {
      expr =
        let
          cyclic = { type = "derivation"; name = "c"; outPath = "/nix/store/c"; }
                 // { self = cyclic; };
          state  = { id = 0; pkg = mkDerivationThunk cyclic; };
        in (builtins.tryEval (builtins.deepSeq state null)).success;
      expected = true;
    };

    "force-recovers-drv" = {
      expr = (forceDerivationThunk (mkDerivationThunk fakeDrv)).outPath;
      expected = "/nix/store/x-fake";
    };

    "mkDerivationThunk-rejects-non-drv" = {
      expr = (builtins.tryEval (mkDerivationThunk { not = "a drv"; })).success;
      expected = false;
    };

    "mkDerivationThunk-rejects-string" = {
      expr = (builtins.tryEval (mkDerivationThunk "pkgs.hello")).success;
      expected = false;
    };

    "forceDerivationThunk-rejects-raw-drv" = {
      expr = (builtins.tryEval (forceDerivationThunk fakeDrv)).success;
      expected = false;
    };

    "forceDerivationThunk-rejects-wrong-tag" = {
      expr = (builtins.tryEval (forceDerivationThunk { _tag = "Other"; _force = _: null; })).success;
      expected = false;
    };

    "isDerivationThunk-accepts-carrier" = {
      expr = isDerivationThunk (mkDerivationThunk fakeDrv);
      expected = true;
    };

    "isDerivationThunk-rejects-raw-drv" = {
      expr = isDerivationThunk fakeDrv;
      expected = false;
    };

    "isDerivationThunk-rejects-plain-attrset" = {
      expr = isDerivationThunk { a = 1; };
      expected = false;
    };

    "isDerivationThunk-rejects-non-attrset" = {
      expr = isDerivationThunk "DerivationThunk";
      expected = false;
    };

    "carrier-has-tag" = {
      expr = (mkDerivationThunk fakeDrv)._tag;
      expected = "DerivationThunk";
    };

    "round-trip-preserves-identity" = {
      expr = (forceDerivationThunk (mkDerivationThunk fakeDrv)) == fakeDrv;
      expected = true;
    };
  };
}
