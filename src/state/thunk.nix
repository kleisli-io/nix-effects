# Thunk: deepSeq-safe carrier for arbitrary values in handler state.
#
# Handler state threaded through `fx.run` / `fx.handle` is `builtins.deepSeq`-
# forced at each trampoline step (see `src/trampoline.nix:20-22,124`) to break
# thunk chains that would stack-overflow on the final force. Real Nix
# derivations (and other cyclic attrsets) send `deepSeq` into infinite
# recursion; `tryEval` cannot recover.
#
# The carrier wraps a value as `{ _tag = "Thunk"; _force = _: value; }`.
# Nix never recurses into a closure's captured environment, so `deepSeq` sees
# only the `_tag` string and the `_force` closure itself — both inert. The
# `_tag` also halts `api.extractValue` (`src/api.nix:17-21`), shielding the
# carrier against both the trampoline's deepSeq AND the module walker.
#
# Discipline:
#   - Wrap with `mkThunk` BEFORE storing in handler state.
#   - Unwrap with `forceThunk` AFTER `fx.run` / `fx.handle` returns.
#   - Never unwrap inside a handler — the recovered value would re-enter
#     state on the next handler return and re-trigger the deepSeq hang.
{ api, ... }:

let
  mkThunk = value: { _tag = "Thunk"; _force = _: value; };

  forceThunk = t:
    if !(builtins.isAttrs t && t ? _force && builtins.isFunction t._force)
    then throw "forceThunk: expected a Thunk carrier with _force closure"
    else t._force null;

  isThunk = v:
    builtins.isAttrs v && v ? _force && builtins.isFunction v._force;

  fakeDrv = { type = "derivation"; name = "fake"; outPath = "/nix/store/x-fake"; };

in
{
  scope = {
    thunk = api.namespace {
      description = "Thunk: deepSeq-safe carrier for transporting values through trampoline-threaded handler state via a closure that hides the value from `builtins.deepSeq`.";
      doc = ''
        Runtime carrier module. Three exports:

          mkThunk    : a       -> Thunk a
          forceThunk : Thunk a -> a
          isThunk    : Value   -> Bool

        A `Thunk` is `{ _tag = "Thunk"; _force = _: value; }`. The value is
        captured in the closure's environment, where `builtins.deepSeq` cannot
        reach it. The companion HOAS combinator `H.thunk inner` provides the
        structurally-lazy kernel type former.

        This carrier is intentionally runtime-only: the HOAS `thunk`
        combinator supplies the typed surface, and handlers use the carrier
        to keep state transport lazy under trampoline evaluation.
      '';
      value = {
        mkThunk = api.leaf {
          value = mkThunk;
          description = "Thunk: deepSeq-safe carrier for transporting values through trampoline-threaded handler state via a closure that hides the value from `builtins.deepSeq`.";
          signature = "mkThunk : a -> Thunk a";
          doc = ''
            A `Thunk` is `{ _tag = "Thunk"; _force = _: value; }`. The value is
            captured in the closure's environment, where `builtins.deepSeq` cannot
            reach it. The companion HOAS combinator `H.thunk inner` provides the
            structurally-lazy kernel type former.

            This carrier is intentionally runtime-only: the HOAS `thunk`
            combinator supplies the typed surface, and handlers use the carrier
            to keep state transport lazy under trampoline evaluation.
          '';
          tests = {
            "deepSeq-survives-cyclic-drv" = {
              expr =
                let
                  cyclic = { type = "derivation"; name = "c"; outPath = "/nix/store/c"; }
                    // { self = cyclic; };
                  state = { id = 0; pkg = mkThunk cyclic; };
                in
                (builtins.tryEval (builtins.deepSeq state null)).success;
              expected = true;
            };

            "force-recovers-value" = {
              expr = (forceThunk (mkThunk fakeDrv)).outPath;
              expected = "/nix/store/x-fake";
            };

            "forceThunk-rejects-raw-value" = {
              expr = (builtins.tryEval (forceThunk fakeDrv)).success;
              expected = false;
            };

            "forceThunk-rejects-attrset-without-force" = {
              expr = (builtins.tryEval (forceThunk { _tag = "Thunk"; })).success;
              expected = false;
            };

            "isThunk-accepts-carrier" = {
              expr = isThunk (mkThunk fakeDrv);
              expected = true;
            };

            "isThunk-rejects-raw-value" = {
              expr = isThunk fakeDrv;
              expected = false;
            };

            "isThunk-rejects-plain-attrset" = {
              expr = isThunk { a = 1; };
              expected = false;
            };

            "isThunk-rejects-non-attrset" = {
              expr = isThunk "Thunk";
              expected = false;
            };

            "carrier-has-tag" = {
              expr = (mkThunk fakeDrv)._tag;
              expected = "Thunk";
            };

            "round-trip-preserves-identity" = {
              expr = (forceThunk (mkThunk fakeDrv)) == fakeDrv;
              expected = true;
            };

            "mkThunk-accepts-non-derivation" = {
              expr = (mkThunk { arbitrary = "value"; })._tag;
              expected = "Thunk";
            };

            "forceThunk-round-trips-string" = {
              expr = forceThunk (mkThunk "hello");
              expected = "hello";
            };
          };
        };

        forceThunk = api.leaf {
          value = forceThunk;
          description = "forceThunk: recover the value hidden inside a Thunk carrier; rejects raw values and malformed carriers.";
          signature = "forceThunk : Thunk a -> a";
          doc = "Recover the value captured inside a `Thunk` carrier.";
        };

        isThunk = api.leaf {
          value = isThunk;
          description = "isThunk: predicate recognizing Thunk carriers by their `_force` closure.";
          signature = "isThunk : Value -> Bool";
          doc = "Return true when a value has the Thunk carrier shape.";
        };
      };
    };
  };
}
