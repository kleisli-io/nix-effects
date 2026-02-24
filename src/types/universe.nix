# nix-effects universe hierarchy
#
# Type_0 : Type_1 : Type_2 : ... — a cumulative universe tower.
# Nix's laziness means the tower is infinite but only materialized on demand.
# Avoids Russell's paradox: no type contains itself (Type_n has universe n+1,
# so Type_n is not a member of Type_n).
#
# Convention (cumulative):
#   Type_n = { types with universe <= n }
#   Type_n itself has universe = n + 1
#
# The kernel's checkTypeLevel computes and verifies universe levels from
# the typing derivation (kernel-spec.md §8.2), enforcing U(i) : U(i+1).
#
# Grounded in Martin-Löf (1984) "Intuitionistic Type Theory" for the
# stratified universe hierarchy, and Russell's original paradox resolution.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;

  isType = v: builtins.isAttrs v && v ? _tag && v._tag == "Type";

  H = fx.tc.hoas;

  typeAt = mk {
    doc = ''
      Create universe type at level n (cumulative). `Type_n` contains all types
      with universe ≤ n. `Type_n` itself has universe n + 1.

      ```
      Type_n : Type_(n+1) for all n
      ```
    '';
    value = n:
      # Universe types have a precise kernel type (U(n)) but their VALUES
      # (nix-effects type attrsets) can't be elaborated by decide — the
      # kernel has no representation for runtime type attrsets. So we keep
      # _kernel and prove (the kernel type IS U(n)) but remove kernelCheck.
      # Instead, check uses a guard that verifies the attrset structure.
      builtins.removeAttrs (mkType {
        name = "Type_${toString n}";
        kernelType = H.u n;
        # Guard: types-as-values can't be elaborated by decide(), so the
        # guard replaces kernel decide. The `v ? universe` check is a crash
        # boundary: without it, accessing v.universe on a fake type attrset
        # (has _tag="Type" but no universe field) would crash Nix.
        guard = v: isType v && v ? universe && v.universe <= n;
        universe = n + 1;
        description = "Universe level ${toString n}";
      }) ["kernelCheck"];
    tests = {
      "type0-accepts-level0-type" = {
        expr =
          let IntType = mkType { name = "Int"; kernelType = H.int_; };
          in check (typeAt.value 0) IntType;
        expected = true;
      };
      "type0-rejects-itself" = {
        expr = check (typeAt.value 0) (typeAt.value 0);
        expected = false;
      };
      "type1-accepts-type0" = {
        expr = check (typeAt.value 1) (typeAt.value 0);
        expected = true;
      };
      "no-self-membership" = {
        expr = check (typeAt.value 3) (typeAt.value 3);
        expected = false;
      };
      "cumulative-type1-accepts-level0" = {
        expr =
          let IntType = mkType { name = "Int"; kernelType = H.int_; };
          in check (typeAt.value 1) IntType;
        expected = true;
      };
      "has-kernel" = {
        expr = (typeAt.value 0) ? _kernel;
        expected = true;
      };
      "has-prove" = {
        expr = (typeAt.value 0) ? prove;
        expected = true;
      };
      "prove-accepts-nat-in-U0" = {
        expr = (typeAt.value 0).prove H.nat;
        expected = true;
      };
      "prove-accepts-bool-in-U0" = {
        expr = (typeAt.value 0).prove H.bool;
        expected = true;
      };
      "no-kernelCheck" = {
        # Types-as-values can't be elaborated
        expr = (typeAt.value 0) ? kernelCheck;
        expected = false;
      };
    };
  };

  Type_0 = typeAt.value 0;
  Type_1 = typeAt.value 1;
  Type_2 = typeAt.value 2;
  Type_3 = typeAt.value 3;
  Type_4 = typeAt.value 4;

  level = mk {
    doc = "Get the universe level of a type.";
    value = type: type.universe;
    tests = {
      "level0-for-primitive" = {
        expr = level.value (mkType { name = "Int"; kernelType = H.int_; });
        expected = 0;
      };
      "level1-for-type0" = {
        expr = level.value Type_0;
        expected = 1;
      };
      "level2-for-type1" = {
        expr = level.value Type_1;
        expected = 2;
      };
    };
  };

in mk {
  doc = "Universe hierarchy: Type_0 : Type_1 : Type_2 : ... Lazy infinite tower.";
  value = {
    inherit typeAt level;
    inherit Type_0 Type_1 Type_2 Type_3 Type_4;
  };
}
