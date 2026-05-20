# nix-effects primitive types
#
# Base types corresponding to Nix's built-in value categories.
# Each is a Type at universe level 0 with kernel backing.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  H = fx.tc.hoas;

  String = mkType { name = "String"; kernelType = H.string; };

  Int = mkType { name = "Int"; kernelType = H.int_; };

  Bool = mkType { name = "Bool"; kernelType = H.bool; };

  Float = mkType { name = "Float"; kernelType = H.float_; };

  Attrs = mkType { name = "Attrs"; kernelType = H.attrs; };

  Path = mkType { name = "Path"; kernelType = H.path; };

  Derivation = mkType { name = "Derivation"; kernelType = H.derivation; };

  DerivationThunk = mkType { name = "DerivationThunk"; kernelType = H.derivationThunk; };

  Function = mkType { name = "Function"; kernelType = H.function_; };

  Null = mkType { name = "Null"; kernelType = H.unit; };

  Unit = mkType { name = "Unit"; kernelType = H.unit; };

  Any = mkType { name = "Any"; kernelType = H.any; };

in mk {
  description = "Primitive types: String/Int/Bool/Float/Attrs/Path/Derivation/DerivationThunk/Function/Null/Unit/Any — universe-0 atomic types corresponding to Nix's value categories, plus the deepSeq-safe DerivationThunk carrier type.";
  doc = "Primitive types: String, Int, Bool, Float, Attrs, Path, Derivation, DerivationThunk, Function, Null, Unit, Any.";
  value = {
    inherit String Int Bool Float Attrs Path Derivation DerivationThunk Function Null Unit Any;

    __docs = {
      String = {
        description = "String: primitive type whose values are Nix strings; backed by the `H.string` kernel type and decided by `builtins.isString` at the elaborator.";
        doc = "String type. Inhabited by Nix string values.";
        tests = {
          "accepts-string" = { expr = check String "hello"; expected = true; };
          "rejects-int" = { expr = check String 42; expected = false; };
        };
      };

      Int = {
        description = "Int: primitive type whose values are Nix integers; backed by the `H.int_` kernel type and decided by `builtins.isInt` (excludes floats).";
        doc = "Integer type. Inhabited by Nix integer values; rejects floats.";
        tests = {
          "accepts-int" = { expr = check Int 42; expected = true; };
          "rejects-string" = { expr = check Int "hello"; expected = false; };
        };
      };

      Bool = {
        description = "Bool: primitive type whose only inhabitants are `true` and `false`; backed by the `H.bool` kernel type with precise kernel decision.";
        doc = "Boolean type. Inhabited by `true` and `false`.";
        tests = {
          "accepts-bool" = { expr = check Bool true; expected = true; };
          "rejects-int" = { expr = check Bool 1; expected = false; };
          "has-kernelCheck" = { expr = Bool ? kernelCheck; expected = true; };
          "kernelCheck-accepts" = { expr = Bool.kernelCheck true; expected = true; };
          "kernelCheck-rejects" = { expr = Bool.kernelCheck 42; expected = false; };
        };
      };

      Float = {
        description = "Float: primitive type whose values are Nix floating-point numbers; backed by `H.float_` and decided by `builtins.isFloat` (excludes ints).";
        doc = "Float type. Inhabited by Nix floats; rejects integers.";
        tests = {
          "accepts-float" = { expr = check Float 3.14; expected = true; };
          "rejects-int" = { expr = check Float 42; expected = false; };
        };
      };

      Attrs = {
        description = "Attrs: primitive type for any Nix attribute set; backed by `H.attrs` — accepts every attrset including `{}`, never checks field shape.";
        doc = "Attribute set type. Any attrset, including `{}`. Use `Record` for declared-field shape.";
        tests = {
          "accepts-attrs" = { expr = check Attrs { a = 1; }; expected = true; };
          "rejects-list" = { expr = check Attrs [1]; expected = false; };
        };
      };

      Path = {
        description = "Path: primitive type for Nix path values; rejects strings — paths and strings are distinct value categories in Nix.";
        doc = "Path type. Nix path values (e.g. `./foo`); not interchangeable with strings.";
        tests = {
          "rejects-string" = { expr = check Path "/not/a/path"; expected = false; };
        };
      };

      Derivation = {
        description = "Derivation: primitive type for Nix derivation values — attrsets carrying `type = \"derivation\"`. The store-producing irreducible value category that makes Nix Nix; rejects plain attrsets, strings, and paths.";
        doc = ''
          Derivation type. Nix derivation values (built via `mkDerivation` /
          `runCommand` / `stdenv.mkDerivation` etc.).

          Membership is decided structurally: any attrset with
          `type = "derivation"` qualifies. Bare attrsets (no `type` field),
          strings (e.g. `"pkgs.hello"`), and paths (e.g. `./foo`) are
          rejected — derivations are a distinct value category.
        '';
        tests = {
          "accepts-derivation-shape" = {
            expr = check Derivation { type = "derivation"; name = "fake"; outPath = "/nix/store/x"; };
            expected = true;
          };
          "rejects-plain-attrset" = {
            expr = check Derivation { a = 1; };
            expected = false;
          };
          "rejects-string" = { expr = check Derivation "pkgs.hello"; expected = false; };
          "rejects-attrset-with-non-derivation-type" = {
            expr = check Derivation { type = "function"; };
            expected = false;
          };
        };
      };

      DerivationThunk = {
        description = "DerivationThunk: deepSeq-safe carrier wrapping a Nix derivation; an attrset of shape `{ _tag = \"DerivationThunk\"; _force = _: drv; }` produced by `fx.state.mkDerivationThunk`.";
        doc = ''
          DerivationThunk type. Inhabited by carriers produced by
          `fx.state.mkDerivationThunk`.

          Kernel-primitive type: `kernelType = H.derivationThunk` — membership
          is decided structurally by the kernel's native predicate
          (`_tag = "DerivationThunk"` ∧ `_force` field present). The
          companion runtime helper `fx.state.forceDerivationThunk` recovers
          the underlying drv after the trampoline returns.

          `DerivationThunk` and `Derivation` are distinct types with disjoint
          value sets — there is no implicit subtyping. Coercions are explicit
          and one-step (`mkDerivationThunk` and `forceDerivationThunk`).

          Use as the payload type in effect descriptions for ops that carry
          derivations through trampoline-threaded handler state. See
          `src/state/derivation-thunk.nix` for the runtime carrier and
          `docs/kernel-spec.md` for the trampoline-contract rationale.
        '';
        tests =
          let fakeDrv = { type = "derivation"; name = "fake"; outPath = "/nix/store/x"; };
          in {
            "accepts-carrier" = {
              expr = check DerivationThunk
                (fx.state.derivation-thunk.mkDerivationThunk fakeDrv);
              expected = true;
            };
            "rejects-raw-derivation" = {
              expr = check DerivationThunk fakeDrv;
              expected = false;
            };
            "rejects-plain-attrset" = {
              expr = check DerivationThunk { a = 1; };
              expected = false;
            };
            "rejects-attrset-with-wrong-tag" = {
              expr = check DerivationThunk { _tag = "Other"; _force = _: null; };
              expected = false;
            };
            "rejects-attrset-with-tag-but-no-force" = {
              expr = check DerivationThunk { _tag = "DerivationThunk"; };
              expected = false;
            };
            "rejects-non-attrset" = {
              expr = check DerivationThunk "DerivationThunk";
              expected = false;
            };
          };
      };

      Function = {
        description = "Function: primitive type for Nix lambdas; backed by `H.function_` and decided by `builtins.isFunction` — argument/result shape is not introspected.";
        doc = "Function type. Any Nix lambda. The arrow shape (`a -> b`) is not checked at this level — use `H.forall` for that.";
        tests = {
          "accepts-lambda" = { expr = check Function (x: x); expected = true; };
          "rejects-int" = { expr = check Function 42; expected = false; };
        };
      };

      Null = {
        description = "Null: primitive type whose only inhabitant is `null`; isomorphic to `Unit` and backed by the `H.unit` kernel type.";
        doc = "Null type. Only `null` inhabits it. Isomorphic to `Unit`.";
        tests = {
          "accepts-null" = { expr = check Null null; expected = true; };
          "rejects-zero" = { expr = check Null 0; expected = false; };
        };
      };

      Unit = {
        description = "Unit: primitive type with one inhabitant `null`; isomorphic to `Null`, backed by the `H.unit` kernel type — the trivial / terminal type.";
        doc = "Unit type. Trivial type with one inhabitant. Isomorphic to `Null`.";
        tests = {
          "unit-is-null" = { expr = check Unit null; expected = true; };
          "unit-has-kernelCheck" = { expr = Unit ? kernelCheck; expected = true; };
          "unit-kernelCheck-null" = { expr = Unit.kernelCheck null; expected = true; };
          "unit-kernelCheck-rejects" = { expr = Unit.kernelCheck 42; expected = false; };
        };
      };

      Any = {
        description = "Any: top type; every Nix value inhabits it, backed by `H.any` — used as the lossy fallback kernel for approximate types.";
        doc = "Top type. Every value inhabits `Any`. Approximate types fall back to `Any` for their kernel slot.";
        tests = {
          "accepts-anything" = {
            expr = check Any 42
                   && check Any "hello"
                   && check Any null;
            expected = true;
          };
        };
      };
    };
  };
}
