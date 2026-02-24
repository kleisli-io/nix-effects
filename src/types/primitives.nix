# nix-effects primitive types
#
# Base types corresponding to Nix's built-in value categories.
# Each is a Type at universe level 0 with kernel backing.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  H = fx.tc.hoas;

  String = mk {
    doc = "String type.";
    value = mkType { name = "String"; kernelType = H.string; };
    tests = {
      "accepts-string" = { expr = check (String.value) "hello"; expected = true; };
      "rejects-int" = { expr = check (String.value) 42; expected = false; };
    };
  };

  Int = mk {
    doc = "Integer type.";
    value = mkType { name = "Int"; kernelType = H.int_; };
    tests = {
      "accepts-int" = { expr = check (Int.value) 42; expected = true; };
      "rejects-string" = { expr = check (Int.value) "hello"; expected = false; };
    };
  };

  Bool = mk {
    doc = "Boolean type.";
    value = mkType { name = "Bool"; kernelType = H.bool; };
    tests = {
      "accepts-bool" = { expr = check (Bool.value) true; expected = true; };
      "rejects-int" = { expr = check (Bool.value) 1; expected = false; };
      "has-kernelCheck" = { expr = (Bool.value) ? kernelCheck; expected = true; };
      "kernelCheck-accepts" = { expr = (Bool.value).kernelCheck true; expected = true; };
      "kernelCheck-rejects" = { expr = (Bool.value).kernelCheck 42; expected = false; };
    };
  };

  Float = mk {
    doc = "Float type.";
    value = mkType { name = "Float"; kernelType = H.float_; };
    tests = {
      "accepts-float" = { expr = check (Float.value) 3.14; expected = true; };
      "rejects-int" = { expr = check (Float.value) 42; expected = false; };
    };
  };

  Attrs = mk {
    doc = "Attribute set type (any attrset).";
    value = mkType { name = "Attrs"; kernelType = H.attrs; };
    tests = {
      "accepts-attrs" = { expr = check (Attrs.value) { a = 1; }; expected = true; };
      "rejects-list" = { expr = check (Attrs.value) [1]; expected = false; };
    };
  };

  Path = mk {
    doc = "Path type.";
    value = mkType { name = "Path"; kernelType = H.path; };
    tests = {
      "rejects-string" = { expr = check (Path.value) "/not/a/path"; expected = false; };
    };
  };

  Function = mk {
    doc = "Function type.";
    value = mkType { name = "Function"; kernelType = H.function_; };
    tests = {
      "accepts-lambda" = { expr = check (Function.value) (x: x); expected = true; };
      "rejects-int" = { expr = check (Function.value) 42; expected = false; };
    };
  };

  Null = mk {
    doc = "Null type. Only null inhabits it.";
    value = mkType { name = "Null"; kernelType = H.unit; };
    tests = {
      "accepts-null" = { expr = check (Null.value) null; expected = true; };
      "rejects-zero" = { expr = check (Null.value) 0; expected = false; };
    };
  };

  Unit = mk {
    doc = "Unit type. Isomorphic to Null — the trivial type with one inhabitant.";
    value = mkType { name = "Unit"; kernelType = H.unit; };
    tests = {
      "unit-is-null" = { expr = check (Unit.value) null; expected = true; };
      "unit-has-kernelCheck" = { expr = (Unit.value) ? kernelCheck; expected = true; };
      "unit-kernelCheck-null" = { expr = (Unit.value).kernelCheck null; expected = true; };
      "unit-kernelCheck-rejects" = { expr = (Unit.value).kernelCheck 42; expected = false; };
    };
  };

  Any = mk {
    doc = "Top type. Every value inhabits Any.";
    value = mkType { name = "Any"; kernelType = H.any; };
    tests = {
      "accepts-anything" = {
        expr = check (Any.value) 42
               && check (Any.value) "hello"
               && check (Any.value) null;
        expected = true;
      };
    };
  };

in mk {
  doc = "Primitive types: String, Int, Bool, Float, Attrs, Path, Function, Null, Unit, Any.";
  value = {
    inherit String Int Bool Float Attrs Path Function Null Unit Any;
  };
}
