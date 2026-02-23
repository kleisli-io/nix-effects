# nix-effects primitive types
#
# Base types corresponding to Nix's built-in value categories.
# Each is a Type at universe level 0.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  H = fx.tc.hoas;

  String = mk {
    doc = "String type.";
    value = mkType { name = "String"; check = builtins.isString; };
    tests = {
      "accepts-string" = { expr = check (String.value) "hello"; expected = true; };
      "rejects-int" = { expr = check (String.value) 42; expected = false; };
    };
  };

  Int = mk {
    doc = "Integer type.";
    value = mkType { name = "Int"; check = builtins.isInt; };
    tests = {
      "accepts-int" = { expr = check (Int.value) 42; expected = true; };
      "rejects-string" = { expr = check (Int.value) "hello"; expected = false; };
    };
  };

  Bool = mk {
    doc = "Boolean type.";
    value = mkType { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
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
    value = mkType { name = "Float"; check = builtins.isFloat; };
    tests = {
      "accepts-float" = { expr = check (Float.value) 3.14; expected = true; };
      "rejects-int" = { expr = check (Float.value) 42; expected = false; };
    };
  };

  Attrs = mk {
    doc = "Attribute set type (any attrset).";
    value = mkType { name = "Attrs"; check = builtins.isAttrs; };
    tests = {
      "accepts-attrs" = { expr = check (Attrs.value) { a = 1; }; expected = true; };
      "rejects-list" = { expr = check (Attrs.value) [1]; expected = false; };
    };
  };

  Path = mk {
    doc = "Path type.";
    value = mkType { name = "Path"; check = builtins.isPath; };
    tests = {
      "rejects-string" = { expr = check (Path.value) "/not/a/path"; expected = false; };
    };
  };

  Function = mk {
    doc = "Function type.";
    value = mkType { name = "Function"; check = builtins.isFunction; };
    tests = {
      "accepts-lambda" = { expr = check (Function.value) (x: x); expected = true; };
      "rejects-int" = { expr = check (Function.value) 42; expected = false; };
    };
  };

  Null = mk {
    doc = "Null type. Only null inhabits it.";
    value = mkType { name = "Null"; check = v: v == null; kernelType = H.unit; };
    tests = {
      "accepts-null" = { expr = check (Null.value) null; expected = true; };
      "rejects-zero" = { expr = check (Null.value) 0; expected = false; };
    };
  };

  Unit = mk {
    doc = "Unit type. Isomorphic to Null — the trivial type with one inhabitant.";
    value = mkType { name = "Unit"; check = v: v == null; kernelType = H.unit; };
    tests = {
      "unit-is-null" = { expr = check (Unit.value) null; expected = true; };
      "unit-has-kernelCheck" = { expr = (Unit.value) ? kernelCheck; expected = true; };
      "unit-kernelCheck-null" = { expr = (Unit.value).kernelCheck null; expected = true; };
      "unit-kernelCheck-rejects" = { expr = (Unit.value).kernelCheck 42; expected = false; };
    };
  };

  Any = mk {
    doc = "Top type. Every value inhabits Any.";
    value = mkType { name = "Any"; check = _: true; };
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
