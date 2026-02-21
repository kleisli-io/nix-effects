# nix-effects type constructors
#
# Higher-kinded type constructors that build compound types from simpler ones.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  inherit (fx.kernel) pure bind send;

  Record = mk {
    doc = ''
      Record type constructor. Takes a schema { field = Type; ... } and checks
      that a value has all required fields with correct types.
      Extra fields are permitted (open record semantics).
    '';
    value = schema: mkType {
      name = "Record{${builtins.concatStringsSep ", " (builtins.attrNames schema)}}";
      check = v:
        builtins.isAttrs v
        && builtins.all (field:
          v ? ${field} && (schema.${field}).check v.${field}
        ) (builtins.attrNames schema);
    };
    tests = {
      "accepts-matching-record" = {
        expr =
          let
            PersonT = Record.value {
              name = mkType { name = "String"; check = builtins.isString; };
              age = mkType { name = "Int"; check = builtins.isInt; };
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "rejects-missing-field" = {
        expr =
          let
            PersonT = Record.value {
              name = mkType { name = "String"; check = builtins.isString; };
              age = mkType { name = "Int"; check = builtins.isInt; };
            };
          in check PersonT { name = "Alice"; };
        expected = false;
      };
      "rejects-wrong-type" = {
        expr =
          let
            PersonT = Record.value {
              name = mkType { name = "String"; check = builtins.isString; };
              age = mkType { name = "Int"; check = builtins.isInt; };
            };
          in check PersonT { name = "Alice"; age = "thirty"; };
        expected = false;
      };
      "allows-extra-fields" = {
        expr =
          let
            PersonT = Record.value {
              name = mkType { name = "String"; check = builtins.isString; };
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
    };
  };

  ListOf = mk {
    doc = ''
      Homogeneous list type. `ListOf Type` checks that all elements have the given type.

      Custom verifier sends per-element `typeCheck` effects with indexed context
      strings (e.g. `List[Int][2]`) for blame tracking. Unlike Sigma, elements
      are independent — no short-circuit. All elements are checked; the handler
      decides error policy (strict aborts on first, collecting gathers all).
    '';
    value = elemType: mkType {
      name = "List[${elemType.name}]";
      check = v:
        builtins.isList v && builtins.all elemType.check v;
      # Per-element effectful verify for blame tracking.
      # Sends typeCheck per element with indexed context: "List[Int][0]", etc.
      # Non-list inputs fall back to a single typeCheck for the whole type.
      verify = self: v:
        if !(builtins.isList v) then
          send "typeCheck" { type = self; context = self.name; value = v; }
        else
          let
            n = builtins.length v;
            # Build chain right-to-left so effects execute in index order (0, 1, 2, ...)
            checkAll = builtins.foldl'
              (acc: i:
                bind (send "typeCheck" {
                  type = elemType;
                  context = "${self.name}[${toString i}]";
                  value = builtins.elemAt v i;
                }) (_: acc))
              (pure v)
              (builtins.genList (i: n - 1 - i) n);
          in if n == 0 then pure v else checkAll;
    };
    tests = {
      "accepts-matching-list" = {
        expr =
          let intList = ListOf.value (mkType { name = "Int"; check = builtins.isInt; });
          in check intList [1 2 3];
        expected = true;
      };
      "rejects-mixed-list" = {
        expr =
          let intList = ListOf.value (mkType { name = "Int"; check = builtins.isInt; });
          in check intList [1 "two" 3];
        expected = false;
      };
      "accepts-empty-list" = {
        expr =
          let intList = ListOf.value (mkType { name = "Int"; check = builtins.isInt; });
          in check intList [];
        expected = true;
      };
    };
  };

  Maybe = mk {
    doc = "Option type. Maybe Type accepts null or a value of Type.";
    value = innerType: mkType {
      name = "Maybe[${innerType.name}]";
      check = v: v == null || innerType.check v;
    };
    tests = {
      "accepts-null" = {
        expr =
          let maybeInt = Maybe.value (mkType { name = "Int"; check = builtins.isInt; });
          in check maybeInt null;
        expected = true;
      };
      "accepts-value" = {
        expr =
          let maybeInt = Maybe.value (mkType { name = "Int"; check = builtins.isInt; });
          in check maybeInt 42;
        expected = true;
      };
      "rejects-wrong-type" = {
        expr =
          let maybeInt = Maybe.value (mkType { name = "Int"; check = builtins.isInt; });
          in check maybeInt "hello";
        expected = false;
      };
    };
  };

  Either = mk {
    doc = ''
      Tagged union of two types. Accepts `{ _tag = "Left"; value = a; }`
      or `{ _tag = "Right"; value = b; }`.
    '';
    value = leftType: rightType: mkType {
      name = "Either[${leftType.name}, ${rightType.name}]";
      check = v:
        builtins.isAttrs v
        && v ? _tag && v ? value
        && ((v._tag == "Left" && leftType.check v.value)
            || (v._tag == "Right" && rightType.check v.value));
    };
    tests = {
      "accepts-left" = {
        expr =
          let
            e = Either.value
              (mkType { name = "String"; check = builtins.isString; })
              (mkType { name = "Int"; check = builtins.isInt; });
          in check e { _tag = "Left"; value = "error"; };
        expected = true;
      };
      "accepts-right" = {
        expr =
          let
            e = Either.value
              (mkType { name = "String"; check = builtins.isString; })
              (mkType { name = "Int"; check = builtins.isInt; });
          in check e { _tag = "Right"; value = 42; };
        expected = true;
      };
      "rejects-wrong-tag" = {
        expr =
          let
            e = Either.value
              (mkType { name = "String"; check = builtins.isString; })
              (mkType { name = "Int"; check = builtins.isInt; });
          in check e { _tag = "Other"; value = 42; };
        expected = false;
      };
    };
  };

  Variant = mk {
    doc = ''
      Discriminated union. Takes `{ tag = Type; ... }` schema.
      Accepts `{ _tag = "tag"; value = ...; }` where value has the corresponding type.
    '';
    value = schema: mkType {
      name = "Variant{${builtins.concatStringsSep " | " (builtins.attrNames schema)}}";
      check = v:
        builtins.isAttrs v
        && v ? _tag && v ? value
        && schema ? ${v._tag}
        && (schema.${v._tag}).check v.value;
    };
    tests = {
      "accepts-valid-variant" = {
        expr =
          let
            Shape = Variant.value {
              circle = mkType { name = "Float"; check = builtins.isFloat; };
              rect = mkType { name = "Attrs"; check = builtins.isAttrs; };
            };
          in check Shape { _tag = "circle"; value = 5.0; };
        expected = true;
      };
      "rejects-unknown-tag" = {
        expr =
          let
            Shape = Variant.value {
              circle = mkType { name = "Float"; check = builtins.isFloat; };
            };
          in check Shape { _tag = "triangle"; value = null; };
        expected = false;
      };
    };
  };

in mk {
  doc = "Type constructors: Record, ListOf, Maybe, Either, Variant.";
  value = {
    inherit Record ListOf Maybe Either Variant;
  };
}
