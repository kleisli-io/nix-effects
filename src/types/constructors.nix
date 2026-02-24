# nix-effects type constructors
#
# Higher-kinded type constructors that build compound types from simpler ones.
# All types require kernelType. When sub-types lack kernel backing (_kernel),
# kernelType = H.any with a guard fallback for the real check.
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  inherit (fx.kernel) pure bind send;
  H = fx.tc.hoas;

  Record = mk {
    doc = ''
      Record type constructor. Takes a schema { field = Type; ... } and checks
      that a value has all required fields with correct types.
      Extra fields are permitted (open record semantics).
    '';
    value = schema:
      let
        sortedNames = builtins.sort builtins.lessThan (builtins.attrNames schema);
        allHaveKernel = builtins.all (f: schema.${f} ? _kernel) sortedNames;
        hoasFields = map (f: { name = f; type = schema.${f}._kernel; }) sortedNames;
        kernelType = if allHaveKernel && sortedNames != []
          then H.record hoasFields
          else H.any;
        guard = v:
          builtins.isAttrs v
          && builtins.all (field:
            v ? ${field} && (schema.${field}).check v.${field}
          ) sortedNames;
      in mkType {
        name = "Record{${builtins.concatStringsSep ", " sortedNames}}";
        inherit kernelType guard;
      };
    tests = let
      FP = fx.types.primitives;
    in {
      "accepts-matching-record" = {
        expr =
          let
            PersonT = Record.value {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "rejects-missing-field" = {
        expr =
          let
            PersonT = Record.value {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; };
        expected = false;
      };
      "rejects-wrong-type" = {
        expr =
          let
            PersonT = Record.value {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; age = "thirty"; };
        expected = false;
      };
      "allows-extra-fields" = {
        expr =
          let
            PersonT = Record.value {
              name = FP.String;
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "has-kernelCheck" = {
        expr = (Record.value { n = FP.Int; b = FP.Bool; }) ? kernelCheck;
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
    value = elemType:
      let
        hasKernel = elemType ? _kernel;
        kernelType = if hasKernel then H.listOf elemType._kernel else H.any;
        # Always guard with element-level .check: refined types (and any type
        # with a guard) have .check ≠ .kernelCheck, so kernel decide on
        # listOf(elemKernel) would miss the refinement predicate.
        # .kernelCheck (via kernelType) remains pure kernel for formal paths.
        guard = v: builtins.isList v && builtins.all elemType.check v;
      in mkType {
        name = "List[${elemType.name}]";
        inherit kernelType guard;
        # Per-element effectful verify for blame tracking.
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
    tests = let FP = fx.types.primitives; in {
      "accepts-matching-list" = {
        expr =
          let intList = ListOf.value FP.Int;
          in check intList [1 2 3];
        expected = true;
      };
      "rejects-mixed-list" = {
        expr =
          let intList = ListOf.value FP.Int;
          in check intList [1 "two" 3];
        expected = false;
      };
      "accepts-empty-list" = {
        expr =
          let intList = ListOf.value FP.Int;
          in check intList [];
        expected = true;
      };
      "kernel-propagates" = {
        expr = (ListOf.value FP.Bool) ? kernelCheck;
        expected = true;
      };
      "kernelCheck-accepts" = {
        expr = (ListOf.value FP.Bool).kernelCheck [true false];
        expected = true;
      };
      "kernelCheck-rejects-bad-elem" = {
        expr = (ListOf.value FP.Bool).kernelCheck [42];
        expected = false;
      };
    };
  };

  Maybe = mk {
    doc = "Option type. Maybe Type accepts null or a value of Type.";
    value = innerType:
      let
        hasKernel = innerType ? _kernel;
        kernelType = if hasKernel then H.maybe innerType._kernel else H.any;
        guard =
          if hasKernel then null
          else v: v == null || innerType.check v;
      in mkType {
        name = "Maybe[${innerType.name}]";
        inherit kernelType guard;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-null" = {
        expr = check (Maybe.value FP.Int) null;
        expected = true;
      };
      "accepts-value" = {
        expr = check (Maybe.value FP.Int) 42;
        expected = true;
      };
      "rejects-wrong-type" = {
        expr = check (Maybe.value FP.Int) "hello";
        expected = false;
      };
      "has-kernelCheck" = {
        expr = (Maybe.value FP.Int) ? kernelCheck;
        expected = true;
      };
    };
  };

  Either = mk {
    doc = ''
      Tagged union of two types. Accepts `{ _tag = "Left"; value = a; }`
      or `{ _tag = "Right"; value = b; }`.
    '';
    value = leftType: rightType:
      let
        hasKernel = leftType ? _kernel && rightType ? _kernel;
        kernelType = if hasKernel
          then H.sum leftType._kernel rightType._kernel
          else H.any;
        guard =
          if hasKernel then null
          else v:
            builtins.isAttrs v
            && v ? _tag && v ? value
            && ((v._tag == "Left" && leftType.check v.value)
                || (v._tag == "Right" && rightType.check v.value));
      in mkType {
        name = "Either[${leftType.name}, ${rightType.name}]";
        inherit kernelType guard;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-left" = {
        expr =
          let e = Either.value FP.String FP.Int;
          in check e { _tag = "Left"; value = "error"; };
        expected = true;
      };
      "accepts-right" = {
        expr =
          let e = Either.value FP.String FP.Int;
          in check e { _tag = "Right"; value = 42; };
        expected = true;
      };
      "rejects-wrong-tag" = {
        expr =
          let e = Either.value FP.String FP.Int;
          in check e { _tag = "Other"; value = 42; };
        expected = false;
      };
      "kernel-propagates" = {
        expr = (Either.value FP.Int FP.Bool) ? kernelCheck;
        expected = true;
      };
      "kernelCheck-accepts-left" = {
        expr = (Either.value FP.Int FP.Bool).kernelCheck { _tag = "Left"; value = 42; };
        expected = true;
      };
      "kernelCheck-rejects-wrong-val" = {
        expr = (Either.value FP.Int FP.Bool).kernelCheck { _tag = "Left"; value = true; };
        expected = false;
      };
    };
  };

  Variant = mk {
    doc = ''
      Discriminated union. Takes `{ tag = Type; ... }` schema.
      Accepts `{ _tag = "tag"; value = ...; }` where value has the corresponding type.
    '';
    value = schema:
      let
        sortedTags = builtins.sort builtins.lessThan (builtins.attrNames schema);
        allHaveKernel = builtins.all (t: schema.${t} ? _kernel) sortedTags;
        hoasBranches = map (t: { tag = t; type = schema.${t}._kernel; }) sortedTags;
        kernelType = if allHaveKernel && sortedTags != []
          then H.variant hoasBranches
          else H.any;
        guard = v:
          builtins.isAttrs v
          && v ? _tag && v ? value
          && schema ? ${v._tag}
          && (schema.${v._tag}).check v.value;
      in mkType {
        name = "Variant{${builtins.concatStringsSep " | " sortedTags}}";
        inherit kernelType guard;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-valid-variant" = {
        expr =
          let
            Shape = Variant.value {
              circle = FP.Float;
              rect = FP.Attrs;
            };
          in check Shape { _tag = "circle"; value = 5.0; };
        expected = true;
      };
      "rejects-unknown-tag" = {
        expr =
          let
            Shape = Variant.value {
              circle = FP.Float;
            };
          in check Shape { _tag = "triangle"; value = null; };
        expected = false;
      };
      "has-kernelCheck" = {
        expr = (Variant.value { a = FP.Int; b = FP.Bool; }) ? kernelCheck;
        expected = true;
      };
    };
  };

in mk {
  doc = "Type constructors: Record, ListOf, Maybe, Either, Variant.";
  value = {
    inherit Record ListOf Maybe Either Variant;
  };
}
