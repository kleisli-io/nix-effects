# nix-effects type constructors
#
# Higher-kinded type constructors that build compound types from simpler ones.
# Guard and approximate decisions use orthogonal flags: _kernelPrecise
# (kernel faithfully represents structure) drives the approximate flag,
# _kernelSufficient (kernel alone decides membership) drives guard presence.
# Kernel building always uses children's _kernel regardless of flags.
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
        allPrecise = builtins.all (f: schema.${f}._kernelPrecise) sortedNames;
        allSufficient = builtins.all (f: schema.${f}._kernelSufficient) sortedNames;
        hoasFields = map (f: { name = f; type = schema.${f}._kernel; }) sortedNames;
        kernelType = if sortedNames != []
          then H.record hoasFields
          else H.any;
        guard = if allSufficient && sortedNames != []
          then null
          else v:
            builtins.isAttrs v
            && builtins.all (field:
              v ? ${field} && (schema.${field}).check v.${field}
            ) sortedNames;
      in mkType {
        name = "Record{${builtins.concatStringsSep ", " sortedNames}}";
        inherit kernelType guard;
        approximate = !(allPrecise && sortedNames != []);
        # Per-field effectful verify for blame tracking. Delegates to each
        # field type's .validate for recursive decomposition — a nested
        # Record or ListOf field produces deep per-component effects.
        verify = self: v:
          if !(builtins.isAttrs v) then
            send "typeCheck" { type = self; context = self.name; value = v; }
          else
            let
              n = builtins.length sortedNames;
              # Build chain right-to-left so effects fire in field-name order
              checkAll = builtins.foldl'
                (acc: i:
                  let field = builtins.elemAt sortedNames i; in
                  if !(v ? ${field}) then
                    bind (send "typeCheck" {
                      type = schema.${field};
                      context = "${self.name}.${field}";
                      value = null;
                    }) (_: acc)
                  else
                    bind (schema.${field}.validate v.${field}) (_: acc))
                (pure v)
                (builtins.genList (i: n - 1 - i) n);
            in if n == 0 then pure v else checkAll;
      };
    tests = let
      FP = fx.types.primitives;
    in {
      "accepts-matching-record" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "rejects-missing-field" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; };
        expected = false;
      };
      "rejects-wrong-type" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in check PersonT { name = "Alice"; age = "thirty"; };
        expected = false;
      };
      "allows-extra-fields" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
            };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "has-kernelCheck" = {
        expr = (Record { n = FP.Int; b = FP.Bool; }) ? kernelCheck;
        expected = true;
      };
      "exact-record-is-kernel-sufficient" = {
        expr = (Record { n = FP.Int; b = FP.Bool; })._kernelSufficient;
        expected = true;
      };
      # -- Per-field blame tracking --
      "verify-per-field-blame" = {
        expr =
          let
            PersonT = Record { n = FP.Int; s = FP.String; };
            result = fx.trampoline.handle {
              handlers = fx.effects.typecheck.collecting;
              state = [];
            } (PersonT.validate { n = "wrong"; s = 42; });
          in builtins.length result.state;
        expected = 2;
      };
      "verify-missing-field-blame" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            result = fx.trampoline.handle {
              handlers = fx.effects.typecheck.collecting;
              state = [];
            } (PersonT.validate {});
          in builtins.length result.state;
        expected = 1;
      };
      "verify-nested-decomposition" = {
        expr =
          let
            Inner = Record { x = FP.Int; };
            Outer = Record { inner = Inner; };
            result = fx.trampoline.handle {
              handlers = fx.effects.typecheck.collecting;
              state = [];
            } (Outer.validate { inner = { x = "bad"; }; });
          in builtins.length result.state;
        expected = 1;
      };
      # -- Composition soundness --
      "deep-maybe-record-listof-refined" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
            PersonT = Record { scores = ListOf Pos; name = FP.String; };
          in (Maybe PersonT).check { scores = [(-1)]; name = "x"; };
        expected = false;
      };
      "kernel-sufficient-propagation" = {
        expr =
          let T = Maybe (Record { items = ListOf (Either FP.Int FP.Bool); });
          in T._kernelSufficient;
        expected = true;
      };
      "refined-preserves-kernel-precise" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
            T = Maybe (Record { items = ListOf (Either Pos FP.Bool); });
          in T._kernelPrecise;
        expected = true;
      };
      "refined-kills-kernel-sufficient" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
            T = Maybe (Record { items = ListOf (Either Pos FP.Bool); });
          in T._kernelSufficient;
        expected = false;
      };
      "record-with-refined-field-has-kernelCheck" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
          in (Record { n = Pos; b = FP.Bool; }) ? kernelCheck;
        expected = true;
      };
      "chained-refinement-soundness" = {
        expr =
          let
            Pos = fx.types.foundation.refine FP.Int (x: x > 0);
            PosEven = fx.types.foundation.refine Pos (x: builtins.bitAnd x 1 == 0);
          in (Maybe PosEven).check (-2);
        expected = false;
      };
      "deep-blame-nested-record" = {
        expr =
          let
            Inner = Record { c = FP.Int; };
            Outer = Record { a = Record { b = Inner; }; };
            result = fx.trampoline.handle {
              handlers = fx.effects.typecheck.collecting;
              state = [];
            } (Outer.validate { a = { b = { c = "wrong"; }; }; });
          in builtins.length result.state;
        expected = 1;
      };
      # -- Adequacy: kernel-exact types have check == kernelCheck --
      "adequacy-record" = {
        expr =
          let T = Record { n = FP.Int; b = FP.Bool; };
          in T.check { n = 1; b = true; } == T.kernelCheck { n = 1; b = true; };
        expected = true;
      };
      "adequacy-record-negative" = {
        expr =
          let T = Record { n = FP.Int; b = FP.Bool; };
          in T.check { n = "x"; b = true; } == T.kernelCheck { n = "x"; b = true; };
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
        isPrecise = elemType._kernelPrecise;
        isSufficient = elemType._kernelSufficient;
        kernelType = H.listOf elemType._kernel;
        guard = if isSufficient then null
          else v: builtins.isList v && builtins.all elemType.check v;
      in mkType {
        name = "List[${elemType.name}]";
        inherit kernelType guard;
        approximate = !isPrecise;
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
          let intList = ListOf FP.Int;
          in check intList [1 2 3];
        expected = true;
      };
      "rejects-mixed-list" = {
        expr =
          let intList = ListOf FP.Int;
          in check intList [1 "two" 3];
        expected = false;
      };
      "accepts-empty-list" = {
        expr =
          let intList = ListOf FP.Int;
          in check intList [];
        expected = true;
      };
      "kernel-propagates" = {
        expr = (ListOf FP.Bool) ? kernelCheck;
        expected = true;
      };
      "kernelCheck-accepts" = {
        expr = (ListOf FP.Bool).kernelCheck [true false];
        expected = true;
      };
      "kernelCheck-rejects-bad-elem" = {
        expr = (ListOf FP.Bool).kernelCheck [42];
        expected = false;
      };
    };
  };

  Maybe = mk {
    doc = "Option type. Maybe Type accepts null or a value of Type.";
    value = innerType:
      let
        isPrecise = innerType._kernelPrecise;
        isSufficient = innerType._kernelSufficient;
        kernelType = H.maybe innerType._kernel;
        guard = if isSufficient then null
          else v: v == null || innerType.check v;
      in mkType {
        name = "Maybe[${innerType.name}]";
        inherit kernelType guard;
        approximate = !isPrecise;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-null" = {
        expr = check (Maybe FP.Int) null;
        expected = true;
      };
      "accepts-value" = {
        expr = check (Maybe FP.Int) 42;
        expected = true;
      };
      "rejects-wrong-type" = {
        expr = check (Maybe FP.Int) "hello";
        expected = false;
      };
      "has-kernelCheck" = {
        expr = (Maybe FP.Int) ? kernelCheck;
        expected = true;
      };
      # -- Soundness: refined types through Maybe --
      "soundness-maybe-refined-rejects" = {
        expr =
          let Nat = fx.types.refinement.refined "Nat" FP.Int (x: x >= 0);
          in (Maybe Nat).check (-1);
        expected = false;
      };
      "soundness-maybe-refined-accepts-null" = {
        expr =
          let Nat = fx.types.refinement.refined "Nat" FP.Int (x: x >= 0);
          in (Maybe Nat).check null;
        expected = true;
      };
      "soundness-maybe-refined-accepts-valid" = {
        expr =
          let Nat = fx.types.refinement.refined "Nat" FP.Int (x: x >= 0);
          in (Maybe Nat).check 5;
        expected = true;
      };
      "refined-not-kernel-sufficient" = {
        expr =
          let Nat = fx.types.refinement.refined "Nat" FP.Int (x: x >= 0);
          in Nat._kernelSufficient;
        expected = false;
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
        allPrecise = leftType._kernelPrecise && rightType._kernelPrecise;
        allSufficient = leftType._kernelSufficient && rightType._kernelSufficient;
        kernelType = H.sum leftType._kernel rightType._kernel;
        guard = if allSufficient then null
          else v:
            builtins.isAttrs v
            && v ? _tag && v ? value
            && ((v._tag == "Left" && leftType.check v.value)
                || (v._tag == "Right" && rightType.check v.value));
      in mkType {
        name = "Either[${leftType.name}, ${rightType.name}]";
        inherit kernelType guard;
        approximate = !allPrecise;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-left" = {
        expr =
          let e = Either FP.String FP.Int;
          in check e { _tag = "Left"; value = "error"; };
        expected = true;
      };
      "accepts-right" = {
        expr =
          let e = Either FP.String FP.Int;
          in check e { _tag = "Right"; value = 42; };
        expected = true;
      };
      "rejects-wrong-tag" = {
        expr =
          let e = Either FP.String FP.Int;
          in check e { _tag = "Other"; value = 42; };
        expected = false;
      };
      "kernel-propagates" = {
        expr = (Either FP.Int FP.Bool) ? kernelCheck;
        expected = true;
      };
      "kernelCheck-accepts-left" = {
        expr = (Either FP.Int FP.Bool).kernelCheck { _tag = "Left"; value = 42; };
        expected = true;
      };
      "kernelCheck-rejects-wrong-val" = {
        expr = (Either FP.Int FP.Bool).kernelCheck { _tag = "Left"; value = true; };
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
        allPrecise = builtins.all (t: schema.${t}._kernelPrecise) sortedTags;
        allSufficient = builtins.all (t: schema.${t}._kernelSufficient) sortedTags;
        hoasBranches = map (t: { tag = t; type = schema.${t}._kernel; }) sortedTags;
        kernelType = if sortedTags != []
          then H.variant hoasBranches
          else H.any;
        guard = if allSufficient && sortedTags != []
          then null
          else v:
            builtins.isAttrs v
            && v ? _tag && v ? value
            && schema ? ${v._tag}
            && (schema.${v._tag}).check v.value;
      in mkType {
        name = "Variant{${builtins.concatStringsSep " | " sortedTags}}";
        inherit kernelType guard;
        approximate = !(allPrecise && sortedTags != []);
        # Per-branch verify: only the active branch needs validation.
        # Delegates to the branch type's .validate for recursive decomposition.
        verify = self: v:
          if !(builtins.isAttrs v && v ? _tag && v ? value && schema ? ${v._tag}) then
            send "typeCheck" { type = self; context = self.name; value = v; }
          else
            schema.${v._tag}.validate v.value;
      };
    tests = let FP = fx.types.primitives; in {
      "accepts-valid-variant" = {
        expr =
          let
            Shape = Variant {
              circle = FP.Float;
              rect = FP.Attrs;
            };
          in check Shape { _tag = "circle"; value = 5.0; };
        expected = true;
      };
      "rejects-unknown-tag" = {
        expr =
          let
            Shape = Variant {
              circle = FP.Float;
            };
          in check Shape { _tag = "triangle"; value = null; };
        expected = false;
      };
      "has-kernelCheck" = {
        expr = (Variant { a = FP.Int; b = FP.Bool; }) ? kernelCheck;
        expected = true;
      };
      # -- Per-branch blame tracking --
      "verify-variant-active-branch" = {
        expr =
          let
            Shape = Variant { circle = FP.Float; rect = FP.Attrs; };
            result = fx.trampoline.handle {
              handlers = fx.effects.typecheck.collecting;
              state = [];
            } (Shape.validate { _tag = "circle"; value = "not-float"; });
          in builtins.length result.state;
        expected = 1;
      };
    };
  };

in mk {
  doc = "Type constructors: Record, ListOf, Maybe, Either, Variant.";
  value = {
    inherit Record ListOf Maybe Either Variant;
  };
}
