# nix-effects type constructors
#
# Higher-kinded type constructors that build compound types from simpler ones.
# Guard and approximate decisions use orthogonal flags: _kernelPrecise
# (kernel faithfully represents structure) drives the approximate flag,
# _kernelSufficient (kernel alone decides membership) drives guard presence.
# Kernel building always uses children's _kernel regardless of flags.
{ fx, api, ... }:
let
  inherit (fx.types.foundation) mkType check;
  inherit (fx.kernel) pure bind send;
  H = fx.tc.hoas;
  R = fx.tc.kernel.reflect;
  P = fx.diag.positions;

  # A Sum-carrier coproduct (variant/either) lives at the common universe
  # `kH = max(branch universes)`; each branch carrier is lifted there from its
  # own universe. `LiftAt u u A ≡ A`, so an all-U(0) compound is unchanged.
  maxUniverse = tys: builtins.foldl' (m: ty: if ty.universe > m then ty.universe else m) 0 tys;
  liftKernel = kH: ty: H._internal._indexed.LiftAt (H.natToLevel ty.universe) (H.natToLevel kH) ty._kernel;

  # Fuel-gated child descent; bounce onto the trampoline when fuel runs out.
  nativeWalkBudget = 512;
  descendV = t: fuel: p: x:
    if fuel <= 0
    then send "deriveBounce" { run = _: t.validateAtF nativeWalkBudget p x; }
    else t.validateAtF (fuel - 1) p x;
  shapeErr = self: path: v:
    send "typeCheck" { type = self; context = self.name; value = v; reason = "shape-mismatch"; inherit path; };

  # Shared Record/RecordOpen builder. `open` toggles whether undeclared
  # fields are silently ignored (true) or kernel-rejected (false). Verify
  # walks declared fields only either way — extras emit no blame.
  mkRecordType = { open }: schema:
    let
      sortedNames = builtins.sort builtins.lessThan (builtins.attrNames schema);
      allPrecise = builtins.all (f: schema.${f}._kernelPrecise) sortedNames;
      allSufficient = builtins.all (f: schema.${f}._kernelSufficient) sortedNames;
      typeName =
        let prefix = if open then "RecordOpen" else "Record"; in
        "${prefix}{${builtins.concatStringsSep ", " sortedNames}}";
      # The carrier lives at the common universe kH = max(field universes);
      # each field is declared at its own universe and conDesc lifts it to kH.
      # An all-U(0) record is byte-identical (fieldAt 0 ≡ field, datatypeAt
      # name 0 ≡ datatype name).
      kH = maxUniverse (map (f: schema.${f}) sortedNames);
      datatypeFields = map (f: H.fieldAt schema.${f}.universe f schema.${f}._kernel) sortedNames;
      recSpec = H._internal._indexed.datatypeAt typeName kH [ (H.con "mk" datatypeFields) ];
      baseKernel = recSpec.T;
      kernelType =
        if open
        then baseKernel // {
          _dtypeMeta = baseKernel._dtypeMeta // { openExtras = true; };
        }
        else baseKernel;
      hostGuard = v:
        builtins.isAttrs v
        && builtins.all
          (field:
            v ? ${field} && (schema.${field}).check v.${field}
          )
          sortedNames;
      # Records internalize as a single descCata fold over the declared-field
      # description when every field's refinement is kernel-decidable. The fold
      # is identical open or closed; the carrier's openExtras flag makes the
      # bridge drop undeclared fields before the fold sees them, so an open
      # record decides exactly its declared fields and ignores the rest.
      structuralKP = R.mkCompoundPred {
        carrier = kernelType;
        D = recSpec.D;
        childKts = map (f: schema.${f}.ktype or null) sortedNames;
      };
      guard =
        if allSufficient then null
        else if structuralKP != null then structuralKP
        else hostGuard;
    in
    mkType {
      name = typeName;
      inherit kernelType guard;
      approximate = !allPrecise;
      # Descend each declared field through its own validateAtF so a refined
      # field's guard is authoritative. Extras unblamed (closed .check rejects).
      verify = self: fuel: path: v:
        if !builtins.isAttrs v then shapeErr self path v
        else
          let
            step = acc: fname:
              bind acc (_:
                let
                  childPath = path ++ [ (P.Field fname) ];
                  childType = schema.${fname};
                in
                if !(v ? ${fname})
                then send "typeCheck" { type = childType; context = fname; value = null; reason = "missing-field"; path = childPath; }
                else descendV childType fuel childPath v.${fname});
          in
          bind (builtins.foldl' step (pure null) sortedNames) (_: pure v);
    };

  Record = mkRecordType { open = false; };
  RecordTests =
    let
      FP = fx.types.primitives;
      U = fx.types.universe;
    in
    {
      "accepts-matching-record" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in
          check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "rejects-missing-field" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in
          check PersonT { name = "Alice"; };
        expected = false;
      };
      "rejects-wrong-type" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
              age = FP.Int;
            };
          in
          check PersonT { name = "Alice"; age = "thirty"; };
        expected = false;
      };
      "rejects-extra-fields" = {
        expr =
          let
            PersonT = Record {
              name = FP.String;
            };
          in
          check PersonT { name = "Alice"; age = 30; };
        expected = false;
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
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (PersonT.validate { n = "wrong"; s = 42; });
          in
          builtins.length result.state;
        expected = 2;
      };
      "verify-missing-field-blame" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (PersonT.validate { });
          in
          builtins.length result.state;
        expected = 1;
      };
      "verify-nested-decomposition" = {
        expr =
          let
            Inner = Record { x = FP.Int; };
            Outer = Record { inner = Inner; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (Outer.validate { inner = { x = "bad"; }; });
          in
          builtins.length result.state;
        expected = 1;
      };
      # -- Composition soundness --
      "deep-maybe-record-listof-refined" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
            PersonT = Record { scores = ListOf Pos; name = FP.String; };
          in
          (Maybe PersonT).check { scores = [ (-1) ]; name = "x"; };
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
          in
          T._kernelPrecise;
        expected = true;
      };
      "refined-kills-kernel-sufficient" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
            T = Maybe (Record { items = ListOf (Either Pos FP.Bool); });
          in
          T._kernelSufficient;
        expected = false;
      };
      "record-with-refined-field-has-kernelCheck" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int (x: x > 0);
          in
          (Record { n = Pos; b = FP.Bool; }) ? kernelCheck;
        expected = true;
      };
      "chained-refinement-soundness" = {
        expr =
          let
            Pos = fx.types.foundation.refine FP.Int (x: x > 0);
            PosEven = fx.types.foundation.refine Pos (x: builtins.bitAnd x 1 == 0);
          in
          (Maybe PosEven).check (-2);
        expected = false;
      };
      "deep-blame-nested-record" = {
        expr =
          let
            Inner = Record { c = FP.Int; };
            Outer = Record { a = Record { b = Inner; }; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (Outer.validate { a = { b = { c = "wrong"; }; }; });
          in
          builtins.length result.state;
        expected = 1;
      };
      "deep-blame-nested-record-path" = {
        expr =
          let
            Inner = Record { c = FP.Int; };
            Outer = Record { a = Record { b = Inner; }; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (Outer.validate { a = { b = { c = "wrong"; }; }; });
          in
          (builtins.head result.state).path;
        expected = [ (P.Field "a") (P.Field "b") (P.Field "c") ];
      };
      "verify-per-field-blame-paths" = {
        expr =
          let
            PersonT = Record { n = FP.Int; s = FP.String; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (PersonT.validate { n = "wrong"; s = 42; });
          in
          map (e: e.path) result.state;
        # Field order is sorted (n, s)
        expected = [ [ (P.Field "n") ] [ (P.Field "s") ] ];
      };
      "verify-missing-field-has-path" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.collecting;
                state = [ ];
              }
              (PersonT.validate { });
          in
          (builtins.head result.state).path;
        expected = [ (P.Field "n") ];
      };
      # -- Position threading --
      "verify-wrong-shape-path-is-empty-at-root" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            comp = PersonT.validate 42;
          in
          comp.effect.param.path;
        expected = [ ];
      };
      "verify-missing-field-has-Field-position" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            comp = PersonT.validate { };
          in
          map (p: p.tag) comp.effect.param.path;
        expected = [ "Field" ];
      };
      "verify-missing-field-position-carries-field-name" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            comp = PersonT.validate { };
          in
          (builtins.elemAt comp.effect.param.path 0).name;
        expected = "n";
      };
      "verify-bad-field-threads-path-through-primitive" = {
        expr =
          let
            PersonT = Record { n = FP.Int; };
            comp = PersonT.validate { n = "wrong"; };
            pos = comp.effect.param.path;
          in
          {
            length = builtins.length pos;
            tag = (builtins.elemAt pos 0).tag;
            name = (builtins.elemAt pos 0).name;
          };
        expected = { length = 1; tag = "Field"; name = "n"; };
      };
      "verify-nested-record-threads-two-Field-positions" = {
        expr =
          let
            Inner = Record { x = FP.Int; };
            Outer = Record { y = Inner; };
            comp = Outer.validate { y = { x = "wrong"; }; };
          in
          map (p: p.name) comp.effect.param.path;
        expected = [ "y" "x" ];
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
      # -- Description-backed kernel: datatypeInfo surfaces the schema --
      "datatypeInfo-on-record-surfaces-schema" = {
        expr =
          let
            T = Record { a = FP.Int; b = FP.Bool; };
            info = fx.tc.generic.datatype.datatypeInfo T._kernel;
            con = builtins.head info.constructors;
          in
          {
            n = builtins.length info.constructors;
            con = con.name;
            fields = map (f: f.name) con.fields;
          };
        expected = {
          n = 1;
          con = "mk";
          fields = [ "a" "b" ];
        };
      };
      # -- Universe-polymorphic field (lifted to U(k>0)): the generic walker
      # descends through the field's `LiftAt` node, so a lifted field decides
      # exactly like its base; an unlifted field is the control. The Record
      # carrier itself stays at U(0) (a lifted field does not raise the record's
      # universe), and that U(0) kernel is well-formed (the elaborate fold
      # re-wraps the inhabitant in `liftAt`). --
      "lifted-field-accepts" = {
        expr = (Record { x = U.liftTo 2 FP.Int; }).check { x = 5; };
        expected = true;
      };
      "lifted-field-rejects-wrong" = {
        expr = (Record { x = U.liftTo 2 FP.Int; }).check { x = "no"; };
        expected = false;
      };
      "lifted-field-unlifted-control" = {
        expr = (Record { x = FP.Int; }).check { x = 5; };
        expected = true;
      };
      # The carrier of a record with a U(2) field lives at U(2): the kernel
      # is universe-coherent with the field's level (non-cumulative — not U(0)).
      "lifted-field-kernel-wellformed-at-u2" = {
        expr = (H.checkHoas (H.u 2) (Record { x = U.liftTo 2 FP.Int; })._kernel) ? error;
        expected = false;
      };
      "lifted-field-kernel-not-at-u0" = {
        expr = (H.checkHoas (H.u 0) (Record { x = U.liftTo 2 FP.Int; })._kernel) ? error;
        expected = true;
      };
      "lifted-field-raises-universe" = {
        expr = (Record { x = U.liftTo 2 FP.Int; }).universe;
        expected = 2;
      };
      "mixed-level-fields-take-max-universe" = {
        expr = (Record { x = U.liftTo 2 FP.Int; y = FP.Int; }).universe;
        expected = 2;
      };
      "all-base-fields-stay-universe-0" = {
        expr = (Record { x = FP.Int; y = FP.Bool; }).universe;
        expected = 0;
      };
      "nested-lifted-field-propagates-universe" = {
        expr = (Record { inner = Record { x = U.liftTo 2 FP.Int; }; }).universe;
        expected = 2;
      };
      "lifted-record-is-member-at-target-universe" = {
        expr = check (U.typeAt 2) (Record { x = U.liftTo 2 FP.Int; });
        expected = true;
      };
      "lifted-record-not-member-below-noncumulative" = {
        expr = check (U.typeAt 0) (Record { x = U.liftTo 2 FP.Int; });
        expected = false;
      };
    };

  RecordOpen = mkRecordType { open = true; };
  RecordOpenTests =
    let
      FP = fx.types.primitives;
    in
    {
      "accepts-matching-record" = {
        expr =
          let PersonT = RecordOpen { name = FP.String; age = FP.Int; };
          in check PersonT { name = "Alice"; age = 30; };
        expected = true;
      };
      "accepts-extra-fields" = {
        expr =
          let PersonT = RecordOpen { name = FP.String; };
          in check PersonT { name = "Alice"; age = 30; nickname = "Al"; };
        expected = true;
      };
      "rejects-missing-field" = {
        expr =
          let PersonT = RecordOpen { name = FP.String; age = FP.Int; };
          in check PersonT { name = "Alice"; };
        expected = false;
      };
      "rejects-wrong-type" = {
        expr =
          let PersonT = RecordOpen { name = FP.String; age = FP.Int; };
          in check PersonT { name = "Alice"; age = "thirty"; };
        expected = false;
      };
      "rejects-non-attrs" = {
        expr =
          let PersonT = RecordOpen { name = FP.String; };
          in check PersonT 42;
        expected = false;
      };
      # A kernel-expressible refined field internalizes the open .check: the
      # carrier's openExtras flag drops undeclared fields at the bridge, so the
      # structural fold decides exactly the declared fields.
      "refined-field-internalizes" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int fx.tc.kernel.reflect.intPositive;
          in
          (RecordOpen { age = Pos; }) ? kernelCheck
          && (RecordOpen { age = Pos; })._kernelPred != null;
        expected = true;
      };
      "refined-field-accepts-with-extras" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int fx.tc.kernel.reflect.intPositive;
          in
          check (RecordOpen { age = Pos; }) { age = 5; nickname = "Al"; };
        expected = true;
      };
      "refined-field-rejects-bad-refinement-with-extras" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int fx.tc.kernel.reflect.intPositive;
          in
          check (RecordOpen { age = Pos; }) { age = 0; nickname = "Al"; };
        expected = false;
      };
      "refined-field-rejects-missing" = {
        expr =
          let
            Pos = fx.types.refinement.refined "Pos" FP.Int fx.tc.kernel.reflect.intPositive;
          in
          check (RecordOpen { age = Pos; }) { nickname = "Al"; };
        expected = false;
      };
      # A raw-lambda refinement is not kernel-expressible, so the open record
      # falls back to its host guard and still decides declared fields.
      "rawlambda-refined-field-keeps-host-guard" = {
        expr =
          let
            RawPos = fx.types.refinement.refined "P" FP.Int (x: x > 0);
            T = RecordOpen { age = RawPos; };
          in
          T._kernelPred == null
          && check T { age = 5; nickname = "x"; }
          && !(check T { age = 0; nickname = "x"; });
        expected = true;
      };
    };

  ListOf = elemType:
    let
      isPrecise = elemType._kernelPrecise;
      isSufficient = elemType._kernelSufficient;
      # Carry the element's universe so a lifted element type (U(m), m>0)
      # forms a well-typed `List` at that level rather than being forced to U(0).
      kH = H.natToLevel elemType.universe;
      kernelType = H.listOfAt kH elemType._kernel;
      # A mono nil/cons mirror gives the fold a concrete (host-walkable) carrier
      # description; its `.T` is convertible with the native `listOf` carrier.
      listMono = H.datatype "List[${elemType.name}]" [
        (H.con "nil" [ ])
        (H.con "cons" [ (H.fieldAt kH "head" elemType._kernel) (H.recField "tail") ])
      ];
      structuralKP =
        if (elemType.ktype or null) == null then null
        else R.mkCompoundPred {
          carrier = kernelType;
          D = listMono.D;
          childKts = [ elemType.ktype ];
        };
      guard =
        if isSufficient then null
        else if structuralKP != null then structuralKP
        else v: builtins.isList v && builtins.all elemType.check v;
    in
    mkType {
      name = "List[${elemType.name}]";
      inherit kernelType guard;
      approximate = !isPrecise;
      # Descend each element through elemType.validateAtF so a refined element's
      # guard is authoritative.
      verify = self: fuel: path: v:
        if !builtins.isList v then shapeErr self path v
        else
          let
            n = builtins.length v;
            indices = builtins.genList (i: i) n;
            step = acc: i:
              bind acc (_: descendV elemType fuel (path ++ [ (P.Elem i) ]) (builtins.elemAt v i));
          in
          bind (builtins.foldl' step (pure null) indices) (_: pure v);
    };
  ListOfTests = let FP = fx.types.primitives; U = fx.types.universe; in {
    "accepts-matching-list" = {
      expr =
        let intList = ListOf FP.Int;
        in check intList [ 1 2 3 ];
      expected = true;
    };
    "rejects-mixed-list" = {
      expr =
        let intList = ListOf FP.Int;
        in check intList [ 1 "two" 3 ];
      expected = false;
    };
    "accepts-empty-list" = {
      expr =
        let intList = ListOf FP.Int;
        in check intList [ ];
      expected = true;
    };
    "kernel-propagates" = {
      expr = (ListOf FP.Bool) ? kernelCheck;
      expected = true;
    };
    "kernelCheck-accepts" = {
      expr = (ListOf FP.Bool).kernelCheck [ true false ];
      expected = true;
    };
    "kernelCheck-rejects-bad-elem" = {
      expr = (ListOf FP.Bool).kernelCheck [ 42 ];
      expected = false;
    };
    # -- Description-backed kernel: datatypeInfo surfaces nil/cons --
    "datatypeInfo-on-listof-surfaces-list-constructors" = {
      expr =
        let
          T = ListOf FP.Int;
          info = fx.tc.generic.datatype.datatypeInfo T._kernel;
        in
        {
          name = info.name;
          params = builtins.length info.params;
          args = builtins.length info.paramArgs;
          constructors = map (c: c.name) info.constructors;
        };
      expected = {
        name = "List";
        params = 2;
        args = 2;
        constructors = [ "nil" "cons" ];
      };
    };
    # -- Per-element blame with paths --
    "listof-primitive-blames-by-index" = {
      expr =
        let
          intList = ListOf FP.Int;
          result = fx.trampoline.handle
            {
              handlers = fx.effects.typecheck.collecting;
              state = [ ];
            }
            (intList.validate [ 1 "two" 3 "four" ]);
        in
        map (e: e.path) result.state;
      expected = [ [ (P.Elem 1) ] [ (P.Elem 3) ] ];
    };
    "listof-record-decomposes-into-per-field-blame" = {
      expr =
        let
          Iface = Record { name = FP.String; mtu = FP.Int; };
          ifaces = ListOf Iface;
          result = fx.trampoline.handle
            {
              handlers = fx.effects.typecheck.collecting;
              state = [ ];
            }
            (ifaces.validate [
              { name = "eth0"; mtu = 1500; }
              { name = 42; mtu = "bad"; }
            ]);
        in
        map (e: e.path) result.state;
      # Element 1 has two bad fields; they appear in sorted field order
      # (mtu, name). Element 0 passes cleanly.
      expected = [
        [ (P.Elem 1) (P.Field "mtu") ]
        [ (P.Elem 1) (P.Field "name") ]
      ];
    };
    # -- Elem-tagged Position threading --
    "listof-element-carries-Elem-position" = {
      expr =
        let
          intList = ListOf FP.Int;
          comp = intList.validate [ "bad" ];
          pos = comp.effect.param.path;
        in
        {
          length = builtins.length pos;
          tag = (builtins.elemAt pos 0).tag;
          idx = (builtins.elemAt pos 0).idx;
        };
      expected = { length = 1; tag = "Elem"; idx = 0; };
    };
    "listof-of-record-threads-Elem-then-Field" = {
      expr =
        let
          Iface = Record { name = FP.String; };
          ifaces = ListOf Iface;
          comp = ifaces.validate [{ name = 42; }];
        in
        map (p: p.tag) comp.effect.param.path;
      expected = [ "Elem" "Field" ];
    };
    # -- Universe-polymorphic element (lifted to U(k>0)): the List carrier is
    # built at the element's universe, so a higher-universe element type yields
    # a well-typed list carrier; at U(0) it is the old monomorphic List. --
    "lifted-element-accepts" = {
      expr = (ListOf (U.liftTo 2 FP.Int)).check [ 1 2 3 ];
      expected = true;
    };
    "lifted-element-accepts-empty" = {
      expr = (ListOf (U.liftTo 2 FP.Int)).check [ ];
      expected = true;
    };
    "lifted-element-rejects-wrong" = {
      expr = (ListOf (U.liftTo 2 FP.Int)).check [ 1 "two" ];
      expected = false;
    };
    "lifted-element-universe-rises" = {
      expr = (ListOf (U.liftTo 2 FP.Int)).universe;
      expected = 2;
    };
  };

  Maybe = innerType:
    let
      isPrecise = innerType._kernelPrecise;
      isSufficient = innerType._kernelSufficient;
      # `maybeAt k` puts the optional carrier at the inner's own universe, so a
      # higher-universe inner (e.g. a lifted type) yields a well-typed carrier;
      # at U(0) it is the old `Sum inner Unit`.
      kernelType = H.maybeAt innerType.universe innerType._kernel;
      hostGuard = v: v == null || innerType.check v;
      # `maybe` is `Sum inner Unit`; internalize as a `sumElim` deciding the
      # present value, accepting absence, when the inner is kernel-decidable.
      # The structural predicate only ever decides a U(0) inner: a guarded
      # higher-universe inner has no kernel `ktype` (innerKt null ⇒ host guard),
      # and a kernel-sufficient inner makes the whole Maybe sufficient
      # (guard null ⇒ this predicate is discarded). Both stay sound.
      structuralKP = R.mkMaybePred {
        carrier = kernelType;
        inner = innerType._kernel;
        innerKt = innerType.ktype or null;
      };
      guard =
        if isSufficient then null
        else if structuralKP != null then structuralKP
        else hostGuard;
    in
    mkType {
      name = "Maybe[${innerType.name}]";
      inherit kernelType guard;
      approximate = !isPrecise;
    };
  MaybeTests = let FP = fx.types.primitives; U = fx.types.universe; in {
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
    # -- Universe-polymorphic inner (lifted to U(k>0)): the carrier is built at
    # the inner's universe so it stays well-typed; checks behave like U(0). --
    "lifted-inner-accepts-value" = {
      expr = (Maybe (U.liftTo 2 FP.Int)).check 5;
      expected = true;
    };
    "lifted-inner-accepts-null" = {
      expr = (Maybe (U.liftTo 2 FP.Int)).check null;
      expected = true;
    };
    "lifted-inner-rejects-wrong" = {
      expr = (Maybe (U.liftTo 2 FP.Int)).check "x";
      expected = false;
    };
    "lifted-inner-universe-rises" = {
      expr = (Maybe (U.liftTo 2 FP.Int)).universe;
      expected = 2;
    };
    # Non-cumulative guard: the lifted carrier lives at U(2), not U(0).
    "lifted-inner-kernel-not-at-u0" = {
      expr = (H.checkHoas (H.u 0) (Maybe (U.liftTo 2 FP.Int))._kernel) ? error;
      expected = true;
    };
    "lifted-inner-kernel-at-u2" = {
      expr = (H.checkHoas (H.u 2) (Maybe (U.liftTo 2 FP.Int))._kernel) ? error;
      expected = false;
    };
  };

  Either = leftType: rightType:
    let
      allPrecise = leftType._kernelPrecise && rightType._kernelPrecise;
      allSufficient = leftType._kernelSufficient && rightType._kernelSufficient;
      # First-class kernel variant: `Pos.Tag "Left"`/`Pos.Tag "Right"`
      # are the leaf branch coordinates; payload descent delegates to
      # the branch type's walker. No synthetic `Pos.Field "value"`
      # leaks into blame paths — the kernel knows about Either as a
      # 2-tag variant rather than a μ-encoded SumDT.
      kH = maxUniverse [ leftType rightType ];
      kernelType = H.variantAt kH [
        { tag = "Left"; type = liftKernel kH leftType; }
        { tag = "Right"; type = liftKernel kH rightType; }
      ];
      hostGuard = v:
        builtins.isAttrs v
        && v ? _tag && v ? value
        && ((v._tag == "Left" && leftType.check v.value)
        || (v._tag == "Right" && rightType.check v.value));
      # Internalize as a nested `sumElim` over the native variant carrier when
      # both branches are kernel-decidable; branch order matches `kernelType`.
      # Restricted to an all-U(0) coproduct: the kernel reflects branch carriers
      # only at U(0), so a higher-universe branch keeps the (always-sound) host
      # guard rather than a lifted decision the kernel cannot soundly express.
      structuralKP =
        if kH != 0 then null
        else R.mkVariantPred {
          carrier = kernelType;
          branches = [
            { type = leftType._kernel; kt = leftType.ktype or null; }
            { type = rightType._kernel; kt = rightType.ktype or null; }
          ];
        };
      guard =
        if allSufficient then null
        else if structuralKP != null then structuralKP
        else hostGuard;
    in
    mkType {
      name = "Either[${leftType.name}, ${rightType.name}]";
      inherit kernelType guard;
      approximate = !allPrecise;
      # Descend the active branch through its own validateAtF so a refined
      # branch's guard is authoritative.
      verify = self: fuel: path: v:
        if !(builtins.isAttrs v && v ? _tag && v ? value) then shapeErr self path v
        else if v._tag == "Left" then descendV leftType fuel (path ++ [ (P.Tag "Left") ]) v.value
        else if v._tag == "Right" then descendV rightType fuel (path ++ [ (P.Tag "Right") ]) v.value
        else shapeErr self path v;
    };
  EitherTests = let FP = fx.types.primitives; U = fx.types.universe; in {
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
    # -- Mixed-universe branches: lifted to the common max so the coproduct
    # carrier is well-typed; both tags still decide via the host guard. --
    "lifted-accepts-left" = {
      expr = (Either (U.liftTo 2 FP.Int) FP.Int).check { _tag = "Left"; value = 5; };
      expected = true;
    };
    "lifted-accepts-right" = {
      expr = (Either (U.liftTo 2 FP.Int) FP.Int).check { _tag = "Right"; value = 9; };
      expected = true;
    };
    "lifted-rejects-wrong-payload" = {
      expr = (Either (U.liftTo 2 FP.Int) FP.Int).check { _tag = "Left"; value = "x"; };
      expected = false;
    };
    "lifted-universe-rises" = {
      expr = (Either (U.liftTo 2 FP.Int) FP.Int).universe;
      expected = 2;
    };
  };

  Variant = schema:
    let
      sortedTags = builtins.sort builtins.lessThan (builtins.attrNames schema);
      allPrecise = builtins.all (t: schema.${t}._kernelPrecise) sortedTags;
      allSufficient = builtins.all (t: schema.${t}._kernelSufficient) sortedTags;
      typeName = "Variant{${builtins.concatStringsSep " | " sortedTags}}";
      # First-class kernel variant: `{_htag = "variant"; branches}`.
      # Walker dispatches via `_tag`, emits `Pos.Tag t` as the leaf
      # branch coordinate, delegates payload descent to the branch
      # type's own walker. No synthetic `Pos.Field "value"` ever
      # appears in the blame path — the kernel is honest about
      # variants without going through a μ-encoding.
      kH = maxUniverse (map (t: schema.${t}) sortedTags);
      kernelType =
        if sortedTags != [ ]
        then
          H.variantAt kH
            (map (t: { tag = t; type = liftKernel kH schema.${t}; }) sortedTags)
        else H.any;
      hostGuard = v:
        builtins.isAttrs v
        && v ? _tag && v ? value
        && schema ? ${v._tag}
        && (schema.${v._tag}).check v.value;
      # Internalize as a nested `sumElim` over the native variant carrier when
      # every branch is kernel-decidable; branch order matches `kernelType`.
      # Restricted to an all-U(0) coproduct (see `Either`): a higher-universe
      # branch keeps the host guard.
      structuralKP =
        if sortedTags == [ ] || kH != 0 then null
        else R.mkVariantPred {
          carrier = kernelType;
          branches = map (t: { type = schema.${t}._kernel; kt = schema.${t}.ktype or null; }) sortedTags;
        };
      guard =
        if allSufficient && sortedTags != [ ]
        then null
        else if structuralKP != null then structuralKP
        else hostGuard;
    in
    mkType {
      name = typeName;
      inherit kernelType guard;
      approximate = !(allPrecise && sortedTags != [ ]);
      # Descend the active branch through its own validateAtF; unknown tag is a
      # shape mismatch.
      verify = self: fuel: path: v:
        if !(builtins.isAttrs v && v ? _tag && v ? value) then shapeErr self path v
        else if schema ? ${v._tag} then descendV schema.${v._tag} fuel (path ++ [ (P.Tag v._tag) ]) v.value
        else shapeErr self path v;
    };
  VariantTests = let FP = fx.types.primitives; U = fx.types.universe; in {
    "accepts-valid-variant" = {
      expr =
        let
          Shape = Variant {
            circle = FP.Float;
            rect = FP.Attrs;
          };
        in
        check Shape { _tag = "circle"; value = 5.0; };
      expected = true;
    };
    "rejects-unknown-tag" = {
      expr =
        let
          Shape = Variant {
            circle = FP.Float;
          };
        in
        check Shape { _tag = "triangle"; value = null; };
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
          result = fx.trampoline.handle
            {
              handlers = fx.effects.typecheck.collecting;
              state = [ ];
            }
            (Shape.validate { _tag = "circle"; value = "not-float"; });
        in
        builtins.length result.state;
      expected = 1;
    };
    "verify-variant-active-branch-path" = {
      expr =
        let
          Shape = Variant { circle = FP.Float; rect = FP.Attrs; };
          result = fx.trampoline.handle
            {
              handlers = fx.effects.typecheck.collecting;
              state = [ ];
            }
            (Shape.validate { _tag = "circle"; value = "not-float"; });
        in
        (builtins.head result.state).path;
      expected = [ (P.Tag "circle") ];
    };
    # -- Tag-tagged Position threading --
    "verify-variant-active-branch-carries-Tag-position" = {
      expr =
        let
          Shape = Variant { circle = FP.Float; };
          comp = Shape.validate { _tag = "circle"; value = "not-float"; };
          pos = comp.effect.param.path;
        in
        {
          length = builtins.length pos;
          tag = (builtins.elemAt pos 0).tag;
          name = (builtins.elemAt pos 0).name;
        };
      expected = { length = 1; tag = "Tag"; name = "circle"; };
    };
    "verify-variant-of-record-threads-Tag-then-Field" = {
      expr =
        let
          Inner = Record { x = FP.Int; };
          V = Variant { some = Inner; };
          comp = V.validate { _tag = "some"; value = { x = "bad"; }; };
        in
        map (p: p.tag) comp.effect.param.path;
      expected = [ "Tag" "Field" ];
    };
    # -- Universe-polymorphic branches: each branch carrier lifts to the common
    # max so the nested coproduct is well-typed; homogeneous and mixed both
    # decide via the (always-sound) host guard for k>0. --
    "lifted-homogeneous-accepts" = {
      expr = (Variant { a = U.liftTo 2 FP.Int; b = U.liftTo 2 FP.Int; }).check { _tag = "a"; value = 3; };
      expected = true;
    };
    "lifted-mixed-accepts-high-branch" = {
      expr = (Variant { a = U.liftTo 2 FP.Int; b = FP.Int; }).check { _tag = "a"; value = 3; };
      expected = true;
    };
    "lifted-mixed-accepts-low-branch" = {
      expr = (Variant { a = U.liftTo 2 FP.Int; b = FP.Int; }).check { _tag = "b"; value = 7; };
      expected = true;
    };
    "lifted-rejects-wrong-payload" = {
      expr = (Variant { a = U.liftTo 2 FP.Int; b = FP.Int; }).check { _tag = "a"; value = "x"; };
      expected = false;
    };
    "lifted-universe-rises" = {
      expr = (Variant { a = U.liftTo 2 FP.Int; b = FP.Int; }).universe;
      expected = 2;
    };
    # All-U(0) variant stays kernel-internalized (refinement branches decided
    # in-kernel) — regression guard for the U(0)-only structural predicate.
    "u0-refinement-variant-internalized" = {
      expr =
        let
          PosInt = fx.types.foundation.mkType { name = "PosInt"; kernelType = H.int_; guard = R.intPositive; };
        in (Variant { a = PosInt; b = FP.Int; }).ktype != null;
      expected = true;
    };
  };

in
api.namespace {
  description = "Type constructors: Record/RecordOpen/ListOf/Maybe/Either/Variant — higher-kinded builders composing simpler types with per-component blame.";
  doc = "Type constructors: Record, RecordOpen, ListOf, Maybe, Either, Variant.";
  value = {
    Record = api.leaf {
      value = Record;
      description = "Record: closed record type constructor; `Record { f = T; ... }` checks that values carry exactly the declared fields with matching types and rejects extras.";
      signature = "Record : { <field> = Type; ... } -> Type";
      doc = ''
        Closed record type constructor. Takes a schema `{ field = Type; ... }`
        and checks that a value has exactly the declared fields with correct
        types. Unknown fields are rejected — for open semantics use `RecordOpen`.

        Verify is per-field and emits one `typeCheck` effect per blamed field,
        threading a `Field name` Position so handlers can recover the structural
        path.
      '';
      tests = RecordTests;
    };
    RecordOpen = api.leaf {
      value = RecordOpen;
      description = "RecordOpen: open-record type constructor; like `Record` but undeclared fields are accepted untouched, useful for records carrying optional metadata slots.";
      signature = "RecordOpen : { <field> = Type; ... } -> Type";
      doc = ''
        Open record type constructor. Like `Record`, but undeclared fields are
        permitted (and ignored by kernel and verify). Use for types whose
        values carry intentional metadata slots beyond the declared schema —
        e.g. build steps with optional `tools` / `env` / `when` annotations.

        The kernel datatype tags `openExtras = true` in `_dtypeMeta` so
        downstream type-directed walks know to allow them.
      '';
      tests = RecordOpenTests;
    };
    ListOf = api.leaf {
      value = ListOf;
      description = "ListOf: homogeneous list type constructor; `ListOf T` checks every element has type `T`, blames per-index, never short-circuits — handler picks error policy.";
      signature = "ListOf : Type -> Type";
      doc = ''
        Homogeneous list type. `ListOf Type` checks that all elements have the given type.

        Custom verifier sends per-element `typeCheck` effects with indexed context
        strings (e.g. `List[Int][2]`) for blame tracking. Unlike Sigma, elements
        are independent — no short-circuit. All elements are checked; the handler
        decides error policy (strict aborts on first, collecting gathers all).
      '';
      tests = ListOfTests;
    };
    Maybe = api.leaf {
      value = Maybe;
      description = "Maybe: option type constructor; `Maybe T` accepts null or any value of type `T`; kernel precision and sufficiency inherit from the inner type.";
      signature = "Maybe : Type -> Type";
      doc = "Option type. Maybe Type accepts null or a value of Type.";
      tests = MaybeTests;
    };
    Either = api.leaf {
      value = Either;
      description = "Either: tagged sum type constructor; `Either L R` accepts `{ _tag = \"Left\"; value : L }` or `{ _tag = \"Right\"; value : R }`.";
      signature = "Either : Type -> Type -> Type";
      doc = ''
        Tagged union of two types. Accepts `{ _tag = "Left"; value = a; }`
        or `{ _tag = "Right"; value = b; }`.
      '';
      tests = EitherTests;
    };
    Variant = api.leaf {
      value = Variant;
      description = "Variant: discriminated-union type constructor; `Variant { tag = T; ... }` accepts `{ _tag = name; value }` checked against the named branch.";
      signature = "Variant : { <tag> = Type; ... } -> Type";
      doc = ''
        Discriminated union. Takes `{ tag = Type; ... }` schema.
        Accepts `{ _tag = "tag"; value = ...; }` where value has the corresponding type.
      '';
      tests = VariantTests;
    };

  };
}
