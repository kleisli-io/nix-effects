{ lib, fx }:

let
  inherit (fx.types) Int String Bool Float Path Null Unit Any Record mkType defEq;
  refined = fx.types.refined;
  sug = fx.sugar.types;

  primitives = [ Int String Bool Float Path Null Unit Any ];
  sugPrimitives = [ sug.Int sug.String sug.Bool sug.Float sug.Path sug.Null sug.Unit sug.Any ];
  allIndex = f: builtins.all f (lib.range 0 (builtins.length primitives - 1));

  additiveOnlyPrimitives = {
    expr = allIndex (i:
      let
        orig = builtins.elemAt primitives i;
        sug' = builtins.elemAt sugPrimitives i;
        origKeys = builtins.attrNames orig;
        sugKeys = builtins.attrNames sug';
        preserved = builtins.all (k: builtins.elem k sugKeys) origKeys;
        new = lib.subtractLists origKeys sugKeys;
      in
      preserved
      && builtins.length new == 2
      && builtins.elem "__functor" new
      && builtins.elem "__toString" new);
    expected = true;
  };

  additiveOnlyRefined = {
    expr =
      let
        p = x: x > 0;
        base = refined "Int?" Int p;
        wrapped = sug.Int p;
        baseKeys = builtins.attrNames base;
        wrappedKeys = builtins.attrNames wrapped;
        preserved = builtins.all (k: builtins.elem k wrappedKeys) baseKeys;
        new = lib.subtractLists baseKeys wrappedKeys;
      in
      preserved
      && builtins.length new == 2
      && builtins.elem "__functor" new
      && builtins.elem "__toString" new;
    expected = true;
  };

  kernelDelegation = {
    expr = allIndex (i:
      let
        orig = builtins.elemAt primitives i;
        sug' = builtins.elemAt sugPrimitives i;
        p = x: true;
        direct = refined "${orig.name}?" orig p;
        viaSugar = sug' p;
      in
      viaSugar._kernel == direct._kernel);
    expected = true;
  };

  checkDelegation = {
    expr =
      let
        p = x: x > 0;
        direct = refined "Int?" Int p;
        viaSugar = sug.Int p;
        probes = [ 5 0 (-3) "x" [ ] { } ];
      in
      builtins.all (v: direct.check v == viaSugar.check v) probes;
    expected = true;
  };

  noKernelDiagEmission = {
    expr =
      let
        files = map builtins.readFile [
          ../src/sugar/types.nix
          ../src/sugar/effects.nix
          ../src/sugar/operators.nix
          ../src/sugar/module.nix
        ];
        lineMatches = pat: s:
          builtins.any (l: builtins.match ".*${pat}.*" l != null)
            (lib.splitString "\n" s);
        anyFile = pat: builtins.any (lineMatches pat) files;
      in
        !(anyFile "fx\\.diag\\.");
    expected = true;
  };

  universePrimitives = {
    expr = allIndex (i:
      let
        orig = builtins.elemAt primitives i;
        sug' = builtins.elemAt sugPrimitives i;
      in
      sug'.universe == orig.universe && orig.universe == 0);
    expected = true;
  };

  universeRefined = {
    expr =
      let
        p = x: true;
        q = x: true;
      in
      (sug.Int p).universe == Int.universe
      && (sug.Int p q).universe == Int.universe
      && (sug.String p).universe == String.universe;
    expected = true;
  };

  # Sugar preserves type identity: the type-theoretic claim is that
  # `Record { age = Int }` and `Record { age = sug.Int }` denote the
  # same type. The right predicate is definitional equality (conv),
  # not Nix `==` on `_kernel` — the latter is an
  # implementation-coupled approximation that stops being sound once
  # the kernel encoding carries closures (post Record/Variant
  # description-backed migration).
  recordKernelIdentity = {
    expr =
      let
        r1 = Record { age = Int; };
        r2 = Record { age = sug.Int; };
      in
      defEq r1 r2;
    expected = true;
  };

  recordKernelIdentityRefined = {
    expr =
      let
        p = x: x > 0;
        r1 = Record { age = refined "Int?" Int p; };
        r2 = Record { age = sug.Int p; };
      in
      defEq r1 r2;
    expected = true;
  };

  recordKernelIdentityMultiField = {
    expr =
      let
        p = x: x > 0;
        r1 = Record {
          age = refined "Int?" Int p;
          name = String;
          active = Bool;
        };
        r2 = Record {
          age = sug.Int p;
          name = sug.String;
          active = sug.Bool;
        };
      in
      defEq r1 r2;
    expected = true;
  };

  stabilityAudit = {
    expr =
      let
        files = map builtins.readFile [
          ../src/sugar/types.nix
          ../src/sugar/effects.nix
          ../src/sugar/operators.nix
          ../src/sugar/module.nix
        ];
        lineMatches = pat: s:
          builtins.any (l: builtins.match ".*${pat}.*" l != null)
            (lib.splitString "\n" s);
        anyFile = pat: builtins.any (lineMatches pat) files;
      in
      {
        noDiag = !(anyFile "fx\\.diag\\.");
        noTc = !(anyFile "fx\\.tc\\.");
        noRecordVerify = !(anyFile "Record\\.verify");
        noMkType = !(anyFile "mkType");
      };
    expected = {
      noDiag = true;
      noTc = true;
      noRecordVerify = true;
      noMkType = true;
    };
  };

  # Precondition for layer-tag propagation. The diag ADT tags every error
  # with Kernel | Generic. Today `typecheck.collecting` flattens its state
  # records to { actual, context, message, path, typeName }, so the layer
  # tag isn't yet reachable from the handler output. This test asserts only
  # that sugar-refined validation fails cleanly and emits exactly one
  # collected error. When the collecting handler begins surfacing the full
  # diag record, replace this with an assertion that
  # `(builtins.head result.state).layer.tag == "Generic"`.
  validationFailureEmits = {
    expr =
      let
        t = sug.Int (x: x > 10);
        result = fx.handle
          {
            handlers = fx.effects.typecheck.collecting;
            state = [ ];
          }
          (t.validate 5);
      in
      {
        failed = result.value == false;
        collected = builtins.length result.state == 1;
      };
    expected = { failed = true; collected = true; };
  };

  allTests = {
    inherit additiveOnlyPrimitives additiveOnlyRefined
      kernelDelegation checkDelegation
      noKernelDiagEmission
      universePrimitives universeRefined
      recordKernelIdentity recordKernelIdentityRefined recordKernelIdentityMultiField
      validationFailureEmits
      stabilityAudit;
  };

in
allTests
