{ lib, fx }:

let
  inherit (fx.types) Int String Bool Float Path Null Unit Any Record mkType defEq;
  refined = fx.types.refined;
  H = fx.types.hoas;
  sug = fx.sugar.types;

  primitives = [ Int String Bool Float Path Null Unit Any ];
  sugPrimitives = [ sug.Int sug.String sug.Bool sug.Float sug.Path sug.Null sug.Unit sug.Any ];

  additiveKeysInt = {
    expr =
      let
        origKeys = builtins.attrNames Int;
        sugKeys = builtins.attrNames sug.Int;
        preservedAll = builtins.all (k: builtins.elem k sugKeys) origKeys;
        newKeys = lib.subtractLists origKeys sugKeys;
        onlyExpected = builtins.length newKeys == 2
          && builtins.elem "__functor" newKeys
          && builtins.elem "__toString" newKeys;
      in
      preservedAll && onlyExpected;
    expected = true;
  };

  additiveKeysAllPrimitives = {
    expr =
      let
        check = i:
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
          && builtins.elem "__toString" new;
      in
      builtins.all check (lib.range 0 (builtins.length primitives - 1));
    expected = true;
  };

  keyValuesPreserved = {
    expr = {
      kernelEq = sug.Int._kernel == Int._kernel;
      checkEq = sug.Int.check 42 == Int.check 42;
      checkEqNeg = sug.Int.check "x" == Int.check "x";
      nameEq = sug.Int.name == Int.name;
      descEq = sug.Int.description == Int.description;
      universeEq = sug.Int.universe == Int.universe;
    };
    expected = {
      kernelEq = true;
      checkEq = true;
      checkEqNeg = true;
      nameEq = true;
      descEq = true;
      universeEq = true;
    };
  };

  delegationKernelEq = {
    expr =
      let p = x: x > 0;
      in (sug.Int p)._kernel == (refined "Int?" Int p)._kernel;
    expected = true;
  };

  delegationGuardEq = {
    expr =
      let
        p = x: x > 0;
        sg = sug.Int p;
        dr = refined "Int?" Int p;
      in
      {
        accept5 = sg.check 5 == dr.check 5;
        rejectNeg = sg.check (-1) == dr.check (-1);
        rejectStr = sg.check "hi" == dr.check "hi";
      };
    expected = { accept5 = true; rejectNeg = true; rejectStr = true; };
  };

  compositionCheck = {
    expr =
      let t = sug.Int (x: x > 0) (x: x < 10);
      in {
        accept5 = t.check 5;
        rejectNeg1 = t.check (-1);
        reject20 = t.check 20;
        rejectStr = t.check "hi";
      };
    expected = {
      accept5 = true;
      rejectNeg1 = false;
      reject20 = false;
      rejectStr = false;
    };
  };

  universePreservation = {
    expr = builtins.all (u: u == 0)
      (map (t: t.universe) sugPrimitives
        ++ [
        (sug.Int (x: x > 0)).universe
        (sug.Int (x: x > 0) (x: x < 10)).universe
        (sug.String (s: builtins.stringLength s > 0)).universe
      ]);
    expected = true;
  };

  toStringNoPred = {
    expr = builtins.toString sug.Int;
    expected = "Int";
  };

  toStringOnePred = {
    expr = builtins.toString (sug.Int (x: x > 0));
    expected = "Int?";
  };

  toStringTwoPred = {
    expr = builtins.toString (sug.Int (x: x > 0) (x: x < 10));
    expected = "Int??";
  };

  toStringAllPrimitives = {
    expr = map builtins.toString sugPrimitives;
    expected = [ "Int" "String" "Bool" "Float" "Path" "Null" "Unit" "Any" ];
  };

  wrapUserType = {
    expr =
      let
        UserInt = mkType { name = "UserInt"; kernelType = H.int_; };
        w = sug.wrap UserInt;
      in
      {
        name = w.name;
        accept = w.check 42;
        reject = w.check "x";
        refinedAccept = (w (x: x > 0)).check 5;
        refinedReject = (w (x: x > 0)).check (-1);
        refinedName = (w (x: x > 0)).name;
        toStr = builtins.toString w;
        toStrRefined = builtins.toString (w (x: x > 0));
        universe = w.universe == UserInt.universe;
      };
    expected = {
      name = "UserInt";
      accept = true;
      reject = false;
      refinedAccept = true;
      refinedReject = false;
      refinedName = "UserInt?";
      toStr = "UserInt";
      toStrRefined = "UserInt?";
      universe = true;
    };
  };

  # Sugar preserves type identity. Equality is definitional (conv),
  # not Nix `==`: see types/foundation.nix:defEq and the analogous
  # tests in sugar-compat-test.nix.
  recordStructuralIdentity = {
    expr =
      let
        r1 = Record { age = Int; };
        r2 = Record { age = sug.Int; };
      in
      defEq r1 r2;
    expected = true;
  };

  recordWithRefinedField = {
    expr =
      let
        p = x: x > 0;
        r1 = Record { age = refined "Int?" Int p; };
        r2 = Record { age = sug.Int p; };
      in
      defEq r1 r2;
    expected = true;
  };

  noDiagImports = {
    expr =
      let
        files = [
          (builtins.readFile ../src/sugar/types.nix)
          (builtins.readFile ../src/sugar/effects.nix)
          (builtins.readFile ../src/sugar/operators.nix)
          (builtins.readFile ../src/sugar/module.nix)
        ];
        lineContains = pat: s:
          builtins.any (l: builtins.match ".*${pat}.*" l != null)
            (lib.splitString "\n" s);
        anyFile = pat: builtins.any (lineContains pat) files;
      in
      {
        diag = anyFile "fx\\.diag\\.";
        tc = anyFile "fx\\.tc\\.";
        recordVerify = anyFile "Record\\.verify";
        mkType = anyFile "mkType";
      };
    expected = {
      diag = false;
      tc = false;
      recordVerify = false;
      mkType = false;
    };
  };

  allTests = {
    inherit additiveKeysInt additiveKeysAllPrimitives keyValuesPreserved
      delegationKernelEq delegationGuardEq
      compositionCheck
      universePreservation
      toStringNoPred toStringOnePred toStringTwoPred toStringAllPrimitives
      wrapUserType
      recordStructuralIdentity recordWithRefinedField
      noDiagImports;
  };

in
allTests
