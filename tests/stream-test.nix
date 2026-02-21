# nix-effects stream integration tests
#
# Validates the full stream pipeline: create, transform, limit, reduce, combine.
# Streams are pure computations — no handler needed for basic operations.
# Effectful streams (using send inside stream steps) require handlers.
{ lib, fx }:

let
  inherit (fx) run;
  s = fx.stream;

  # Helper: run a pure stream computation through empty handler
  eval = comp: (run comp {} null).value;

  # =========================================================================
  # CORE: fromList, range, replicate
  # =========================================================================

  fromListToListTest = {
    expr = eval (s.toList (s.fromList [ 1 2 3 4 5 ]));
    expected = [ 1 2 3 4 5 ];
  };

  fromListEmptyTest = {
    expr = eval (s.toList (s.fromList []));
    expected = [];
  };

  rangeTest = {
    expr = eval (s.toList (s.range 0 5));
    expected = [ 0 1 2 3 4 ];
  };

  rangeEmptyTest = {
    expr = eval (s.toList (s.range 5 5));
    expected = [];
  };

  replicateTest = {
    expr = eval (s.toList (s.replicate 4 "x"));
    expected = [ "x" "x" "x" "x" ];
  };

  replicateZeroTest = {
    expr = eval (s.toList (s.replicate 0 "x"));
    expected = [];
  };

  # Parametric: fromList roundtrip for various lists
  fromListParametric = builtins.all (xs:
    eval (s.toList (s.fromList xs)) == xs
  ) [ [] [ 1 ] [ 1 2 3 ] [ "a" "b" ] [ true false true ] ];

  # Parametric: range produces correct length
  rangeParametric = builtins.all (n:
    eval (s.length (s.range 0 n)) == n
  ) [ 0 1 5 10 20 ];

  # =========================================================================
  # TRANSFORM: map, filter
  # =========================================================================

  mapTest = {
    expr = eval (s.toList (s.map (x: x * 2) (s.fromList [ 1 2 3 ])));
    expected = [ 2 4 6 ];
  };

  filterTest = {
    expr = eval (s.toList (s.filter (x: lib.mod x 2 == 0) (s.fromList [ 1 2 3 4 5 6 ])));
    expected = [ 2 4 6 ];
  };

  filterAllTest = {
    expr = eval (s.toList (s.filter (_: false) (s.fromList [ 1 2 3 ])));
    expected = [];
  };

  filterNoneTest = {
    expr = eval (s.toList (s.filter (_: true) (s.fromList [ 1 2 3 ])));
    expected = [ 1 2 3 ];
  };

  # Parametric: map preserves length
  mapPreservesLength = builtins.all (n:
    eval (s.length (s.map (x: x * 2) (s.range 0 n))) == n
  ) [ 0 1 5 10 ];

  # Parametric: map identity is identity
  mapIdentity = builtins.all (xs:
    eval (s.toList (s.map (x: x) (s.fromList xs))) == xs
  ) [ [] [ 1 ] [ 1 2 3 ] ];

  # Parametric: map composition
  mapComposition =
    let
      f = x: x + 10;
      g = x: x * 2;
      xs = [ 1 2 3 4 5 ];
    in eval (s.toList (s.map (x: f (g x)) (s.fromList xs)))
    == eval (s.toList (s.map f (s.map g (s.fromList xs))));

  # =========================================================================
  # FULL PIPELINE: fromList |> filter |> take |> toList
  # =========================================================================

  pipelineTest = {
    expr = eval (
      s.toList (
        s.take 3 (
          s.filter (x: lib.mod x 2 == 1) (
            s.fromList [ 1 2 3 4 5 6 7 8 9 10 ]))));
    expected = [ 1 3 5 ];
  };

  # =========================================================================
  # LIMIT: take, takeWhile, drop
  # =========================================================================

  takeTest = {
    expr = eval (s.toList (s.take 3 (s.fromList [ 10 20 30 40 50 ])));
    expected = [ 10 20 30 ];
  };

  takeMoreThanAvailable = {
    expr = eval (s.toList (s.take 100 (s.fromList [ 1 2 ])));
    expected = [ 1 2 ];
  };

  takeZeroTest = {
    expr = eval (s.toList (s.take 0 (s.fromList [ 1 2 3 ])));
    expected = [];
  };

  takeWhileTest = {
    expr = eval (s.toList (s.takeWhile (x: x < 4) (s.fromList [ 1 2 3 4 5 ])));
    expected = [ 1 2 3 ];
  };

  takeFromInfinite = {
    expr = eval (s.toList (s.take 5 (s.iterate (x: x + 1) 0)));
    expected = [ 0 1 2 3 4 ];
  };

  dropTest = {
    expr = eval (s.toList (s.drop 2 (s.fromList [ 10 20 30 40 ])));
    expected = [ 30 40 ];
  };

  dropAllTest = {
    expr = eval (s.toList (s.drop 100 (s.fromList [ 1 2 ])));
    expected = [];
  };

  # Parametric: take n from range 0..m gives min(n,m) elements
  takeParametric = builtins.all (pair:
    let n = builtins.elemAt pair 0; m = builtins.elemAt pair 1;
        expected = if n < m then n else m;
    in eval (s.length (s.take n (s.range 0 m))) == expected
  ) [ [ 0 5 ] [ 3 5 ] [ 5 5 ] [ 10 5 ] ];

  # =========================================================================
  # REDUCE: fold, sum, length, any, all
  # =========================================================================

  foldTest = {
    expr = eval (s.fold (acc: x: acc + x) 0 (s.fromList [ 1 2 3 4 5 ]));
    expected = 15;
  };

  sumTest = {
    expr = eval (s.sum (s.fromList [ 10 20 30 ]));
    expected = 60;
  };

  lengthTest = {
    expr = eval (s.length (s.fromList [ "a" "b" "c" ]));
    expected = 3;
  };

  anyTrueTest = {
    expr = eval (s.any (x: x > 3) (s.fromList [ 1 2 3 4 5 ]));
    expected = true;
  };

  anyFalseTest = {
    expr = eval (s.any (x: x > 10) (s.fromList [ 1 2 3 ]));
    expected = false;
  };

  allTrueTest = {
    expr = eval (s.all (x: x > 0) (s.fromList [ 1 2 3 ]));
    expected = true;
  };

  allFalseTest = {
    expr = eval (s.all (x: x > 2) (s.fromList [ 1 2 3 ]));
    expected = false;
  };

  # Parametric: sum of range 0..n = n*(n-1)/2
  sumRangeParametric = builtins.all (n:
    eval (s.sum (s.range 0 n)) == (n * (n - 1)) / 2
  ) [ 0 1 5 10 100 ];

  # =========================================================================
  # COMBINE: concat, interleave, zip, zipWith
  # =========================================================================

  concatTest = {
    expr = eval (s.toList (s.concat (s.fromList [ 1 2 ]) (s.fromList [ 3 4 ])));
    expected = [ 1 2 3 4 ];
  };

  concatEmptyLeftTest = {
    expr = eval (s.toList (s.concat (s.fromList []) (s.fromList [ 1 2 ])));
    expected = [ 1 2 ];
  };

  interleaveTest = {
    expr = eval (s.toList (s.interleave (s.fromList [ 1 3 5 ]) (s.fromList [ 2 4 6 ])));
    expected = [ 1 2 3 4 5 6 ];
  };

  interleaveUnevenTest = {
    expr = eval (s.toList (s.interleave (s.fromList [ 1 3 ]) (s.fromList [ 2 4 6 8 ])));
    expected = [ 1 2 3 4 6 8 ];
  };

  zipTest = {
    expr = eval (s.toList (s.zip (s.fromList [ 1 2 3 ]) (s.fromList [ "a" "b" "c" ])));
    expected = [ { fst = 1; snd = "a"; } { fst = 2; snd = "b"; } { fst = 3; snd = "c"; } ];
  };

  zipUnevenTest = {
    expr = eval (s.length (s.zip (s.fromList [ 1 2 ]) (s.fromList [ "a" "b" "c" ])));
    expected = 2;
  };

  zipWithTest = {
    expr = eval (s.toList (s.zipWith (a: b: a + b) (s.fromList [ 1 2 3 ]) (s.fromList [ 10 20 30 ])));
    expected = [ 11 22 33 ];
  };

  # =========================================================================
  # COLLECT RESULTS
  # =========================================================================

  boolTests = {
    inherit fromListParametric rangeParametric
            mapPreservesLength mapIdentity mapComposition
            takeParametric sumRangeParametric;
  };

  exprTests = {
    inherit fromListToListTest fromListEmptyTest
            rangeTest rangeEmptyTest
            replicateTest replicateZeroTest
            mapTest filterTest filterAllTest filterNoneTest
            pipelineTest
            takeTest takeMoreThanAvailable takeZeroTest
            takeWhileTest takeFromInfinite
            dropTest dropAllTest
            foldTest sumTest lengthTest
            anyTrueTest anyFalseTest allTrueTest allFalseTest
            concatTest concatEmptyLeftTest
            interleaveTest interleaveUnevenTest
            zipTest zipUnevenTest zipWithTest;
  };

  exprResults = builtins.mapAttrs (_: test:
    let actual = test.expr; in
    { inherit actual; expected = test.expected; pass = actual == test.expected; }
  ) exprTests;

  exprFailed = lib.filterAttrs (_: r: !r.pass) exprResults;

  boolAllPass = builtins.all (n: boolTests.${n}) (builtins.attrNames boolTests);
  exprAllPass = (builtins.length (builtins.attrNames exprFailed)) == 0;

in boolTests // exprTests // {
  allPass = boolAllPass && exprAllPass;
}
