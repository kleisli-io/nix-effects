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
  eval = comp: (run comp { } null).value;

  # =========================================================================
  # CORE: fromList, range, replicate
  # =========================================================================

  fromListToListTest = {
    expr = eval (s.toList (s.fromList [ 1 2 3 4 5 ]));
    expected = [ 1 2 3 4 5 ];
  };

  fromListEmptyTest = {
    expr = eval (s.toList (s.fromList [ ]));
    expected = [ ];
  };

  rangeTest = {
    expr = eval (s.toList (s.range 0 5));
    expected = [ 0 1 2 3 4 ];
  };

  rangeEmptyTest = {
    expr = eval (s.toList (s.range 5 5));
    expected = [ ];
  };

  replicateTest = {
    expr = eval (s.toList (s.replicate 4 "x"));
    expected = [ "x" "x" "x" "x" ];
  };

  replicateZeroTest = {
    expr = eval (s.toList (s.replicate 0 "x"));
    expected = [ ];
  };

  # Parametric: fromList roundtrip for various lists
  fromListParametric = builtins.all
    (xs:
      eval (s.toList (s.fromList xs)) == xs
    ) [ [ ] [ 1 ] [ 1 2 3 ] [ "a" "b" ] [ true false true ] ];

  # Parametric: range produces correct length
  rangeParametric = builtins.all
    (n:
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
    expected = [ ];
  };

  filterNoneTest = {
    expr = eval (s.toList (s.filter (_: true) (s.fromList [ 1 2 3 ])));
    expected = [ 1 2 3 ];
  };

  # Parametric: map preserves length
  mapPreservesLength = builtins.all
    (n:
      eval (s.length (s.map (x: x * 2) (s.range 0 n))) == n
    ) [ 0 1 5 10 ];

  # Parametric: map identity is identity
  mapIdentity = builtins.all
    (xs:
      eval (s.toList (s.map (x: x) (s.fromList xs))) == xs
    ) [ [ ] [ 1 ] [ 1 2 3 ] ];

  # Parametric: map composition
  mapComposition =
    let
      f = x: x + 10;
      g = x: x * 2;
      xs = [ 1 2 3 4 5 ];
    in
    eval (s.toList (s.map (x: f (g x)) (s.fromList xs)))
    == eval (s.toList (s.map f (s.map g (s.fromList xs))));

  # =========================================================================
  # FULL PIPELINE: fromList |> filter |> take |> toList
  # =========================================================================

  pipelineTest = {
    expr = eval (
      s.toList (
        s.take 3 (
          s.filter (x: lib.mod x 2 == 1) (
            s.fromList [ 1 2 3 4 5 6 7 8 9 10 ]))
      ));
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
    expected = [ ];
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
    expected = [ ];
  };

  # Parametric: take n from range 0..m gives min(n,m) elements
  takeParametric = builtins.all
    (pair:
      let
        n = builtins.elemAt pair 0;
        m = builtins.elemAt pair 1;
        expected = if n < m then n else m;
      in
      eval (s.length (s.take n (s.range 0 m))) == expected
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
  sumRangeParametric = builtins.all
    (n:
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
    expr = eval (s.toList (s.concat (s.fromList [ ]) (s.fromList [ 1 2 ])));
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
    expected = [{ fst = 1; snd = "a"; } { fst = 2; snd = "b"; } { fst = 3; snd = "c"; }];
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
  # STACK SAFETY — N=100000 (10× past the old recursive-overflow ceiling ~5-10k)
  #
  # Each test drives a stream combinator over bigN=100000 elements and
  # compares against an INDEPENDENT builtins-computed reference value.
  # Completion at N=100k without stack overflow = stack-safe; value match
  # against the builtins reference = correct.  Both paths must agree.
  # =========================================================================

  bigN = 100000;
  bigXs = builtins.genList (i: i) bigN;
  bigSum = builtins.foldl' (a: b: a + b) 0 bigXs; # = bigN*(bigN-1)/2

  # fold-sum: stream fold (+) 0 matches builtins.foldl'
  stackSafeFoldSum = {
    expr = eval (s.fold (acc: x: acc + x) 0 (s.fromList bigXs));
    expected = bigSum;
  };

  # fromList-toList-length: round-trip preserves element count
  stackSafeFromListLength = {
    expr = eval (s.length (s.fromList bigXs));
    expected = bigN;
  };

  # any worst-case: predicate always false → full traversal, no early exit
  stackSafeAnyWorst = {
    expr = eval (s.any (_: false) (s.fromList bigXs));
    expected = false;
  };

  # all worst-case: predicate always true → full traversal, no early exit
  stackSafeAllWorst = {
    expr = eval (s.all (_: true) (s.fromList bigXs));
    expected = true;
  };

  # drop: drop first half and sum the rest
  stackSafeDrop = {
    expr = eval (s.fold (a: b: a + b) 0 (s.drop (bigN / 2) (s.fromList bigXs)));
    expected = builtins.foldl' (a: b: a + b) 0 (builtins.genList (i: i + bigN / 2) (bigN / 2));
  };

  # filter-reject: filter that rejects everything → 0
  stackSafeFilterReject = {
    expr = eval (s.fold (a: b: a + b) 0 (s.filter (_: false) (s.fromList bigXs)));
    expected = 0;
  };

  # filter-sparse: only the very last element passes
  stackSafeFilterSparse = {
    expr = eval (s.fold (a: b: a + b) 0 (s.filter (x: x == (bigN - 1)) (s.fromList bigXs)));
    expected = bigN - 1;
  };

  # filter-pass: filter that passes everything → same sum as reference
  stackSafeFilterPass = {
    expr = eval (s.fold (a: b: a + b) 0 (s.filter (_: true) (s.fromList bigXs)));
    expected = bigSum;
  };

  # map: double every element; verify via builtins.map reference
  stackSafeMap = {
    expr = eval (s.fold (a: b: a + b) 0 (s.map (x: x * 2) (s.fromList bigXs)));
    expected = builtins.foldl' (a: b: a + b) 0 (builtins.map (x: x * 2) bigXs);
  };

  # flatMap-empty: first half maps to empty, second half passes through
  stackSafeFlatMap = {
    expr = eval (s.fold (a: b: a + b) 0
      (s.flatMap
        (x: if x < (bigN / 2) then s.fromList [ ] else s.fromList [ x ])
        (s.fromList bigXs)));
    expected = builtins.foldl' (a: b: a + b) 0
      (builtins.genList (i: i + bigN / 2) (bigN / 2));
  };

  # take: take bigN from a 2*bigN list → same as bigXs sum
  stackSafeTake = {
    expr = eval (s.fold (a: b: a + b) 0
      (s.take bigN (s.fromList (builtins.genList (i: i) (2 * bigN)))));
    expected = bigSum;
  };

  # concat: two copies of bigXs concatenated → 2× the sum
  stackSafeConcat = {
    expr = eval (s.fold (a: b: a + b) 0
      (s.concat (s.fromList bigXs) (s.fromList bigXs)));
    expected = 2 * bigSum;
  };

  # range: fold over range 0..bigN matches bigXs sum
  stackSafeRange = {
    expr = eval (s.fold (a: b: a + b) 0 (s.range 0 bigN));
    expected = bigSum;
  };

  # iterate: take bigN from iterate (+1) 0 → same as range 0..bigN
  stackSafeIterate = {
    expr = eval (s.fold (a: b: a + b) 0 (s.take bigN (s.iterate (x: x + 1) 0)));
    expected = bigSum;
  };

  # replicate: sum bigN copies of 1 == bigN
  stackSafeReplicate = {
    expr = eval (s.fold (a: b: a + b) 0 (s.replicate bigN 1));
    expected = bigN;
  };

  # takeWhile: take elements < bigN from range 0..2*bigN → same as bigXs sum
  stackSafeTakeWhile = {
    expr = eval (s.fold (a: b: a + b) 0
      (s.takeWhile (x: x < bigN) (s.range 0 (2 * bigN))));
    expected = bigSum;
  };

  # signalOn: z=0, cmp==, over replicate bigN 5 → emits [0, 5] (length 2)
  # First 0 is the initial z; go sees 5 (≠0) → emits 5; then all remaining 5s
  # are equal to previous 5 → skipped to Done.  Full traversal, no overflow.
  stackSafeSignalOn = {
    expr = eval (s.length (s.signalOn 0 (a: b: a == b) (s.replicate bigN 5)));
    expected = 2;
  };

  # zipWith: sum of pair-wise (+) over two ranges == 2 * bigSum
  stackSafeZipWith = {
    expr = eval (s.fold (a: b: a + b) 0
      (s.zipWith (a: b: a + b) (s.range 0 bigN) (s.range 0 bigN)));
    expected = 2 * bigSum;
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
      zipTest zipUnevenTest zipWithTest
      # Stack-safety regression tests (N=100000)
      stackSafeFoldSum stackSafeFromListLength
      stackSafeAnyWorst stackSafeAllWorst
      stackSafeDrop
      stackSafeFilterReject stackSafeFilterSparse stackSafeFilterPass
      stackSafeMap stackSafeFlatMap
      stackSafeTake stackSafeConcat
      stackSafeRange stackSafeIterate stackSafeReplicate
      stackSafeTakeWhile stackSafeSignalOn stackSafeZipWith;
  };

in
boolTests // exprTests
