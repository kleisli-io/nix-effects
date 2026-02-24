# Verified Functions: extracting correct-by-construction Nix functions
#
# The v.verify pipeline type-checks a HOAS implementation against a type,
# evaluates it, and extracts a real Nix function. The result is a plain
# Nix value you can call — but one that was kernel-verified before use.
#
# Pipeline: write HOAS type + impl → kernel checks → eval → extract Nix value
#
# This file builds up from the simplest case (successor) through boolean
# logic, multi-argument functions, pattern matching, list operations,
# and finally composed pipelines. Each section extracts a verified function
# and tests it on concrete Nix data.
#
#   nix build .#checks.verified-functions   — verify all tests
{ fx, ... }:

let
  H = fx.types.hoas;
  v = fx.types.verified;

in rec {

  # ===== 1. Successor: Nat → Nat =====
  #
  # The simplest verified function. The kernel confirms that succ
  # maps a natural number to a natural number, then extracts a Nix
  # function you can call on integers.

  succFn = v.verify (H.forall "x" H.nat (_: H.nat))
                    (v.fn "x" H.nat (x: H.succ x));

  succApply5 = succFn 5 == 6;
  succApply0 = succFn 0 == 1;


  # ===== 2. Boolean not: Bool → Bool =====
  #
  # v.if_ builds a BoolElim with a constant motive — you supply the
  # result type, the scrutinee, and then/else branches.

  notFn = v.verify (H.forall "b" H.bool (_: H.bool))
                   (v.fn "b" H.bool (b:
                     v.if_ H.bool b { then_ = v.false_; else_ = v.true_; }));

  notTrue  = notFn true  == false;
  notFalse = notFn false == true;


  # ===== 3. Addition: Nat → Nat → Nat =====
  #
  # Two-argument verified function. v.match builds a NatElim with
  # constant motive: zero branch returns n, succ branch wraps the
  # inductive hypothesis with S.
  #
  # add(0, n) = n
  # add(S(k), n) = S(add(k, n))

  addFn = v.verify (H.forall "m" H.nat (_: H.forall "n" H.nat (_: H.nat)))
                   (v.fn "m" H.nat (m: v.fn "n" H.nat (n:
                     v.match H.nat m {
                       zero = n;
                       succ = _k: ih: H.succ ih;
                     })));

  add2and3 = addFn 2 3 == 5;
  add0and7 = addFn 0 7 == 7;
  add4and0 = addFn 4 0 == 4;


  # ===== 4. IsZero: Nat → Bool =====
  #
  # Pattern match on a natural to produce a boolean.
  # Shows cross-type elimination: Nat scrutinee, Bool result.

  isZeroFn = v.verify (H.forall "n" H.nat (_: H.bool))
                      (v.fn "n" H.nat (n:
                        v.match H.bool n {
                          zero = v.true_;
                          succ = _k: _ih: v.false_;
                        }));

  isZeroOf0 = isZeroFn 0 == true;
  isZeroOf5 = isZeroFn 5 == false;


  # ===== 5. Predecessor: Nat → Nat =====
  #
  # pred(0) = 0, pred(S(k)) = k.
  # The succ branch ignores the inductive hypothesis and returns
  # the predecessor directly.

  predFn = v.verify (H.forall "n" H.nat (_: H.nat))
                    (v.fn "n" H.nat (n:
                      v.match H.nat n {
                        zero = v.nat 0;
                        succ = k: _ih: k;
                      }));

  predOf0 = predFn 0 == 0;
  predOf1 = predFn 1 == 0;
  predOf5 = predFn 5 == 4;


  # ===== 6. Map: apply a function to every list element =====
  #
  # v.map takes element type, result type, a HOAS function term, and
  # a HOAS list. The whole expression is verified and extracted as a
  # Nix list.

  mapSuccResult = v.verify (H.listOf H.nat)
    (v.map H.nat H.nat
      (v.fn "x" H.nat (x: H.succ x))
      (H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 1)
        (H.cons H.nat (v.nat 2) (H.nil H.nat)))));

  mapSuccCorrect = mapSuccResult == [1 2 3];

  mapEmptyResult = v.verify (H.listOf H.nat)
    (v.map H.nat H.nat
      (v.fn "x" H.nat (x: H.succ x))
      (H.nil H.nat));

  mapEmptyCorrect = mapEmptyResult == [];


  # ===== 7. Filter: keep elements matching a predicate =====
  #
  # v.filter takes element type, a HOAS predicate (A → Bool), and a
  # HOAS list. Returns only elements where the predicate returns true.

  filterZerosResult = v.verify (H.listOf H.nat)
    (v.filter H.nat
      (v.fn "n" H.nat (n:
        v.match H.bool n {
          zero = v.true_;
          succ = _k: _ih: v.false_;
        }))
      (H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 1)
        (H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 2) (H.nil H.nat))))));

  filterZerosCorrect = filterZerosResult == [0 0];


  # ===== 8. Fold: reduce a list to a single value =====
  #
  # v.fold takes element type, result type, initial accumulator,
  # a HOAS combining function (A → R → R), and a HOAS list.

  foldSumResult = v.verify H.nat
    (v.fold H.nat H.nat (v.nat 0)
      (v.fn "a" H.nat (a: v.fn "b" H.nat (b:
        v.match H.nat a {
          zero = b;
          succ = _k: ih: H.succ ih;
        })))
      (H.cons H.nat (v.nat 1) (H.cons H.nat (v.nat 2)
        (H.cons H.nat (v.nat 3) (H.nil H.nat)))));

  foldSumCorrect = foldSumResult == 6;


  # ===== 9. Composed pipeline: sum of filtered list =====
  #
  # Build a HOAS list, filter to keep only non-zero elements,
  # then fold to sum them — all in one verified expression.
  #
  # Input:  [0, 3, 0, 2, 1]
  # Filter: [3, 2, 1]    (remove zeros)
  # Sum:    6

  composedResult =
    let
      input = H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 3)
        (H.cons H.nat (v.nat 0) (H.cons H.nat (v.nat 2)
          (H.cons H.nat (v.nat 1) (H.nil H.nat)))));
      # Predicate: non-zero?
      nonZero = v.fn "n" H.nat (n:
        v.match H.bool n {
          zero = v.false_;
          succ = _k: _ih: v.true_;
        });
      filtered = v.filter H.nat nonZero input;
      # Addition as combining function
      addCombine = v.fn "a" H.nat (a: v.fn "acc" H.nat (acc:
        v.match H.nat a {
          zero = acc;
          succ = _k: ih: H.succ ih;
        }));
    in v.verify H.nat (v.fold H.nat H.nat (v.nat 0) addCombine filtered);

  composedCorrect = composedResult == 6;


  # ===== 10. Sum elimination: dispatch on coproduct =====
  #
  # v.matchSum eliminates Sum(A,B) into a result type.
  # Left(n:Nat) → succ(n), Right(b:Bool) → if b then 1 else 0.

  sumLeftResult = v.verify H.nat
    (v.matchSum H.nat H.bool H.nat (v.inl H.nat H.bool (v.nat 5)) {
      left = x: H.succ x;
      right = b: v.if_ H.nat b { then_ = v.nat 1; else_ = v.nat 0; };
    });

  sumLeftCorrect = sumLeftResult == 6;

  sumRightResult = v.verify H.nat
    (v.matchSum H.nat H.bool H.nat (v.inr H.nat H.bool v.true_) {
      left = x: H.succ x;
      right = b: v.if_ H.nat b { then_ = v.nat 1; else_ = v.nat 0; };
    });

  sumRightCorrect = sumRightResult == 1;


  # ===== 11. Let binding: local definitions =====
  #
  # v.let_ introduces a type-checked local binding.
  # let x = 3 in succ(x) → 4

  letResult = v.verify H.nat
    (v.let_ "x" H.nat (v.nat 3) (x: H.succ x));

  letCorrect = letResult == 4;


  # ===== 12. Pairs: construct and project =====
  #
  # v.pair builds a Sigma pair, v.fst/v.snd project.
  # Projections need the pair annotated with its Sigma type so the
  # checker can synthesize the component types.

  pairFstResult = v.verify H.nat
    (let
      sigTy = H.sigma "x" H.nat (_: H.bool);
      p = H.ann (v.pair (v.nat 42) v.true_ sigTy) sigTy;
    in v.fst p);

  pairFstCorrect = pairFstResult == 42;

  pairSndResult = v.verify H.bool
    (let
      sigTy = H.sigma "x" H.nat (_: H.bool);
      p = H.ann (v.pair (v.nat 42) v.true_ sigTy) sigTy;
    in v.snd p);

  pairSndCorrect = pairSndResult == true;


  # ===== 13. Record-domain functions =====
  #
  # v.field projects named fields from H.record types.
  # Records elaborate to nested Sigma; v.field desugars to fst/snd chains.

  # Get first field from a 2-field record
  recordGetX = v.verify
    (H.forall "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (_: H.nat))
    (v.fn "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (r:
      v.field (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) "x" r));

  recordGetXCorrect = recordGetX { x = 3; y = true; } == 3;

  # Get second field
  recordGetY = v.verify
    (H.forall "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (_: H.bool))
    (v.fn "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (r:
      v.field (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) "y" r));

  recordGetYCorrect = recordGetY { x = 3; y = true; } == true;

  # Compute on record: succ(x)
  recordSuccX = v.verify
    (H.forall "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (_: H.nat))
    (v.fn "r" (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) (r:
      H.succ (v.field (H.record [ { name = "x"; type = H.nat; } { name = "y"; type = H.bool; } ]) "x" r)));

  recordSuccXCorrect = recordSuccX { x = 10; y = false; } == 11;


  # ===== 14. String equality: kernel-verified strEq =====

  strEqFn = v.verify (H.forall "a" H.string (_: H.forall "b" H.string (_: H.bool)))
    (v.fn "a" H.string (a: v.fn "b" H.string (b: v.strEq a b)));

  strEqSame = strEqFn "foo" "foo" == true;
  strEqDiff = strEqFn "foo" "bar" == false;
  strEqEmpty = strEqFn "" "" == true;


  # ===== 15. String membership: kernel-verified strElem =====

  strElemFn = v.verify (H.forall "t" H.string (_: H.forall "xs" (H.listOf H.string) (_: H.bool)))
    (v.fn "t" H.string (t: v.fn "xs" (H.listOf H.string) (xs:
      v.strElem t xs)));

  strElemFound = strElemFn "b" [ "a" "b" "c" ] == true;
  strElemMissing = strElemFn "z" [ "a" "b" "c" ] == false;
  strElemEmptyList = strElemFn "a" [] == false;


  # ===== 16. Record + strEq: kernel-verified record function =====

  recordStrEqFn = let
    recTy = H.record [
      { name = "name"; type = H.string; }
      { name = "target"; type = H.string; }
    ];
  in v.verify (H.forall "r" recTy (_: H.bool))
    (v.fn "r" recTy (r:
      v.strEq (v.field recTy "name" r) (v.field recTy "target" r)));

  recordStrEqMatch = recordStrEqFn { name = "hello"; target = "hello"; } == true;
  recordStrEqNoMatch = recordStrEqFn { name = "hello"; target = "world"; } == false;


  # ===== All tests =====

  allPass =
    succApply5 && succApply0
    && notTrue && notFalse
    && add2and3 && add0and7 && add4and0
    && isZeroOf0 && isZeroOf5
    && predOf0 && predOf1 && predOf5
    && mapSuccCorrect && mapEmptyCorrect
    && filterZerosCorrect
    && foldSumCorrect
    && composedCorrect
    && sumLeftCorrect && sumRightCorrect
    && letCorrect
    && pairFstCorrect && pairSndCorrect
    && recordGetXCorrect && recordGetYCorrect && recordSuccXCorrect
    && strEqSame && strEqDiff && strEqEmpty
    && strElemFound && strElemMissing && strElemEmptyList
    && recordStrEqMatch && recordStrEqNoMatch;
}
