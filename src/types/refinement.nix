# nix-effects refinement types and predicate combinators
#
# {v:B|r} — a value v of base type B satisfying refinement predicate r.
# Runtime checking: predicates evaluated at Nix eval time, catching
# misconfiguration before deployment.
#
# Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
{ fx, api, ... }:
let
  inherit (fx.types.foundation) mkType check refineGuard;
  H = fx.tc.hoas;
  R = fx.tc.kernel.reflect;

  # Named refinement constructor

  refined = name: base: predicate: mkType {
    inherit name;
    kernelType = base._kernel;
    guard = refineGuard base predicate;
    description = "${name} (refined from ${base.name})";
    # Same kernel as `base`, so `base.universe` (>= the kernel minimum) stays a
    # consistent declaration — a refinement must not silently drop a declared
    # universe back to the kernel floor.
    universe = base.universe;
  };

  refinedTests = {
    "named-refinement-accepts" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
          Nat = refined "Nat" IntType (x: x >= 0);
        in
        check Nat 5;
      expected = true;
    };
    "named-refinement-rejects" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
          Nat = refined "Nat" IntType (x: x >= 0);
        in
        check Nat (-1);
      expected = false;
    };
    # A KernelPred predicate internalizes: check derives from the kernel term
    # and the refined type carries a non-null ktype.
    "kernel-refined-accepts" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
          Pos = refined "Pos" IntType positiveInt;
        in
        check Pos 5;
      expected = true;
    };
    "kernel-refined-rejects" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
          Pos = refined "Pos" IntType positiveInt;
        in
        check Pos 0;
      expected = false;
    };
    "kernel-refined-has-ktype" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
        in
        (refined "Pos" IntType positiveInt).ktype != null;
      expected = true;
    };
    # Nested KernelPred refinements compose; a raw lambda or a String predicate
    # stay opaque and fall to ktype = null.
    "kernel-refined-composition" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
          t = refined "Bounded" (refined "Pos" IntType positiveInt) (inRangeInt 1 10);
        in
        [ (check t 5) (check t 0) (check t 20) ];
      expected = [ true false false ];
    };
    "kernel-refined-rawlambda-null-ktype" = {
      expr =
        let
          IntType = mkType { name = "Int"; kernelType = H.int_; };
        in
        (refined "Pos" IntType (x: x > 0)).ktype == null;
      expected = true;
    };
    "kernel-refined-nonempty-null-ktype" = {
      expr =
        let
          StringType = mkType { name = "String"; kernelType = H.string; };
        in
        (refined "NE" StringType nonEmpty).ktype == null;
      expected = true;
    };
    # oneOfStr internalizes: check via the kernel strEq term, non-null ktype.
    "kernel-refined-oneof-accepts-and-rejects" = {
      expr =
        let
          StringType = mkType { name = "String"; kernelType = H.string; };
          Enum = refined "Enum" StringType (oneOfStr [ "a" "b" ]);
        in
        [ (check Enum "a") (check Enum "b") (check Enum "c") (check Enum 5) ];
      expected = [ true true false false ];
    };
    "kernel-refined-oneof-has-ktype" = {
      expr =
        let
          StringType = mkType { name = "String"; kernelType = H.string; };
        in
        (refined "Enum" StringType (oneOfStr [ "a" "b" ])).ktype != null;
      expected = true;
    };
    # nonEmptyStr internalizes: check via the kernel strLen term, non-null ktype.
    "kernel-refined-nonemptystr-has-ktype" = {
      expr =
        let
          StringType = mkType { name = "String"; kernelType = H.string; };
        in
        (refined "NE" StringType nonEmptyStr).ktype != null;
      expected = true;
    };
    "kernel-refined-nonemptystr-accepts-and-rejects" = {
      expr =
        let
          StringType = mkType { name = "String"; kernelType = H.string; };
          NE = refined "NE" StringType nonEmptyStr;
        in
        [ (check NE "a") (check NE "hello") (check NE "") (check NE 5) ];
      expected = [ true true false false ];
    };
    # A refinement keeps the base's declared universe rather than dropping to the
    # kernel floor: an Int declared at U(5) refines to a still-U(5) type.
    "refined-retains-declared-universe" = {
      expr =
        let
          IntType = mkType { name = "Int5"; kernelType = H.int_; universe = 5; };
          Nat = refined "Nat" IntType (x: x >= 0);
        in
        Nat.universe;
      expected = 5;
    };
  };

  # Predicate combinators

  # Smart conjunction: a non-empty list of KernelPreds folds into one KernelPred
  # (the conjoined refinement internalizes, `.ktype` non-null); any raw lambda in
  # the list, or an empty list, falls back to a plain conjoined guard — deriving
  # the guard of each KernelPred member so it stays callable.
  allOf = preds:
    if preds != [ ] && builtins.all R.isKernelPred preds
    then builtins.foldl' R.andKP (builtins.head preds) (builtins.tail preds)
    else v: builtins.all (p: if R.isKernelPred p then (R.deriveGuard p) v else p v) preds;

  allOfTests = {
    "all-true" = { expr = allOf [ (x: x > 0) (x: x < 10) ] 5; expected = true; };
    "one-false" = { expr = allOf [ (x: x > 0) (x: x < 10) ] 15; expected = false; };
    "empty-is-true" = { expr = allOf [ ] 42; expected = true; };
    # All-KernelPred input folds to a single KernelPred whose guard conjoins both.
    "allof-kernelpreds-is-kernelpred" = { expr = R.isKernelPred (allOf [ positiveInt nonNegativeInt ]); expected = true; };
    "allof-kernelpreds-guard-in" = { expr = (R.deriveGuard (allOf [ positiveInt (inRangeInt 1 5) ])) 3; expected = true; };
    "allof-kernelpreds-guard-out" = { expr = (R.deriveGuard (allOf [ positiveInt (inRangeInt 1 5) ])) 6; expected = false; };
    # A raw lambda in the mix demotes to a plain guard that still conjoins both.
    "allof-mixed-falls-back" = { expr = allOf [ positiveInt (x: x < 100) ] 5; expected = true; };
    "allof-mixed-rejects" = { expr = allOf [ positiveInt (x: x < 100) ] 0; expected = false; };
    # Empty list is not a KernelPred — stays a constant-true guard.
    "allof-empty-not-kernelpred" = { expr = R.isKernelPred (allOf [ ]); expected = false; };
  };

  anyOf = preds: v: builtins.foldl' (acc: p: acc || p v) false preds;

  anyOfTests = {
    "one-true" = { expr = anyOf [ (x: x > 10) (x: x < 0) ] (-5); expected = true; };
    "none-true" = { expr = anyOf [ (x: x > 10) (x: x < 0) ] 5; expected = false; };
    "empty-is-false" = { expr = anyOf [ ] 42; expected = false; };
  };

  negate = p: v: !(p v);

  negateTests = {
    "negates-true" = { expr = negate (x: x > 0) (-1); expected = true; };
    "negates-false" = { expr = negate (x: x > 0) 1; expected = false; };
  };

  # Common predicates

  positive = x: x > 0;

  positiveTests = {
    "accepts-positive" = { expr = positive 5; expected = true; };
    "rejects-zero" = { expr = positive 0; expected = false; };
  };

  nonNegative = x: x >= 0;

  nonNegativeTests = {
    "accepts-zero" = { expr = nonNegative 0; expected = true; };
    "rejects-negative" = { expr = nonNegative (-1); expected = false; };
  };

  inRange = lo: hi: x: x >= lo && x <= hi;

  inRangeTests = {
    "in-range" = { expr = inRange 1 10 5; expected = true; };
    "out-of-range" = { expr = inRange 1 10 15; expected = false; };
    "at-boundary" = { expr = inRange 1 10 10; expected = true; };
  };

  nonEmpty = x:
    if builtins.isString x then builtins.stringLength x > 0
    else if builtins.isList x then builtins.length x > 0
    else false;

  nonEmptyTests = {
    "non-empty-string" = { expr = nonEmpty "hello"; expected = true; };
    "empty-string" = { expr = nonEmpty ""; expected = false; };
    "non-empty-list" = { expr = nonEmpty [ 1 ]; expected = true; };
    "empty-list" = { expr = nonEmpty [ ]; expected = false; };
  };

  matching = pattern: s:
    builtins.isString s && builtins.match pattern s != null;

  matchingTests = {
    "matches" = { expr = matching "[a-z]+" "hello"; expected = true; };
    "no-match" = { expr = matching "[a-z]+" "123"; expected = false; };
  };

  # KernelPred witness over the signed-int carrier; the resulting type's check
  # is kernel-decided, `.ktype` non-null. lo/hi/k are Nix ints.
  positiveInt = R.intPositive;
  nonNegativeInt = R.intNonNegative;
  inRangeInt = R.intInRange;
  eqInt = R.intEq;

  # `oneOfStr [lits]`: KernelPred deciding String membership in a literal set via
  # strEq (singleton = equality). Internalizes (non-null `.ktype`); `matching`
  # needs string introspection the kernel lacks and stays a raw lambda.
  oneOfStr = R.strOneOf;

  # `nonEmptyStr`: KernelPred deciding String non-emptiness via strLen (1 <= len).
  # Internalizes (non-null `.ktype`). The raw `nonEmpty` (below) stays for the
  # list branch, whose carrier the kernel does not introspect.
  nonEmptyStr = R.strNonEmpty;

in
api.namespace {
  description = "Refinement types: `refined` plus `allOf`/`anyOf`/`negate`, raw built-in predicates `positive`/`nonNegative`/`inRange`/`nonEmpty`/`matching`, and the kernel-internalizing predicates — Int `positiveInt`/`nonNegativeInt`/`inRangeInt`/`eqInt` and String `oneOfStr`/`nonEmptyStr` (carry a KernelPred witness so `.ktype` is non-null).";
  doc = ''
    Refinement types and predicate combinators.
    Grounded in Freeman & Pfenning (1991) and Rondon et al. (2008).
  '';
  value = {
    refined = api.leaf {
      value = refined;
      description = "refined: build a named refinement type narrowing `base` with an extra predicate; the resulting type's `check` conjoins kernel decision with the guard.";
      signature = "refined : String -> Type -> (Value -> Bool) -> Type";
      doc = ''
        Create a named refinement type. The supplied predicate runs in
        addition to the base type's check — kernel handles structural
        validation, the predicate handles residual constraints.
      '';
      tests = refinedTests;
    };
    allOf = api.leaf {
      value = allOf;
      description = "allOf: conjoin a list of predicates. A non-empty list of all-KernelPred members folds into one KernelPred (the conjoined refinement internalizes); any raw lambda, or an empty list, yields a plain conjoined guard that holds when every member holds (empty = constant `true`).";
      signature = "allOf : [(KernelPred | (Value -> Bool))] -> (KernelPred | (Value -> Bool))";
      doc = "Combine predicates with conjunction: `(allOf [p1 p2]) v = p1 v && p2 v`. All-KernelPred input folds to a KernelPred so the refinement internalizes; a raw-lambda member demotes to a plain guard. Empty list returns constant `true`.";
      tests = allOfTests;
    };
    anyOf = api.leaf {
      value = anyOf;
      description = "anyOf: disjoin a list of predicates into one that holds when any member holds; the empty list yields a constant `false`.";
      signature = "anyOf : [(Value -> Bool)] -> Value -> Bool";
      doc = "Combine predicates with disjunction: `(anyOf [p1 p2]) v = p1 v || p2 v`. Empty list returns `false`.";
      tests = anyOfTests;
    };
    negate = api.leaf {
      value = negate;
      description = "negate: flip a predicate's polarity; `negate p` accepts exactly the values `p` rejects, and vice versa.";
      signature = "negate : (Value -> Bool) -> Value -> Bool";
      doc = "Negate a predicate: `(negate p) v = !(p v)`.";
      tests = negateTests;
    };
    positive = api.leaf {
      value = positive;
      description = "positive: predicate asserting that a numeric value is strictly greater than zero; rejects zero, negatives, and non-numerics by extension.";
      signature = "positive : Number -> Bool";
      doc = "Predicate: `value > 0`. Strict — zero is rejected.";
      tests = positiveTests;
    };
    nonNegative = api.leaf {
      value = nonNegative;
      description = "nonNegative: predicate asserting that a numeric value is greater than or equal to zero; accepts zero, rejects negatives.";
      signature = "nonNegative : Number -> Bool";
      doc = "Predicate: `value >= 0`. Zero accepted.";
      tests = nonNegativeTests;
    };
    inRange = api.leaf {
      value = inRange;
      description = "inRange: factory predicate asserting that a numeric value lies within `[lo, hi]`; both endpoints are inclusive.";
      signature = "inRange : Number -> Number -> Number -> Bool";
      doc = "Predicate factory: `(inRange lo hi) v = lo <= v <= hi`. Both endpoints inclusive.";
      tests = inRangeTests;
    };
    nonEmpty = api.leaf {
      value = nonEmpty;
      description = "nonEmpty: predicate asserting that a string or list has at least one element/character; values of other types are rejected.";
      signature = "nonEmpty : (String | List) -> Bool";
      doc = "Predicate: string or list is non-empty. Rejects non-string/non-list inputs.";
      tests = nonEmptyTests;
    };
    matching = api.leaf {
      value = matching;
      description = "matching: factory predicate that holds when a value is a string fully matched by the supplied regex pattern; non-strings are rejected.";
      signature = "matching : String -> String -> Bool";
      doc = "Predicate factory: `(matching pattern) s = s matches regex pattern`. Full-match semantics — anchor not needed.";
      tests = matchingTests;
    };

    positiveInt = api.leaf {
      value = positiveInt;
      description = "positiveInt: kernel-internalizing refinement predicate `x > 0` over Int; as the predicate of `refined`/`refine` it yields a type whose check is kernel-decided and whose `.ktype` is non-null.";
      signature = "positiveInt : KernelPred";
      doc = "KernelPred witness over the signed-int carrier deciding `x > 0`. Unlike `positive` (a raw lambda), this internalizes into the kernel `ktype`.";
    };
    nonNegativeInt = api.leaf {
      value = nonNegativeInt;
      description = "nonNegativeInt: kernel-internalizing refinement predicate `x >= 0` over Int; internalizes into the kernel `ktype` when used with `refined`/`refine`.";
      signature = "nonNegativeInt : KernelPred";
      doc = "KernelPred witness over the signed-int carrier deciding `x >= 0`.";
    };
    inRangeInt = api.leaf {
      value = inRangeInt;
      description = "inRangeInt: kernel-internalizing factory predicate `lo <= x <= hi` over Int; both endpoints inclusive, internalizes into the kernel `ktype`.";
      signature = "inRangeInt : Int -> Int -> KernelPred";
      doc = "KernelPred witness factory over the signed-int carrier deciding `lo <= x <= hi`.";
    };
    eqInt = api.leaf {
      value = eqInt;
      description = "eqInt: kernel-internalizing factory predicate `x == k` over Int; internalizes into the kernel `ktype`.";
      signature = "eqInt : Int -> KernelPred";
      doc = "KernelPred witness factory over the signed-int carrier deciding `x == k`.";
    };

    oneOfStr = api.leaf {
      value = oneOfStr;
      description = "oneOfStr: kernel-internalizing factory predicate deciding membership in a fixed String literal set, via the kernel's decidable `strEq`; a singleton list is equality-against-literal. As the predicate of `refined`/`refine` it internalizes into the kernel `ktype`. Decides by literal equality — substring/match stay outside the kernel.";
      signature = "oneOfStr : [String] -> KernelPred";
      doc = "KernelPred witness factory over the string carrier deciding `x ∈ {lits…}` as a strEq disjunction. Unlike `matching` (a raw lambda needing string introspection the kernel lacks), this internalizes.";
    };

    nonEmptyStr = api.leaf {
      value = nonEmptyStr;
      description = "nonEmptyStr: kernel-internalizing refinement predicate deciding String non-emptiness via the host-backed `strLen` (`1 <= length x`). As the predicate of `refined`/`refine` it internalizes into the kernel `ktype`, unlike the raw `nonEmpty` which also covers the list carrier.";
      signature = "nonEmptyStr : KernelPred";
      doc = "KernelPred witness over the string carrier deciding `length x >= 1` through `strLen`. Use in place of `nonEmpty` on String to internalize the refinement (non-null `.ktype`).";
    };

  };
}
