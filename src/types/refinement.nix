# nix-effects refinement types and predicate combinators
#
# {v:B|r} — a value v of base type B satisfying refinement predicate r.
# Runtime checking: predicates evaluated at Nix eval time, catching
# misconfiguration before deployment.
#
# Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;

  # -- Named refinement constructor --

  refined = mk {
    doc = ''
      Create a named refinement type.
      refined : string -> Type -> (value -> bool) -> Type
    '';
    value = name: base: predicate: mkType {
      inherit name;
      check = v: base.check v && predicate v;
      inherit (base) universe;
      description = "${name} (refined from ${base.name})";
    };
    tests = {
      "named-refinement-accepts" = {
        expr =
          let
            IntType = mkType { name = "Int"; check = builtins.isInt; };
            Nat = refined.value "Nat" IntType (x: x >= 0);
          in check Nat 5;
        expected = true;
      };
      "named-refinement-rejects" = {
        expr =
          let
            IntType = mkType { name = "Int"; check = builtins.isInt; };
            Nat = refined.value "Nat" IntType (x: x >= 0);
          in check Nat (-1);
        expected = false;
      };
    };
  };

  # -- Predicate combinators --

  allOf = mk {
    doc = "Combine predicates with conjunction: (allOf [p1 p2]) v = p1 v && p2 v.";
    value = preds: v: builtins.all (p: p v) preds;
    tests = {
      "all-true" = { expr = allOf.value [(x: x > 0) (x: x < 10)] 5; expected = true; };
      "one-false" = { expr = allOf.value [(x: x > 0) (x: x < 10)] 15; expected = false; };
      "empty-is-true" = { expr = allOf.value [] 42; expected = true; };
    };
  };

  anyOf = mk {
    doc = "Combine predicates with disjunction: (anyOf [p1 p2]) v = p1 v || p2 v.";
    value = preds: v: builtins.foldl' (acc: p: acc || p v) false preds;
    tests = {
      "one-true" = { expr = anyOf.value [(x: x > 10) (x: x < 0)] (-5); expected = true; };
      "none-true" = { expr = anyOf.value [(x: x > 10) (x: x < 0)] 5; expected = false; };
      "empty-is-false" = { expr = anyOf.value [] 42; expected = false; };
    };
  };

  negate = mk {
    doc = "Negate a predicate: (negate p) v = !(p v).";
    value = p: v: !(p v);
    tests = {
      "negates-true" = { expr = negate.value (x: x > 0) (-1); expected = true; };
      "negates-false" = { expr = negate.value (x: x > 0) 1; expected = false; };
    };
  };

  # -- Common predicates --

  positive = mk {
    doc = "Predicate: value > 0.";
    value = x: x > 0;
    tests = {
      "accepts-positive" = { expr = positive.value 5; expected = true; };
      "rejects-zero" = { expr = positive.value 0; expected = false; };
    };
  };

  nonNegative = mk {
    doc = "Predicate: value >= 0.";
    value = x: x >= 0;
    tests = {
      "accepts-zero" = { expr = nonNegative.value 0; expected = true; };
      "rejects-negative" = { expr = nonNegative.value (-1); expected = false; };
    };
  };

  inRange = mk {
    doc = "Predicate factory: (inRange lo hi) v = lo <= v <= hi.";
    value = lo: hi: x: x >= lo && x <= hi;
    tests = {
      "in-range" = { expr = inRange.value 1 10 5; expected = true; };
      "out-of-range" = { expr = inRange.value 1 10 15; expected = false; };
      "at-boundary" = { expr = inRange.value 1 10 10; expected = true; };
    };
  };

  nonEmpty = mk {
    doc = "Predicate: string or list is non-empty.";
    value = x:
      if builtins.isString x then builtins.stringLength x > 0
      else if builtins.isList x then builtins.length x > 0
      else false;
    tests = {
      "non-empty-string" = { expr = nonEmpty.value "hello"; expected = true; };
      "empty-string" = { expr = nonEmpty.value ""; expected = false; };
      "non-empty-list" = { expr = nonEmpty.value [1]; expected = true; };
      "empty-list" = { expr = nonEmpty.value []; expected = false; };
    };
  };

  matching = mk {
    doc = "Predicate factory: (matching pattern) s = s matches regex pattern.";
    value = pattern: s:
      builtins.isString s && builtins.match pattern s != null;
    tests = {
      "matches" = { expr = matching.value "[a-z]+" "hello"; expected = true; };
      "no-match" = { expr = matching.value "[a-z]+" "123"; expected = false; };
    };
  };

in mk {
  doc = ''
    Refinement types and predicate combinators.
    Grounded in Freeman & Pfenning (1991) and Rondon et al. (2008).
  '';
  value = {
    inherit refined;
    inherit allOf anyOf negate;
    inherit positive nonNegative inRange nonEmpty matching;
  };
}
