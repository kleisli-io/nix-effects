# nix-effects API layer
#
# Provides mk/extractValue/extractTests for structured module definitions.
# Following the nfx pattern: each function wrapped in mk { doc, value, tests }.
{ lib }:

rec {
  # Wrap a value with documentation and inline tests.
  # Usage: mk { doc = "description"; value = <impl>; tests = { name = { expr; expected; }; }; }
  mk = { doc ? "", value, tests ? {} }: {
    _type = "nix-effects-api";
    inherit doc value tests;
  };

  # Recursively extract raw values, stripping mk wrappers.
  extractValue = x:
    if x ? _type && x._type == "nix-effects-api"
    then extractValue x.value
    else if builtins.isAttrs x && !(x ? _tag)
    then builtins.mapAttrs (_: extractValue) x
    else x;

  # Recursively extract all inline tests from nested mk wrappers.
  # Returns flat attrset: { "prefix.testName" = { expr; expected; }; ... }
  extractTests = prefix: x:
    let
      ownTests =
        if x ? _type && x._type == "nix-effects-api" && x.tests != {}
        then lib.mapAttrs' (name: test: {
          name = "${prefix}.${name}";
          value = test;
        }) x.tests
        else {};
      childTests =
        if x ? _type && x._type == "nix-effects-api" && builtins.isAttrs x.value
        then lib.foldl' (acc: key:
          acc // extractTests "${prefix}.${key}" x.value.${key}
        ) {} (builtins.attrNames x.value)
        else if builtins.isAttrs x && !(x ? _type) && !(x ? _tag)
        then lib.foldl' (acc: key:
          acc // extractTests "${prefix}.${key}" x.${key}
        ) {} (builtins.attrNames x)
        else {};
    in ownTests // childTests;

  # Recursively extract documentation from nested mk wrappers.
  # Returns hierarchical attrset: { doc, tests, fnName = { doc, tests }, subModule = { ... }, ... }
  # Unlike extractTests (flat, dotted prefixes), extractDocs preserves module hierarchy.
  # When a mk wrapper's value is itself an attrset of mk-wrapped functions (module pattern),
  # the inner docs are merged in alongside this node's own doc/tests.
  extractDocs = x:
    if x ? _type && x._type == "nix-effects-api"
    then
      { inherit (x) doc tests; } //
      (if builtins.isAttrs x.value && !(x.value ? _tag)
       then lib.filterAttrs (_: v: v != {})
            (builtins.mapAttrs (_: extractDocs) x.value)
       else {})
    else if builtins.isAttrs x && !(x ? _tag)
    then lib.filterAttrs (_: v: v != {})
         (builtins.mapAttrs (_: extractDocs) x)
    else {};

  # Run collected tests, returning { allPass, passed, failed, summary }.
  runTests = tests:
    let
      results = builtins.mapAttrs (name: test:
        let actual = test.expr; in
        { inherit name actual; expected = test.expected; pass = actual == test.expected; }
      ) tests;
      passedNames = lib.filterAttrs (_: r: r.pass) results;
      failedNames = lib.filterAttrs (_: r: !r.pass) results;
      nPassed = builtins.length (builtins.attrNames passedNames);
      nFailed = builtins.length (builtins.attrNames failedNames);
    in {
      inherit results;
      passed = passedNames;
      failed = failedNames;
      allPass = nFailed == 0;
      summary = "${toString nPassed} passed, ${toString nFailed} failed";
    };
}
