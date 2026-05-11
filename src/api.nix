# nix-effects API layer
#
# Provides mk/extractValue/extractTests for structured module definitions.
# The mk { doc, value, tests } pattern is adapted from nfx by Victor Borja
# (https://github.com/vic/nfx), licensed under Apache-2.0.
{ lib }:

rec {
  # Wrap a value with documentation and inline tests.
  # Usage: mk { doc = "description"; value = <impl>; tests = { name = { expr; expected; }; }; }
  mk = { doc ? "", value, tests ? {} }: {
    _type = "nix-effects-api";
    inherit doc value tests;
  } // (lib.optionalAttrs (lib.isFunction value) { __functor = _self: value; });

  # Recursively extract raw values, stripping mk wrappers.
  extractValue = x:
    if x ? value && x._type or null == "nix-effects-api" then extractValue x.value
    else if builtins.isAttrs x && !(x ? _tag)
    then builtins.mapAttrs (_: extractValue) x
    else x;

  # Recursively extract all inline tests from nested mk wrappers.
  #
  # Traversal discipline:
  #   - mk-wrapped node (_type = "nix-effects-api"): take its own tests,
  #     then recurse into .value ONLY through mk-wrapped children. Plain
  #     data entries in .value (records, functions, primitives) are
  #     terminal — the module's scope is not a namespace.
  #   - Untagged attrset (readSrc namespace): recurse into every entry.
  #   - _tag-marked attrset (ADT instance) or non-attrset: terminal.
  #
  # The strictness in the mk-wrapped branch prevents plain records with
  # fields named `expr`/`expected` (e.g. a Detail default with
  # `expected = null`) from leaking into the test tree.
  extractTests = x:
    if (x._type or null) == "nix-effects-api" then
      let
        ownTests = lib.mapAttrs' (name: test: {
          name = "test-${name}";
          value = test;
        }) x.tests;
        childTests =
          if builtins.isAttrs x.value
          then lib.filterAttrs (_: v: v != {})
                (lib.mapAttrs (_: extractTests)
                  (lib.filterAttrs
                    (_: v: builtins.isAttrs v
                        && (v._type or null) == "nix-effects-api")
                    x.value))
          else {};
      in ownTests // childTests
    else if builtins.isAttrs x && !(x ? _tag)
    then lib.filterAttrs (_: v: v != {})
         (lib.mapAttrs (_: extractTests) x)
    else {};

  # Recursively extract documentation from nested mk wrappers.
  # Returns hierarchical attrset: { doc, tests, fnName = { doc, tests }, subModule = { ... }, ... }
  # Unlike extractTests (flat, dotted prefixes), extractDocs preserves module hierarchy.
  # When a mk wrapper's value is itself an attrset of mk-wrapped functions (module pattern),
  # the inner docs are merged in alongside this node's own doc/tests.
  extractDocs = x:
    if x ? value && x._type or null == "nix-effects-api"
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
  # Handles nested namespaces from extractTests: recurses into attrsets
  # that lack `expr` (namespaces), runs leaf attrsets with `expr` + `expected`.
  runTests = tests:
    let
      # Flatten nested test tree into { "ns.sub.test-name" = { expr; expected; }; }
      flatten = prefix: attrs:
        lib.foldlAttrs (acc: name: value:
          let path = if prefix == "" then name else "${prefix}.${name}";
          in if builtins.isAttrs value && value ? expr && value ? expected
             then acc // { ${path} = value; }
             else if builtins.isAttrs value
             then acc // (flatten path value)
             else acc
        ) {} attrs;
      flat = flatten "" tests;
      results = builtins.mapAttrs (name: test:
        let
          tried = builtins.tryEval test.expr;
          ok = tried.success;
          actual = if ok then tried.value else { __evalFailed = true; };
          pass = ok && actual == test.expected;
        in
        { inherit name actual; expected = test.expected; inherit pass; }
      ) flat;
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
