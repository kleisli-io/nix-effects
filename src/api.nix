# nix-effects API layer
#
# Provides mk/extractValue/extractTests/extractDocs for documented module
# definitions. The mk { doc, value, tests } pattern is adapted from nfx by
# Victor Borja (https://github.com/vic/nfx), licensed under Apache-2.0.
#
# Every documented binding is wrapped via `api.mk` (or its aliases
# `api.leaf` / `api.namespace`). The wrap co-locates the binding's value
# with its `doc`/`description`/`signature`/`tests` metadata in a single
# record `{ _type = "nix-effects-api"; title; doc; description; signature;
# sections; value; tests; docHidden; }`. There is no sibling `__docs` map; "binding
# without doc" and "doc without binding" are structurally unrepresentable.
#
# `extractValue` strips wraps recursively to yield the public-API tree.
# `extractDocs` walks wraps to surface a hierarchical docs tree.
# `extractTests` flattens all inline `tests` blocks for `runTests`.
{ lib }:

rec {
  # Wrap a value with prose `doc`, one-line `description`, hand-authored
  # `signature`, optional walkthrough `sections`, and inline `tests`.
  # Empty defaults are inert.
  mk =
    { doc ? ""
    , title ? ""
    , description ? ""
    , signature ? ""
    , sections ? [ ]
    , value
    , tests ? { }
    , docHidden ? false
    }:
    {
      _type = "nix-effects-api";
      inherit title doc description signature sections value tests docHidden;
    };

  # Call-site aliases for `mk`. `leaf` documents a terminal binding;
  # `namespace` documents an attrset of further wraps. Same wrap shape.
  leaf = mk;
  namespace = mk;

  # Recursively extract raw values, stripping mk wrappers. The result is
  # the public-API view: bare values only, no wraps, no metadata.
  extractValue = x:
    if (x._type or null) == "nix-effects-api" then extractValue x.value
    else if builtins.isAttrs x && !(x ? _tag) && !(x ? _htag)
    then builtins.mapAttrs (_: extractValue) x
    else x;

  # Wrapped-child predicate: only mk wraps qualify. Non-recursive to
  # avoid cycles (parts referencing `self.X`).
  isApiChild = v:
    builtins.isAttrs v
    && !(v ? _tag)
    && (v._type or null) == "nix-effects-api";

  isDocChild = v:
    isApiChild v && !(v.docHidden or false);

  # Recursively extract all inline tests from nested mk wrappers.
  # Returns a hierarchical attrset; `runTests` flattens it.
  extractTests = x:
    if (x._type or null) == "nix-effects-api" then
      let
        ownTests = lib.mapAttrs'
          (name: test: { name = "test-${name}"; value = test; })
          x.tests;
        childTests =
          if builtins.isAttrs x.value
          then walkNsTests x.value
          else { };
      in
      ownTests // childTests
    else if builtins.isAttrs x && !(x ? _tag)
    then walkNsTests x
    else { };

  # Walk an untagged namespace attrset for tests in mk-wrapped children.
  walkNsTests = ns:
    let
      wrapped = lib.filterAttrs (_: v: isApiChild v) ns;
      rendered = lib.mapAttrs (_: extractTests) wrapped;
    in
    lib.filterAttrs (_: v: v != { }) rendered;

  # Recursively extract documentation from nested mk wrappers.
  # Returns hierarchical attrset:
  #   { title; doc; description; signature; sections; tests; <subName> = { ... }; ... }
  extractDocs = x:
    if (x._type or null) == "nix-effects-api" && !(x.docHidden or false)
    then
      { inherit (x) title doc description signature sections tests; } //
      (if builtins.isAttrs x.value && !(x.value ? _tag)
      then walkNsDocs x.value
      else { })
    else if builtins.isAttrs x && !(x ? _tag)
    then walkNsDocs x
    else { };

  # Walk an untagged namespace attrset for docs in mk-wrapped children.
  walkNsDocs = ns:
    let
      documented = lib.filterAttrs (_: v: isDocChild v) ns;
      rendered = lib.mapAttrs (_: extractDocs) documented;
    in
    lib.filterAttrs (_: v: v != { }) rendered;

  # Run collected tests, returning { passed, failed, summary, results }.
  # Handles nested namespaces from extractTests: recurses into attrsets
  # that lack `expr` (namespaces), runs leaf attrsets with `expr` + `expected`.
  runTests = tests:
    let
      # Flatten nested test tree into { "ns.sub.test-name" = { expr; expected; }; }
      flatten = prefix: attrs:
        lib.foldlAttrs
          (acc: name: value:
            let path = if prefix == "" then name else "${prefix}.${name}";
            in if builtins.isAttrs value && value ? expr && value ? expected
            then acc // { ${path} = value; }
            else if builtins.isAttrs value
            then acc // (flatten path value)
            else acc
          )
          { }
          attrs;
      flat = flatten "" tests;
      results = builtins.mapAttrs
        (name: test:
          let
            tried = builtins.tryEval test.expr;
            actual =
              if tried.success
              then tried.value
              else { __evalFailed = true; };
            compared =
              if tried.success
              then builtins.tryEval (tried.value == test.expected)
              else { success = false; value = false; };
            pass = compared.success && compared.value;
          in
          { inherit name actual; expected = test.expected; inherit pass; }
        )
        flat;
      passedNames = lib.filterAttrs (_: r: r.pass) results;
      failedNames = lib.filterAttrs (_: r: !r.pass) results;
      nPassed = builtins.length (builtins.attrNames passedNames);
      nFailed = builtins.length (builtins.attrNames failedNames);
    in
    {
      inherit results;
      passed = passedNames;
      failed = failedNames;
      summary = "${toString nPassed} passed, ${toString nFailed} failed";
    };
}
