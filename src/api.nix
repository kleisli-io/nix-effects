# nix-effects API layer
#
# Provides mk/extractValue/extractTests/extractDocs for structured module
# definitions. The mk { doc, value, tests } pattern is adapted from nfx by
# Victor Borja (https://github.com/vic/nfx), licensed under Apache-2.0.
#
# Two co-existing documentation conventions:
#
#   (a) `mk`-wrapped values  — the historical pattern. `api.mk { doc; value;
#       tests; ... }` returns an opaque record whose own metadata fields
#       (`_type`, `doc`, `description`, `signature`, `tests`, `value`) carry
#       the documentation. Internal callers that need the underlying value
#       read `.value`.
#
#   (b) `__docs` sibling     — the new pattern. At any namespace level, a
#       reserved `__docs` key may carry metadata for the sibling bindings:
#         {
#           foo = <bare value>;
#           bar = <bare value>;
#           __docs = {
#             foo = { doc = "..."; signature = "..."; tests = {...}; };
#             bar = { description = "..."; };
#           };
#         }
#       The value tree stays clean (`foo` IS the value, no wrap, no `.value`
#       tax). `__docs` is consumed only by `extractDocs`/`extractTests`;
#       `extractValue` skips it so it never appears in the public API tree.
#
# Both conventions are recognised by `extractDocs`/`extractTests`/
# `extractValue` so the codebase can migrate per file. New code should prefer
# (b); legacy `mk` wraps remain valid.
{ lib }:

rec {
  # Reserved sibling key carrying per-binding documentation at any namespace
  # level. Excluded from `extractValue` so it doesn't appear in the public API
  # tree; consumed by `extractDocs`/`extractTests`.
  reservedDocsKey = "__docs";

  # Wrap a value with prose `doc`, one-line `description`, hand-authored
  # `signature`, and inline `tests`. Empty defaults are inert.
  mk = { doc ? "", description ? "", signature ? "", value, tests ? {} }: {
    _type = "nix-effects-api";
    inherit doc description signature value tests;
  };

  # Split-module entry point. Called by `module.nix` in directories with
  # parts. Takes the curated public `value` (possibly nested via mk-wrapped
  # sub-namespaces), the flat `partDocs` aggregated by `readSrc`, and the
  # module-level `description`/`doc`/`tests`. Enforces the mutually-strict
  # invariant `flat-leaf-key-set of value == attrNames partDocs` — every
  # publicly-exposed binding is documented by exactly one part, every
  # documented key is publicly exposed. Then injects `__docs` at each
  # namespace level (top-level for top-level leaves, inside each
  # sub-namespace's `value` for sub-namespace leaves) and wraps the result
  # with `mk`.
  #
  # A "leaf binding" is a key whose value is NOT an `mk` wrap. A
  # sub-namespace is an `mk`-wrapped attrset whose `value` contains its
  # own leaves and/or further sub-namespaces. The walker recurses through
  # sub-namespace wraps to gather all leaves transitively.
  mkModule = { description ? "", doc ? "", value, tests ? {}, partDocs }:
    let
      # Two flavours of mk-wrapped attrset appear in a `value` tree:
      #
      # (a) An *inline sub-namespace* — created right here in
      #     module.nix's `value` block via `api.mk { value = { inherit
      #     (self) … }; … }`. Its `.value` is a bare attrset with no
      #     `__docs` yet; THIS mkModule call owns the docs for those
      #     leaves and must enumerate and inject them.
      #
      # (b) A *finalized sub-module* — the result of a nested
      #     `mkModule` call (readSrc found a child subdir with its own
      #     module.nix). Its `.value` already carries an injected
      #     `__docs`; the child has documented its own leaves. The
      #     parent must NOT recurse: it treats this key as a single
      #     leaf, documented by the parent's own `partDocs.<key>`.
      #
      # The discriminator: presence of an already-injected `__docs`
      # inside `.value`. Inline sub-namespaces never carry it (mkModule
      # is the only injector); finalized children always do.
      isInlineSubNamespace = x:
        builtins.isAttrs x
        && (x._type or null) == "nix-effects-api"
        && builtins.isAttrs x.value
        && (x.value._type or null) != "nix-effects-api"
        && !(x.value ? ${reservedDocsKey});

      # A finalized sub-module carries its own `description`/`doc` on
      # its top-level mk-wrap (from its own `mkModule` call). The
      # parent inherits those as the namespace's documentation; it
      # need not (and should not) redocument the child. These keys
      # count as documented for the strict invariant. The
      # discriminator: an mk-wrap whose `.value` already carries an
      # injected `__docs`.
      isFinalizedSubModule = x:
        builtins.isAttrs x
        && (x._type or null) == "nix-effects-api"
        && builtins.isAttrs x.value
        && (x.value ? ${reservedDocsKey});

      # Transitively collect leaf descriptors: descend ONLY through
      # inline sub-namespaces. Each leaf carries its key plus a flag
      # for whether it's a finalized sub-module (auto-documented).
      collectLeavesAnno = v:
        lib.concatMap (k:
          if isInlineSubNamespace v.${k}
          then collectLeavesAnno v.${k}.value
          else [ { name = k; isFinalized = isFinalizedSubModule v.${k}; } ]
        ) (builtins.attrNames v);

      leavesAnno  = collectLeavesAnno value;
      leafKeys    = map (e: e.name) leavesAnno;
      autoDocKeys = map (e: e.name) (lib.filter (e: e.isFinalized) leavesAnno);
      docKeys     = builtins.attrNames partDocs;

      extra   = lib.subtractLists leafKeys docKeys;
      missing = lib.subtractLists (docKeys ++ autoDocKeys) leafKeys;

      # Inject `__docs` at each level: pick the partDocs entries whose keys
      # match leaves at this level, recurse into sub-namespaces. partDocs
      # is FLAT (keyed by binding name only) — leaves carry unique names
      # across the whole split-module group, so per-level filtering picks
      # exactly the right entries.
      inject = v:
        let
          ks           = builtins.attrNames v;
          parts        = lib.partition (k: isInlineSubNamespace v.${k}) ks;
          subKeys      = parts.right;
          leafKeysHere = parts.wrong;
          leafDocsHere = lib.filterAttrs
                           (k: _: builtins.elem k leafKeysHere) partDocs;
          recursedSubs = builtins.listToAttrs (map (k: {
            name  = k;
            value = let w = v.${k}; in w // { value = inject w.value; };
          }) subKeys);
        in
          (lib.getAttrs leafKeysHere v) // recursedSubs //
          (if leafDocsHere != {}
           then { ${reservedDocsKey} = leafDocsHere; }
           else {});
    in
      if extra != []
      then throw "api.mkModule: docs declared for non-public binding(s): ${toString extra}"
      else if missing != []
      then throw "api.mkModule: public binding(s) without docs: ${toString missing}"
      else mk {
        inherit description doc tests;
        value = inject value;
      };

  # Recursively extract raw values, stripping mk wrappers and skipping
  # `__docs` siblings. The result is the public-API view: bare values only,
  # no wraps, no documentation metadata.
  extractValue = x:
    if (x._type or null) == "nix-effects-api" then extractValue x.value
    else if builtins.isAttrs x && !(x ? _tag)
    then builtins.mapAttrs (_: extractValue)
           (removeAttrs x [ reservedDocsKey ])
    else x;

  # `__docs`-bearing detection: does this value carry documentation that
  # should appear in the docs tree?
  #
  # Non-recursive — must not call itself, because the value tree contains
  # cycles (parts referencing `self.X`); a recursive predicate would walk
  # them forever.
  #
  # A value qualifies if:
  #   - It is mk-wrapped, OR
  #   - It has a direct `__docs` sibling carrying any entries.
  isDocChild = v:
    builtins.isAttrs v
    && !(v ? _tag)
    && ( (v._type or null) == "nix-effects-api"
         || (v ? ${reservedDocsKey} && v.${reservedDocsKey} != {}));

  # Recursively extract all inline tests from nested mk wrappers AND
  # `__docs` siblings.
  #
  # Traversal discipline:
  #   - mk-wrapped node: take its own `tests`, then recurse into `value`
  #     using the namespace-walking rules below.
  #   - Untagged attrset (readSrc namespace, or any plain ns): for each
  #     sibling name, take `__docs.<name>.tests` if present, then recurse
  #     into the binding for nested tests. Only documenting children
  #     (mk-wrapped, or transitively containing wraps / `__docs`) are walked,
  #     so plain payload records don't leak.
  #   - `_tag`-marked attrset (ADT instance) or non-attrset: terminal.
  extractTests = x:
    if (x._type or null) == "nix-effects-api" then
      let
        ownTests = lib.mapAttrs' (name: test: {
          name = "test-${name}";
          value = test;
        }) x.tests;
        childTests =
          if builtins.isAttrs x.value
          then walkNsTests x.value
          else {};
      in ownTests // childTests
    else if builtins.isAttrs x && !(x ? _tag)
    then walkNsTests x
    else {};

  # Walk an untagged namespace attrset for tests. For each non-`__docs`
  # child name: collect `__docs.<name>.tests` (sibling-declared) and
  # recurse into the child for any further nested tests.
  walkNsTests = ns:
    let
      docs = ns.${reservedDocsKey} or {};
      children = removeAttrs ns [ reservedDocsKey ];
      perName = name: value:
        let
          # Sibling-declared inline tests for this name.
          siblingTests =
            if docs ? ${name} && docs.${name} ? tests
            then lib.mapAttrs' (tname: t: {
              name = "test-${tname}";
              value = t;
            }) docs.${name}.tests
            else {};
          # Nested tests reachable through this child (legacy wraps, or
          # nested __docs siblings deeper in the tree).
          nested = extractTests value;
        in siblingTests // nested;
      # Descend only into documenting children OR children with sibling docs.
      documented = lib.filterAttrs
        (name: v: (docs ? ${name}) || isDocChild v)
        children;
      rendered = lib.mapAttrs perName documented;
    in lib.filterAttrs (_: v: v != {}) rendered;

  # Recursively extract documentation from nested mk wrappers AND `__docs`
  # siblings. Returns a hierarchical attrset:
  #   { doc; description; signature; tests; <subName> = { ... }; ... }
  # Output keys preserve module hierarchy (unlike `extractTests`'s flat
  # dotted names).
  extractDocs = x:
    if (x._type or null) == "nix-effects-api"
    then
      { inherit (x) doc description signature tests; } //
      (if builtins.isAttrs x.value && !(x.value ? _tag)
       then walkNsDocs x.value
       else {})
    else if builtins.isAttrs x && !(x ? _tag)
    then walkNsDocs x
    else {};

  # Walk an untagged namespace attrset for docs. For each non-`__docs`
  # child name: take direct metadata from `__docs.<name>` (sibling
  # declaration), then merge with what `extractDocs` finds inside the
  # child (legacy wrap, or nested `__docs`). Sibling-declared metadata
  # wins for the four documented fields; the child's recursion
  # contributes nested children.
  walkNsDocs = ns:
    let
      docs = ns.${reservedDocsKey} or {};
      children = removeAttrs ns [ reservedDocsKey ];
      perName = name: value:
        let
          # When a sibling declaration exists for this name, emit all four
          # documented fields with empty defaults — matching legacy `mk`'s
          # uniform shape ({ doc; description; signature; tests; ... }) so
          # downstream consumers see a stable schema regardless of which
          # convention the source file uses.
          siblingMeta =
            if docs ? ${name}
            then
              let d = docs.${name}; in {
                doc         = d.doc or "";
                description = d.description or "";
                signature   = d.signature or "";
                tests       = d.tests or {};
              }
            else {};
          nested = extractDocs value;
        in
          siblingMeta // (lib.filterAttrs (k: _: !(siblingMeta ? ${k})) nested);
      documented = lib.filterAttrs
        (name: v: (docs ? ${name}) || isDocChild v)
        children;
      rendered = lib.mapAttrs perName documented;
    in lib.filterAttrs (_: v: v != {}) rendered;

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
