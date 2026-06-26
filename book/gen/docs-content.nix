# nix-effects docs content
#
# Produces a content directory of front-mattered markdown files keyed by
#   nix-effects/{section}/{page}.md
# Consumed by external documentation hubs (a sibling depot assembles
# this content into its serving tree). No assumptions about the hub
# leak into this file beyond the layout contract above.
#
# Each markdown file has YAML front matter with title.
# Merges hand-written guide chapters with auto-generated API docs from extractDocs.
#
# Output structure:
#   nix-effects/guide/introduction.md
#   nix-effects/guide/getting-started.md
#   nix-effects/guide/theory.md
#   nix-effects/guide/trampoline.md
#   nix-effects/core-api/kernel.md
#   nix-effects/core-api/trampoline.md
#   nix-effects/core-api/adapt.md
#   nix-effects/core-api/queue.md
#   nix-effects/effects/{state,error,...}.md
#   nix-effects/types/{foundation,primitives,...}.md
#   nix-effects/streams/{core,transform,...}.md

# requiredChecks: corpus -> gate derivations. Function-shaped so gates
# share this rendering instead of importing their own.
{ pkgs, lib, nix-effects, requiredChecks ? (_corpus: [ ]) }:

let
  docs = nix-effects.extractDocs;
  docsLib =
    if nix-effects ? docs
    then nix-effects.docs
    else import ../../src/docs.nix { api = import ../../src/api.nix { inherit lib; }; inherit lib; };
  exampleDocs = nix-effects.examplesDocs or { };
  bookSrc = ../src;
  nxSrc = ../../src;

  # mtime + sha data is optional; absent → null → front-matter key omitted.
  readJsonMap = path:
    if builtins.pathExists path
    then builtins.fromJSON (builtins.readFile path)
    else { };

  bookMtimes = readJsonMap (bookSrc + "/mtimes.json");
  bookShas = readJsonMap (bookSrc + "/shas.json");
  mtimeForBookFile = relPath: bookMtimes.${relPath} or null;
  shaForBookFile = relPath: bookShas.${relPath} or null;

  # Per-bucket mtimes + shas for auto-generated API pages. Keyed by first
  # path component under nix-effects/src/ (or `_root` for top-level .nix
  # files). Mtime value = max git_mtime across the bucket's files; sha
  # value = commit at that max-mtime file (the two agree by construction
  # in regenerate_mtimes.py).
  srcMtimes = readJsonMap (nxSrc + "/mtimes.json");
  srcShas = readJsonMap (nxSrc + "/shas.json");
  mtimeForSrcBucket = bucket: srcMtimes.${bucket} or null;
  shaForSrcBucket = bucket: srcShas.${bucket} or null;
  githubBase = "https://github.com/kleisli-io/nix-effects";
  githubBlob = relPath: "${githubBase}/blob/main/${relPath}";
  githubTree = relPath: "${githubBase}/tree/main/${relPath}";
  githubSourceLink = relPath: "[`${relPath}`](${githubBlob relPath})";
  githubSourceLineLink = relPath: line:
    "[`${relPath}:${toString line}`](${githubBlob relPath}#L${toString line})";

  inherit (docsLib) addFrontMatter metaKeys renderApiPage trimText;

  # Enumerate .nix files contributed by a split-module directory under
  # nix-effects/src/. Returns an empty list for non-split-module dirs (no
  # module.nix) and for missing paths. `module.nix` and `tests.nix` are
  # excluded (the former is the aggregator, the latter is test scaffolding).
  #
  # extractDocs strips internal scope from split modules (whose value is a
  # flat function attrset), so this list is the agent's only visibility into
  # which files contribute to the rendered page.
  sourceFilesFor = subPath:
    let
      dir = nxSrc + "/${subPath}";
      hasModuleNix = builtins.pathExists (dir + "/module.nix");
      entries =
        if hasModuleNix && builtins.pathExists dir
        then builtins.readDir dir
        else { };
      isContributing = name: type:
        type == "regular"
        && lib.hasSuffix ".nix" name
        && name != "module.nix"
        && name != "tests.nix";
      files = lib.filter (n: isContributing n entries.${n}) (builtins.attrNames entries);
    in
    map (f: "src/${subPath}/${f}") (lib.sort (a: b: a < b) files);

  renderSourceFilesSection = files:
    lib.optionalString (files != [ ])
      ("## Source\n\n"
        + lib.concatMapStrings (f: "- ${githubSourceLink f}\n") files
        + "\n");

  handwrittenSections = [
    {
      slug = "guide";
      title = "Guide";
      order = 1;
      description = "A practical path through nix-effects: start with imports and handlers, then move into typed validation, generated datatypes, ornaments, proofs, and syntax sugar.";
      introduction = ''
        The guide is the shortest path from using nix-effects to understanding
        the pieces that make it useful. Start with setup and handler basics,
        then follow the later chapters when you need typed validation,
        description-backed datatypes, ornaments, proofs, or syntax helpers.
      '';
      pages = [
        {
          slug = "introduction";
          title = "Introduction";
          description = "nix-effects is a typed, description-backed programming substrate for pure Nix that runs every check at nix eval time before anything builds.";
        }
        {
          slug = "getting-started";
          title = "Getting Started";
          description = "Install nix-effects as a flake input or direct import, define a first type with fx.types, and run a computation through fx.run with a handler.";
        }
        {
          slug = "effects-and-handlers";
          title = "Effects and Handlers";
          description = "Algebraic effects (send/bind/pure plus handlers) separate program intent from execution policy; the substrate underlies fx.types, diagnostics, and the checker.";
        }
        {
          slug = "typed-validation";
          title = "Typed Validation";
          description = "fx.types wraps Nix value predicates with kernel-backed type information; refinements layer guard predicates over structural checks via fx.refine.";
        }
        {
          slug = "generated-datatypes";
          title = "Generated Datatypes";
          description = "H.datatype generates a Nix record whose constructors, type, and description are reusable by the checker, generic walkers, schemas, and ornaments.";
        }
        {
          slug = "generic-programming";
          title = "Generic Programming";
          description = "fx.types.generic consumes the levitated Desc of generated datatypes so checker, derive, and schema agree by sharing one metadata tree per type.";
        }
        {
          slug = "ornaments";
          title = "Ornaments and Description-Backed Data";
          description = "Ornaments refine one generated datatype into another while preserving a forgetful map back, so enriched values stay usable wherever the base value fit.";
        }
        {
          slug = "proof-guide";
          title = "Proof Guide";
          description = "Build proofs in nix-effects from Refl through the J eliminator to verified extraction of plain Nix functions from kernel-checked HOAS terms via NbE.";
        }
        {
          slug = "sugar";
          title = "Sugar";
          description = "fx.sugar adds opt-in syntax (do, /, steps, letM, with, wrap) over the effect substrate; the kernel never imports it and removing it changes nothing.";
        }
      ];
    }
    {
      slug = "concepts";
      title = "Concepts";
      order = 2;
      description = "Background concepts behind nix-effects: handlers, freer monads, queues, normalization by evaluation, and description-backed data.";
      introduction = ''
        Concepts collects the theory that shapes the library. It is useful
        when you want the design vocabulary behind the implementation:
        algebraic effects, freer monads, queue-backed binds, normalization by
        evaluation, and levitated descriptions.
      '';
      pages = [
        {
          slug = "theory";
          title = "Theory";
          description = "Papers behind nix-effects: Plotkin-Pretnar handlers, the freer monad, FTCQueue, Martin-Lof type theory, normalization by evaluation, and levitated descriptions.";
        }
      ];
    }
    {
      slug = "internals";
      title = "Internals";
      order = 3;
      description = "Implementation notes for the evaluator, type-checking kernel, trampoline, architecture, and formal kernel contract.";
      introduction = ''
        Internals explains how nix-effects is put together. These pages cover
        the trampoline, the relationship between the effect layer and the
        type-checking kernel, the trusted computing boundary, and the formal
        contract maintained by the kernel.
      '';
      pages = [
        {
          slug = "trampoline";
          title = "Trampoline";
          description = "builtins.genericClosure trampolines the freer-monad interpreter to O(1) stack depth in Nix, which lacks both iteration primitives and tail-call elimination.";
        }
        {
          slug = "kernel-architecture";
          title = "Kernel Architecture";
          description = "The type-checking kernel layers a TCB (eval/quote/conv) under the bidirectional check/infer pair; errors are sent as typeError effects, not thrown.";
        }
        {
          slug = "kernel-spec";
          title = "Kernel Formal Specification";
          description = "Formal contract for the type-checking kernel: trust layers, typing rules, compute and conversion rules, and invariants the implementation must maintain.";
        }
      ];
    }
  ];

  handwrittenChapters = lib.concatMap
    (section:
      map (page: page // { section = section.slug; }) section.pages)
    handwrittenSections;

  chapterBySlug = builtins.listToAttrs
    (map (chapter: { name = chapter.slug; value = chapter; }) handwrittenChapters);

  manualSectionManifest = map
    (section: {
      inherit (section) slug title order;
      pages = map (page: page.slug) section.pages;
    })
    handwrittenSections;

  # Capitalise a module name for display: "state" -> "State", "acc" -> "Acc".
  capitalise = s:
    let
      first = builtins.substring 0 1 s;
      rest = builtins.substring 1 (builtins.stringLength s) s;
    in
    lib.toUpper first + rest;

  # Rewrite internal mdBook links (e.g. [Trampoline](trampoline.md)) to
  # the consumer's per-section route format
  # (`/<project>/<section>/<page>`).
  rewriteGuideLinks = body:
    builtins.replaceStrings
      (map (f: "](${f}.md)") (builtins.attrNames chapterBySlug))
      (map (f: "](/nix-effects/${chapterBySlug.${f}.section}/${f})")
        (builtins.attrNames chapterBySlug))
      body;

  # Generate linkFarm entries for hand-written chapters.
  guideEntries = map
    (chapter: {
      name = "nix-effects/${chapter.section}/${chapter.slug}.md";
      path = pkgs.writeText "${chapter.slug}.md"
        (addFrontMatter {
          title = chapter.title;
          body = rewriteGuideLinks (builtins.readFile (bookSrc + "/${chapter.slug}.md"));
          mtime = mtimeForBookFile "${chapter.slug}.md";
          sha = shaForBookFile "${chapter.slug}.md";
          description = chapter.description;
        });
    })
    handwrittenChapters;

  manualSectionIndexEntries = map
    (section: {
      name = "nix-effects/${section.slug}/index.md";
      path = pkgs.writeText "${section.slug}-index.md"
        (addFrontMatter {
          title = section.title;
          body = section.introduction;
          description = section.description;
        });
    })
    handwrittenSections;

  # Render the Hint registry as a markdown section. Used as an
  # `appendBody` on the diag/hints page to provide a single in-page
  # overview of the closed key set. The canonical per-key `docLink`
  # targets are the dedicated pages emitted by `diagHintsEntries`; this
  # registry remains as a navigable index on the hints module page.
  renderHintsRegistry = hintsRegistry:
    let
      sortedKeys = diagHintKeys;
      renderHintEntry = key:
        let h = hintsRegistry.${key};
        in ''
          ### ${key}

          Category: **${h.category}** · Severity: **${h.severity}**

          ${h.text}

        '';
    in
    "## Hint registry\n\n"
    + ''
      Diagnostic hints give stable names to recurring checker and validation
      failures. Use the per-hint pages when an error includes a `Hint::<key>`
      token, or scan the registry below to see the available hint keys.

    ''
    + lib.concatStrings (map renderHintEntry sortedKeys);

  # API section configuration. Single source of truth for the namespace
  # roots that mount under their own URL path; top-level modules not listed
  # here render under `core-api/`. Adding a new root is one row.
  apiSections = [
    {
      key = "diag";
      url = "diag";
      bucket = "diag";
      title = "Diagnostics";
    }
    {
      key = "effects";
      url = "effects";
      bucket = "effects";
      title = "Effects";
    }
    {
      key = "types";
      url = "types";
      bucket = "types";
      title = "Types";
    }
    {
      key = "stream";
      url = "streams";
      bucket = "stream";
      title = "Streams";
    }
    {
      key = "tc";
      url = "type-checker";
      bucket = "tc";
      title = "Type Checker";
    }
  ];
  sectionKeys = map (s: s.key) apiSections;

  # Decorate the doc tree with auxiliary content that the renderer treats
  # uniformly via `node.appendix`. The Hint registry attaches here so the
  # renderer needs no per-namespace special case. Hint records are stripped
  # from `extractDocs` by `_tag`-terminal recursion, so we read the raw
  # registry off `nix-effects.src`.
  hintsRegistry = nix-effects.src.diag.hints.hints or { };
  hintExamples = nix-effects.raw.value.diag.value.hints.docs.examples or { };
  augmentedDocs =
    if hintsRegistry == { } || !(docs ? diag) || !(docs.diag ? hints)
    then docs
    else
      lib.recursiveUpdate docs {
        diag.hints.appendix = renderHintsRegistry hintsRegistry;
      };

  # Rewrite `Hint::<key>` substrings in any doc body to a markdown link at
  # the per-key page `/nix-effects/diag-hints/<slug>`. The registry's own
  # `docLink` (computed by hints.nix:slugify) is the ground-truth target —
  # no slug logic is duplicated here.
  linkifyHints = doc:
    let
      keys = builtins.attrNames hintsRegistry;
      needles = map (k: "Hint::${k}") keys;
      replacements = map
        (k:
          let
            entry = hintsRegistry.${k};
            target = entry.docLink or "/nix-effects/diag/hints";
          in
          "[Hint::${k}](${target})"
        )
        keys;
    in
    if keys == [ ] then doc
    else builtins.replaceStrings needles replacements doc;

  # Emit one .md per Hint key under nix-effects/diag-hints/. Each page is
  # the canonical destination of `docLink` (set in hints.nix to
  # `${docBase}/${slugify key}`), so a compiler `Hint::<key>` resolves to
  # focused agent-readable content in one fetch. Consumers that scan the
  # layout pick these up as per-key resources with no further wiring.
  #
  # Slug derivation reuses the registry's own docLink (its last path
  # segment), avoiding any duplicate of hints.nix:slugify here.
  diagHintsMtime = mtimeForSrcBucket "diag";
  diagHintsSha = shaForSrcBucket "diag";
  slugOfHintKey = key:
    lib.last (lib.splitString "/" hintsRegistry.${key}.docLink);
  hintCategoryOrder = [
    "universe"
    "sort"
    "description"
    "arity"
    "indexing"
    "inhabitation"
    "refinement"
    "elimination"
    "type-mismatch"
    "shape"
  ];
  diagHintKeys =
    let
      keys = builtins.attrNames hintsRegistry;
      keysFor = category:
        lib.sort (a: b: a < b)
          (lib.filter (key: hintsRegistry.${key}.category == category) keys);
      selected = lib.concatMap keysFor hintCategoryOrder;
      rest = lib.filter (key: !(builtins.elem key selected)) keys;
    in
    selected ++ lib.sort (a: b: a < b) rest;
  diagHintsPages = map slugOfHintKey diagHintKeys;
  # Render an absolute source path as project-relative, e.g.
  # `src/diag/hints.nix`. Eval-time paths carry whatever absolute
  # prefix the caller's checkout uses; the docs site presents only
  # the path beneath the project root.
  projectRelativePath = absPath:
    let
      parts = lib.splitString "/nix-effects/" absPath;
    in
    if builtins.length parts >= 2
    then lib.last parts
    else absPath;
  diagHintsEntries =
    let
      renderHintPage = key:
        let
          h = hintsRegistry.${key};
          slug = slugOfHintKey key;
          pos = h.srcPosition or null;
          example = hintExamples.${key} or null;
          exampleCode = if example == null then "" else example.code or "";
          sourceLine =
            if pos == null then ""
            else "**Source:** ${githubSourceLineLink (projectRelativePath pos.file) pos.line}\n\n";
          exampleBlock =
            if example == null || exampleCode == "" then ""
            else ''
              ## Example

              ${example.prose}

              ```nix
              ${exampleCode}
              ```

            '';
          body = ''
            **Key:** `${key}`

            **Category:** ${h.category} · **Severity:** ${h.severity}

            ${sourceLine}${h.text}

            ${exampleBlock}
            ---

            [← All diagnostic hints](/nix-effects/diag-hints)
          '';
        in
        {
          name = "nix-effects/diag-hints/${slug}.md";
          path = pkgs.writeText "${slug}.md" (addFrontMatter {
            title = key;
            inherit body;
            mtime = diagHintsMtime;
            sha = diagHintsSha;
            description = h.description;
          });
        };
    in
    lib.optionals (hintsRegistry != { })
      (map renderHintPage diagHintKeys);

  diagHintsIndexEntry = lib.optional (hintsRegistry != { }) {
    name = "nix-effects/diag-hints/index.md";
    path = pkgs.writeText "diag-hints-index.md" (addFrontMatter {
      title = "Diagnostic Hints";
      description = "Stable diagnostic Hint keys for checker and validation failures, with focused pages for each emitted key.";
      body = ''
        Diagnostic hints are stable labels for recurring checker and validation
        failures. When an error includes a `Hint::<key>` token, the matching
        page explains what the key means and where to start debugging.

        Use this section when the raw error is too local and you need the
        larger shape of the failure: which kind of invariant was violated,
        what the checker was trying to establish, and what sort of change is
        usually relevant.

        Each hint page also points back to the source location that emits the
        hint.
      '';
    });
  };

  # A child node either renders inline (leaf, no documented descendants)
  # or as its own page (any documented descendant).
  isChild = k: v: !(builtins.elem k metaKeys) && builtins.isAttrs v;
  isLeafChild = c: lib.filterAttrs isChild c == { };

  orderNames = preferred: names:
    let
      selected = lib.filter (n: builtins.elem n names) preferred;
      rest = lib.filter (n: !(builtins.elem n preferred)) names;
    in
    selected ++ lib.sort (a: b: a < b) rest;

  preferredDocOrder = {
    "core-api" = [
      "kernel"
      "comp"
      "binds"
      "trampoline"
      "queue"
      "adapt"
      "pipeline"
      "state"
      "sugar"
      "build"
      "experimental"
    ];
    diag = [ "positions" "error" "hints" "pretty" ];
    effects = [
      "state"
      "reader"
      "writer"
      "acc"
      "error"
      "conditions"
      "choice"
      "scope"
      "linear"
      "typecheck"
      "hasHandler"
    ];
    types = [
      "foundation"
      "primitives"
      "constructors"
      "refinement"
      "dependent"
      "linear"
      "universe"
    ];
    streams = [ "core" "transform" "limit" "combine" "reduce" ];
    "type-checker" = [
      "term"
      "value"
      "quote"
      "conv"
      "eval"
      "check"
      "elaborate"
      "hoas"
      "surface"
      "generic"
      "verified"
    ];
    "type-checker/check" = [ "ctx" "type" "infer" "check" "bindP" "diag" ];
    "type-checker/check/diag" = [ "source_map" "shell" ];
    "type-checker/eval" = [ "core" "desc" ];
    "type-checker/elaborate" = [
      "core"
      "value"
      "quote"
      "eval-overlay"
      "conv"
      "effects"
      "meta"
      "insertion"
      "infer"
      "check"
      "extract"
      "runElab"
    ];
    "type-checker/elaborate/meta" = [
      "context"
      "meta"
      "eval"
      "constraints"
      "unify"
      "zonk"
    ];
    "type-checker/generic" = [
      "desc"
      "datatype"
      "value"
      "path"
      "derive"
      "check"
      "checkD"
      "ornaments"
    ];
    "type-checker/hoas" = [
      "source_map"
      "plicity"
      "forced"
      "desc"
      "datatype"
      "combinators"
      "decidable"
      "elaborate"
      "ornament"
    ];
    "type-checker/surface" = [
      "framework"
      "registry"
      "prelude"
      "handler-context"
      "implicit"
      "define-surface"
      "derive-parser"
      "derive-elaborator"
      "derive-printer"
      "define-ornament"
    ];
  };

  orderedDocNames = urlPath: attrs:
    orderNames
      (preferredDocOrder.${urlPath} or [ ])
      (builtins.attrNames attrs);

  # Top-level modules that aren't section roots. These render flatly under
  # `core-api/`. The filter excludes section keys and bare metadata.
  coreModuleNames =
    let
      names = builtins.filter
        (name: !(builtins.elem name sectionKeys)
          && !(builtins.elem name metaKeys)
          && builtins.isAttrs augmentedDocs.${name}
          && (augmentedDocs.${name} ? doc
          || augmentedDocs.${name} ? description))
        (builtins.attrNames augmentedDocs);
    in
    orderNames preferredDocOrder."core-api" names;

  hasOwnDoc = node:
    (node ? doc && node.doc != "")
    || (node ? description && node.description != "")
    || (node ? signature && node.signature != "");

  hasApiPageContent = node:
    let
      children = lib.filterAttrs isChild node;
      leafChildren = lib.filterAttrs (_: isLeafChild) children;
      nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;
    in
    hasOwnDoc node || leafChildren != { } || nestedChildren != { };

  nestedApiPagePaths = urlPath: node:
    let
      children = lib.filterAttrs isChild node;
      nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;
    in
    lib.concatLists (map
      (name:
        let
          child = nestedChildren.${name};
          childPath = "${urlPath}/${name}";
        in
        lib.optional (hasApiPageContent child) childPath
        ++ nestedApiPagePaths childPath child)
      (orderedDocNames urlPath nestedChildren));

  apiSectionPagePaths = sectionUrl: node:
    let
      children = lib.filterAttrs isChild node;
    in
    lib.concatLists (map
      (name:
        let
          child = children.${name};
          childPath = "${sectionUrl}/${name}";
        in
        lib.optional (hasApiPageContent child) name
        ++ map
          (path: lib.strings.removePrefix "${sectionUrl}/" path)
          (nestedApiPagePaths childPath child))
      (orderedDocNames sectionUrl children));

  # Recursive page emitter. One rule:
  #   - leaf children render as `## name` entries on this page;
  #   - nested children become their own pages reached via a
  #     "Sub-namespaces" link list at the bottom;
  #   - emit a page iff this node has any of {own doc, leaf entries,
  #     nested children}.
  # URL depth tracks doc-tree depth uniformly — no per-namespace dispatch,
  # arbitrarily deep nesting renders for free.
  walkApi = { urlPrefix, srcPath, node, mtime ? null, sha ? null }:
    let
      children = lib.filterAttrs isChild node;
      leafChildren = lib.filterAttrs (_: isLeafChild) children;
      nestedChildren = lib.filterAttrs (_: c: !(isLeafChild c)) children;

      hasOwnDoc = (node ? doc && node.doc != "")
        || (node ? description && node.description != "")
        || (node ? signature && node.signature != "");
      hasPageContent = hasOwnDoc || leafChildren != { } || nestedChildren != { };

      metaFields = lib.filterAttrs
        (k: _: builtins.elem k [ "doc" "description" "signature" ])
        node;
      pageNode = metaFields // leafChildren;

      subNamespaceSection =
        lib.optionalString (nestedChildren != { })
          ("## Sub-namespaces\n\n"
            + lib.concatStrings (map (n: "- [`${n}`](/${urlPrefix}/${n})\n")
            (orderedDocNames urlPrefix nestedChildren))
            + "\n");

      pageName = baseNameOf urlPrefix;
      selfPage = lib.optional hasPageContent {
        name = "${urlPrefix}.md";
        path = pkgs.writeText "${pageName}.md" (renderApiPage {
          title = capitalise pageName;
          node = pageNode;
          inherit mtime sha;
          namespacePath = "fx.${builtins.replaceStrings [ "/" ] [ "." ] srcPath}";
          subNamespaces = orderedDocNames urlPrefix nestedChildren;
          libraryName = "nix-effects";
          linkify = linkifyHints;
          sourceFilesSection = renderSourceFilesSection (sourceFilesFor srcPath);
          appendBody = (node.appendix or "") + subNamespaceSection;
        });
      };

      nestedPages = lib.concatLists (map
        (name: walkApi {
          urlPrefix = "${urlPrefix}/${name}";
          srcPath = "${srcPath}/${name}";
          node = nestedChildren.${name};
          inherit mtime sha;
        })
        (orderedDocNames urlPrefix nestedChildren));
    in
    selfPage ++ nestedPages;

  # Drive page generation from the doc tree. core-api/ holds top-level
  # un-sectioned modules; each row of `apiSections` mounts a namespace
  # root whose direct children are Tier-1 module pages and whose deeper
  # plain-namespace descendants become Tier-2 pages by the same walker.
  apiEntries =
    let
      corePages = lib.concatLists (map
        (name:
          walkApi {
            urlPrefix = "nix-effects/core-api/${name}";
            srcPath = name;
            node = augmentedDocs.${name};
            mtime = mtimeForSrcBucket "_root";
            sha = shaForSrcBucket "_root";
          }
        )
        coreModuleNames);

      sectionedPages = lib.concatLists (map
        (sec:
          let
            children = lib.filterAttrs isChild (augmentedDocs.${sec.key} or { });
          in
          lib.concatLists (map
            (childName: walkApi {
              urlPrefix = "nix-effects/${sec.url}/${childName}";
              srcPath = "${sec.key}/${childName}";
              node = children.${childName};
              mtime = mtimeForSrcBucket sec.bucket;
              sha = shaForSrcBucket sec.bucket;
            })
            (orderedDocNames sec.url children))
        )
        apiSections);
    in
    corePages ++ sectionedPages;

  trimMarkdown = s:
    lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } s);

  renderExampleSection = section:
    let
      prose = trimMarkdown (section.prose or "");
      code = trimMarkdown (section.code or "");
      proseBlock = lib.optionalString (prose != "") "${prose}\n\n";
      codeBlock = lib.optionalString (code != "") "```nix\n${code}\n```\n\n";
    in
    "## ${section.title}\n\n${proseBlock}${codeBlock}";

  renderExamplePage = { title, node, appendBody ? "" }:
    let
      intro = trimMarkdown (node.doc or "");
      introBlock = lib.optionalString (intro != "") "${intro}\n\n";
      sectionsBody = lib.concatStrings (map renderExampleSection (node.sections or [ ]));
    in
    addFrontMatter {
      inherit title;
      description = node.description or null;
      body = "${introBlock}${sectionsBody}${appendBody}";
    };

  walkExample = { urlPrefix, node }:
    let
      children = lib.filterAttrs isChild node;
      exampleChildOrder = {
        "nix-effects/surface-examples/stlc" = [
          "core"
          "sumsProducts"
          "recursiveLists"
          "refinementsDiagnostics"
        ];
      };
      childNames = orderNames
        (exampleChildOrder.${urlPrefix} or [ ])
        (builtins.attrNames children);
      title =
        if node ? title && node.title != ""
        then node.title
        else capitalise (baseNameOf urlPrefix);
      childLinks =
        lib.optionalString (children != { })
          ("## More walkthroughs\n\n"
            + lib.concatStrings (map
              (name:
                let
                  child = children.${name};
                  childTitle =
                    if child ? title && child.title != ""
                    then child.title
                    else capitalise name;
                in
                "- [${childTitle}](/${urlPrefix}/${name})\n")
              childNames)
            + "\n");
      selfPage = {
        name = "${urlPrefix}.md";
        path = pkgs.writeText "${baseNameOf urlPrefix}.md" (renderExamplePage {
          inherit title node;
          appendBody = childLinks;
        });
      };
      childPages = lib.concatLists (map
        (name: walkExample {
          urlPrefix = "${urlPrefix}/${name}";
          node = children.${name};
        })
        childNames);
    in
    [ selfPage ] ++ childPages;

  exampleGroupSpecs = [
    {
      slug = "proof-examples";
      title = "Proofs";
      description = "Kernel-checked proof walkthroughs: computation, equality reasoning, and verified extraction.";
      introduction = ''
        Proof examples show how HOAS terms become kernel-checked evidence and
        usable Nix values. Start with computational equality, then move to
        reusable equality combinators and verified function extraction.
      '';
      pages = [ "proofBasics" "equalityProofs" "verifiedFunctions" ];
    }
    {
      slug = "effect-examples";
      title = "Effects and Validation";
      description = "Effect-handler walkthroughs that show one computation running under multiple validation policies.";
      introduction = ''
        Effect examples keep the computation fixed and change the handler.
        This makes policy choices explicit: collect validation errors, log
        each check, or stop at the first failure.
      '';
      pages = [ "handlerSwapValidation" ];
    }
    {
      slug = "surface-examples";
      title = "Surface Languages";
      description = "Small source-language walkthroughs built over HOAS, refinements, diagnostics, and generated data.";
      introduction = ''
        Surface-language examples build a simply typed lambda calculus in
        layers. The core syntax introduces functions and application; later
        pages add products, sums, recursive lists, refinements, and diagnostics.
      '';
      pages = [ "stlc" ];
      navPages = [
        "stlc"
        "stlc/core"
        "stlc/sumsProducts"
        "stlc/recursiveLists"
        "stlc/refinementsDiagnostics"
      ];
    }
    {
      slug = "application-examples";
      title = "Applications";
      description = "Complete example programs that double as benchmark workloads.";
      introduction = ''
        Application examples are full modules rather than isolated snippets.
        They expose ordinary Nix APIs, include prose walkthroughs, and provide
        workload generators consumed by the benchmark suite.
      '';
      pages = [ "categoryTheory" "interp" "buildSim" ];
    }
  ];

  examplePageLink = sectionSlug: name:
    let
      node = exampleDocs.${name};
      pageTitle =
        if node ? title && node.title != ""
        then node.title
        else capitalise name;
      pageDescription =
        if node ? description && node.description != ""
        then ": ${node.description}"
        else "";
    in
    "- [${pageTitle}](/nix-effects/${sectionSlug}/${name})${pageDescription}\n";

  exampleGroupEntries = map
    (spec: {
      name = "nix-effects/${spec.slug}/index.md";
      path = pkgs.writeText "${spec.slug}-index.md" (renderExamplePage {
        title = spec.title;
        node = {
          description = spec.description;
          doc = spec.introduction + ''

            The source for this section lives under [examples/](${githubTree "examples"}).
          '';
          sections = [
            {
              title = "Walkthroughs";
              prose = lib.concatMapStrings (examplePageLink spec.slug) spec.pages;
              tests = [ ];
            }
          ];
        };
      });
    })
    exampleGroupSpecs;

  exampleOverviewLinks =
    "## Walkthrough groups\n\n"
    + lib.concatMapStrings
      (spec:
        "- [${spec.title}](/nix-effects/${spec.slug}) - ${spec.description}\n")
      exampleGroupSpecs
    + "\n";

  exampleOverviewEntry = {
    name = "nix-effects/examples/index.md";
    path = pkgs.writeText "examples-index.md" (renderExamplePage {
      title =
        if exampleDocs ? title && exampleDocs.title != ""
        then exampleDocs.title
        else "Examples";
      node = exampleDocs;
      appendBody = exampleOverviewLinks;
    });
  };

  exampleEntries = lib.concatLists (map
    (spec:
      lib.concatLists (map
        (name: walkExample {
          urlPrefix = "nix-effects/${spec.slug}/${name}";
          node = exampleDocs.${name};
        })
        spec.pages))
    exampleGroupSpecs);

  # project.json — standard contract for the documentation app to auto-discover
  # this project. Section ordering and reference flags are declared here so the
  # Lisp server needs zero project-specific code.
  # API Reference children derive from `apiSections` plus core-api.
  projectJson = builtins.toJSON {
    id = "nix-effects";
    name = "nix-effects";
    description = "Pure Nix effects, typed validation, verified boundaries, and description-backed DSLs.";
    source-url = "https://github.com/kleisli-io/nix-effects";
    index = "index.md";
    sections = [
      {
        title = "Manual";
        order = 1;
        children = manualSectionManifest;
      }
      {
        title = "Examples";
        order = 2;
        children = [
          {
            slug = "examples";
            title = "Overview";
            order = 1;
            pages = [ ];
          }
        ] ++ lib.imap1
          (i: spec: {
            slug = spec.slug;
            title = spec.title;
            order = i + 1;
            pages = spec.navPages or spec.pages;
          })
          exampleGroupSpecs;
      }
      {
        title = "API Reference";
        order = 3;
        reference = true;
        children = [
          {
            slug = "core-api";
            title = "Core API";
            order = 1;
            pages = coreModuleNames;
          }
        ] ++ lib.imap1
          (i: sec: {
            slug = sec.url;
            title = sec.title;
            order = i + 1;
            pages = apiSectionPagePaths sec.url (augmentedDocs.${sec.key} or { });
          })
          apiSections
        ++ lib.optional (hintsRegistry != { }) {
          slug = "diag-hints";
          title = "Diagnostic Hints";
          order = (builtins.length apiSections) + 2;
          pages = diagHintsPages;
        };
      }
    ];
  };

  projectEntry = {
    name = "nix-effects/project.json";
    path = pkgs.writeText "project.json" projectJson;
  };

  # Landing page content for docs.kleisli.io/nix-effects.
  # Rendered above section cards on the project page.
  indexEntry = {
    name = "nix-effects/index.md";
    path = pkgs.writeText "index.md"
      (addFrontMatter {
        title = "nix-effects";
        body = builtins.readFile (bookSrc + "/index.md");
        mtime = mtimeForBookFile "index.md";
        sha = shaForBookFile "index.md";
      });
  };

  rawCorpus = pkgs.linkFarm "nix-effects-docs-raw"
    ([ projectEntry indexEntry exampleOverviewEntry ] ++ guideEntries ++ manualSectionIndexEntries ++ exampleGroupEntries ++ exampleEntries ++ apiEntries ++ diagHintsIndexEntry ++ diagHintsEntries);

  checkDeps = lib.concatMapStringsSep "\n"
    (check: "test -e ${check}")
    (requiredChecks rawCorpus);

in
pkgs.runCommand "nix-effects-docs" { } ''
  set -eu
  ${checkDeps}
  mkdir -p "$out"
  cp -a ${rawCorpus}/. "$out/"
''
