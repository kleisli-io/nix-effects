# nix-effects docs content for kleisli-docs
#
# Produces a content directory matching kleisli-docs format:
#   nix-effects/{section}/{page}.md
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

{ pkgs, lib, nix-effects }:

let
  docs = nix-effects.extractDocs;
  bookSrc = ../src;
  nxSrc = ../../src;

  # mtime + sha data is optional; absent → null → front-matter key omitted.
  readJsonMap = path:
    if builtins.pathExists path
    then builtins.fromJSON (builtins.readFile path)
    else {};

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

  # Escape `\` and `"` for a YAML double-quoted scalar.
  yamlEscape = s: builtins.replaceStrings ["\\" "\""] ["\\\\" "\\\""] s;

  # Add YAML front matter to markdown content.
  # Strips a leading `# Title` from body to avoid duplicate heading.
  addFrontMatter = { title, body, mtime ? null, sha ? null, description ? null }:
    let
      # Strip leading "# Title\n\n" from body to avoid duplicate heading
      lines = lib.splitString "\n" body;
      firstLine = builtins.head lines;
      hasH1 = lib.hasPrefix "# " firstLine;
      strippedBody = if hasH1
        then
          let
            rest = builtins.tail lines;
            # Also strip leading blank line after the heading
            trimmed = if rest != [] && builtins.head rest == ""
              then builtins.tail rest
              else rest;
          in lib.concatStringsSep "\n" trimmed
        else body;
      mtimeLine = if mtime != null then "mtime: ${toString mtime}\n" else "";
      shaLine = if sha != null && sha != "" then "sha: ${sha}\n" else "";
      descriptionLine =
        if description != null && description != ""
        then "description: \"${yamlEscape description}\"\n"
        else "";
    in
    "---\ntitle: \"${title}\"\n${mtimeLine}${shaLine}${descriptionLine}---\n\n${strippedBody}";

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
        else {};
      isContributing = name: type:
        type == "regular"
        && lib.hasSuffix ".nix" name
        && name != "module.nix"
        && name != "tests.nix";
      files = lib.filter (n: isContributing n entries.${n}) (builtins.attrNames entries);
    in lib.sort (a: b: a < b) files;

  renderSourceFilesSection = files:
    lib.optionalString (files != [])
      ("## Source files\n\n"
       + "This module is built from multiple files; functions surface via the\n"
       + "module aggregator. The contributing source files are:\n\n"
       + lib.concatMapStrings (f: "- `${f}`\n") files
       + "\n");

  # Metadata keys present alongside documented children on a doc-tree node.
  # The walker treats these as scalar fields, not as candidate child pages/entries.
  metaKeys = [ "doc" "description" "signature" "tests" "appendix" ];

  # Render an API module page with front matter.
  # `sourceFiles` is an optional list of filenames; non-empty triggers a
  # "Source files" section, used for split-module pages where extractDocs
  # has collapsed internal structure to `{ doc, tests }`.
  # `appendBody` is markdown injected between the per-symbol entries and
  # the source-files footer; used by the diag/hints page to attach the
  # Hint registry and by the walker to attach sub-namespace navigation.
  renderApiPage = { title, node, mtime ? null, sha ? null, sourceFiles ? [], appendBody ? "" }:
    let
      moduleDoc = lib.optionalString (node ? doc && node.doc != "")
        (linkifyHints
          (lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } node.doc))
         + "\n\n");

      entries = lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;

      renderEntry = name: entry:
        let
          hasDesc = entry ? description && entry.description != "";
          hasDoc = entry ? doc && entry.doc != "";
          hasSig = entry ? signature && entry.signature != "";
          trim = s: lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } s);
          descBlock = lib.optionalString hasDesc "_${trim entry.description}_\n\n";
          sigBlock = lib.optionalString hasSig "```\n${trim entry.signature}\n```\n\n";
          docBlock = lib.optionalString hasDoc "${linkifyHints (trim entry.doc)}\n\n";
        in
        lib.optionalString (hasDesc || hasDoc || hasSig)
          "## `${name}`\n\n${descBlock}${sigBlock}${docBlock}";

      entriesBody = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);

      sourceFilesSection = renderSourceFilesSection sourceFiles;
    in
    addFrontMatter {
      inherit title mtime sha;
      description = node.description or null;
      body = "${moduleDoc}${entriesBody}${appendBody}${sourceFilesSection}";
    };

  handwrittenSections = [
    {
      slug = "guide";
      title = "Guide";
      order = 1;
      pages = [
        { slug = "introduction"; title = "Introduction"; }
        { slug = "getting-started"; title = "Getting Started"; }
        { slug = "effects-and-handlers"; title = "Effects and Handlers"; }
        { slug = "typed-validation"; title = "Typed Validation"; }
        { slug = "generated-datatypes"; title = "Generated Datatypes"; }
        { slug = "generic-programming"; title = "Generic Programming"; }
        { slug = "sugar"; title = "Sugar"; }
        { slug = "ornaments"; title = "Ornaments and Description-Backed Data"; }
        { slug = "proof-guide"; title = "Proof Guide"; }
      ];
    }
    {
      slug = "concepts";
      title = "Concepts";
      order = 2;
      pages = [
        { slug = "theory"; title = "Theory"; }
      ];
    }
    {
      slug = "internals";
      title = "Internals";
      order = 3;
      pages = [
        { slug = "trampoline"; title = "Trampoline"; }
        { slug = "systems-architecture"; title = "Systems Architecture"; }
        { slug = "kernel-architecture"; title = "Kernel Architecture"; }
        { slug = "kernel-spec"; title = "Kernel Formal Specification"; }
      ];
    }
  ];

  handwrittenChapters = lib.concatMap
    (section:
      map (page: page // { section = section.slug; }) section.pages)
    handwrittenSections;

  chapterBySlug = builtins.listToAttrs
    (map (chapter: { name = chapter.slug; value = chapter; }) handwrittenChapters);

  manualSectionManifest = map (section: {
    inherit (section) slug title order;
    pages = map (page: page.slug) section.pages;
  }) handwrittenSections;

  # Capitalise a module name for display: "state" -> "State", "acc" -> "Acc".
  capitalise = s:
    let
      first = builtins.substring 0 1 s;
      rest = builtins.substring 1 (builtins.stringLength s) s;
    in lib.toUpper first + rest;

  # Rewrite internal mdBook links (e.g. [Trampoline](trampoline.md)) to
  # kleisli-docs route format.
  rewriteGuideLinks = body:
    builtins.replaceStrings
      (map (f: "](${f}.md)") (builtins.attrNames chapterBySlug))
      (map (f: "](/nix-effects/${chapterBySlug.${f}.section}/${f})")
        (builtins.attrNames chapterBySlug))
      body;

  # Generate linkFarm entries for hand-written chapters.
  guideEntries = map (chapter: {
    name = "nix-effects/${chapter.section}/${chapter.slug}.md";
    path = pkgs.writeText "${chapter.slug}.md"
      (addFrontMatter {
        title = chapter.title;
        body = rewriteGuideLinks (builtins.readFile (bookSrc + "/${chapter.slug}.md"));
        mtime = mtimeForBookFile "${chapter.slug}.md";
        sha = shaForBookFile "${chapter.slug}.md";
      });
  }) handwrittenChapters;

  # Render the Hint registry as a markdown section. Used as an
  # `appendBody` on the diag/hints page to provide a single in-page
  # overview of the closed key set. The canonical per-key `docLink`
  # targets are the dedicated pages emitted by `diagHintsEntries`; this
  # registry remains as a navigable index on the hints module page.
  renderHintsRegistry = hintsRegistry:
    let
      sortedKeys = lib.sort (a: b: a < b) (builtins.attrNames hintsRegistry);
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
        The Hint table maps each *blame-path-suffix · classifier-pattern*
        key to a structured Hint record. Each subsection below
        corresponds to one such key; the canonical per-key page
        referenced by `hints.nix:docLink` lives under
        [/nix-effects/diag-hints/<slug>](/nix-effects/diag-hints).

      ''
      + lib.concatStrings (map renderHintEntry sortedKeys);

  # API section configuration. Single source of truth for the namespace
  # roots that mount under their own URL path; top-level modules not listed
  # here render under `core-api/`. Adding a new root is one row.
  apiSections = [
    { key = "diag";    url = "diag";         bucket = "diag";    title = "Diagnostics";
      banner = "Auto-generated API reference for the typed diagnostics namespace."; }
    { key = "effects"; url = "effects";      bucket = "effects"; title = "Effects";
      banner = "Auto-generated API reference from nix-effects source."; }
    { key = "types";   url = "types";        bucket = "types";   title = "Types";
      banner = "Auto-generated API reference from nix-effects source."; }
    { key = "stream";  url = "streams";      bucket = "stream";  title = "Streams";
      banner = "Auto-generated API reference from nix-effects source."; }
    { key = "tc";      url = "type-checker"; bucket = "tc";      title = "Type Checker";
      banner = "Auto-generated API reference from the MLTT type-checking kernel."; }
  ];
  sectionKeys = map (s: s.key) apiSections;

  # Decorate the doc tree with auxiliary content that the renderer treats
  # uniformly via `node.appendix`. The Hint registry attaches here so the
  # renderer needs no per-namespace special case. Hint records are stripped
  # from `extractDocs` by `_tag`-terminal recursion, so we read the raw
  # registry off `nix-effects.src`.
  hintsRegistry = nix-effects.src.diag.hints.hints or {};
  augmentedDocs =
    if hintsRegistry == {} || !(docs ? diag) || !(docs.diag ? hints)
    then docs
    else lib.recursiveUpdate docs {
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
      replacements = map (k:
        let entry = hintsRegistry.${k};
            target = entry.docLink or "/nix-effects/diag/hints";
        in "[Hint::${k}](${target})"
      ) keys;
    in if keys == [] then doc
       else builtins.replaceStrings needles replacements doc;

  # Emit one .md per Hint key under nix-effects/diag-hints/. Each page is
  # the canonical destination of `docLink` (set in hints.nix to
  # `${docBase}/${slugify key}`), so a compiler `Hint::<key>` resolves to
  # focused agent-readable content in one fetch. scan-docs picks these up
  # automatically (kleisli-docs/src/content.lisp:254), giving us
  # `docs://kleisli/nix-effects/diag-hints/<slug>` MCP resources via the
  # existing register-doc-resources maphash with no Lisp changes.
  #
  # Slug derivation reuses the registry's own docLink (its last path
  # segment), avoiding any duplicate of hints.nix:slugify here.
  diagHintsMtime = mtimeForSrcBucket "diag";
  diagHintsSha = shaForSrcBucket "diag";
  slugOfHintKey = key:
    lib.last (lib.splitString "/" hintsRegistry.${key}.docLink);
  diagHintsPages = lib.sort (a: b: a < b)
    (map slugOfHintKey (builtins.attrNames hintsRegistry));
  diagHintsEntries =
    let
      renderHintPage = key:
        let h = hintsRegistry.${key};
            slug = slugOfHintKey key;
            body = ''
              **Key:** `${key}`

              **Category:** ${h.category} · **Severity:** ${h.severity}

              ${h.text}
            '';
        in {
          name = "nix-effects/diag-hints/${slug}.md";
          path = pkgs.writeText "${slug}.md" (addFrontMatter {
            title = key;
            inherit body;
            mtime = diagHintsMtime;
            sha = diagHintsSha;
          });
        };
    in lib.optionals (hintsRegistry != {})
         (map renderHintPage
              (lib.sort (a: b: a < b) (builtins.attrNames hintsRegistry)));

  # A child node either renders inline (leaf, no documented descendants)
  # or as its own page (any documented descendant).
  isChild = k: v: !(builtins.elem k metaKeys) && builtins.isAttrs v;
  isLeafChild = c: lib.filterAttrs isChild c == {};

  documentedNames = node:
    lib.sort (a: b: a < b)
      (builtins.attrNames (lib.filterAttrs isChild node));

  # Top-level modules that aren't section roots. These render flatly under
  # `core-api/`. The filter excludes section keys and bare metadata.
  coreModuleNames = lib.sort (a: b: a < b) (builtins.filter
    (name: !(builtins.elem name sectionKeys)
           && !(builtins.elem name metaKeys)
           && builtins.isAttrs augmentedDocs.${name}
           && (augmentedDocs.${name} ? doc
               || augmentedDocs.${name} ? description))
    (builtins.attrNames augmentedDocs));

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
      hasPageContent = hasOwnDoc || leafChildren != {} || nestedChildren != {};

      metaFields = lib.filterAttrs
        (k: _: builtins.elem k [ "doc" "description" "signature" ]) node;
      pageNode = metaFields // leafChildren;

      subNamespaceSection =
        lib.optionalString (nestedChildren != {})
          ("## Sub-namespaces\n\n"
           + lib.concatStrings (map (n: "- [`${n}`](/${urlPrefix}/${n})\n")
                                     (lib.sort (a: b: a < b)
                                       (builtins.attrNames nestedChildren)))
           + "\n");

      pageName = baseNameOf urlPrefix;
      selfPage = lib.optional hasPageContent {
        name = "${urlPrefix}.md";
        path = pkgs.writeText "${pageName}.md" (renderApiPage {
          title = capitalise pageName;
          node = pageNode;
          inherit mtime sha;
          sourceFiles = sourceFilesFor srcPath;
          appendBody = (node.appendix or "") + subNamespaceSection;
        });
      };

      nestedPages = lib.concatLists (lib.mapAttrsToList
        (name: child: walkApi {
          urlPrefix = "${urlPrefix}/${name}";
          srcPath = "${srcPath}/${name}";
          node = child;
          inherit mtime sha;
        }) nestedChildren);
    in selfPage ++ nestedPages;

  # Drive page generation from the doc tree. core-api/ holds top-level
  # un-sectioned modules; each row of `apiSections` mounts a namespace
  # root whose direct children are Tier-1 module pages and whose deeper
  # plain-namespace descendants become Tier-2 pages by the same walker.
  apiEntries =
    let
      corePages = lib.concatLists (map (name:
        walkApi {
          urlPrefix = "nix-effects/core-api/${name}";
          srcPath = name;
          node = augmentedDocs.${name};
          mtime = mtimeForSrcBucket "_root";
          sha = shaForSrcBucket "_root";
        }
      ) coreModuleNames);

      sectionedPages = lib.concatLists (map (sec:
        lib.concatLists (lib.mapAttrsToList
          (childName: childNode: walkApi {
            urlPrefix = "nix-effects/${sec.url}/${childName}";
            srcPath = "${sec.key}/${childName}";
            node = childNode;
            mtime = mtimeForSrcBucket sec.bucket;
            sha = shaForSrcBucket sec.bucket;
          })
          (lib.filterAttrs isChild (augmentedDocs.${sec.key} or {})))
      ) apiSections);
    in corePages ++ sectionedPages;

  # project.json — standard contract for the documentation app to auto-discover
  # this project. Section ordering, reference flags, and banner templates
  # are all declared here so the Lisp server needs zero project-specific code.
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
        title = "API Reference";
        order = 2;
        reference = true;
        children = [
          { slug = "core-api"; title = "Core API"; order = 1;
            pages = coreModuleNames;
            banner = "Auto-generated API reference from nix-effects source."; }
        ] ++ lib.imap1 (i: sec: {
          slug = sec.url;
          title = sec.title;
          order = i + 1;
          pages = documentedNames (augmentedDocs.${sec.key} or {});
          inherit (sec) banner;
        }) apiSections
        ++ lib.optional (hintsRegistry != {}) {
          slug = "diag-hints";
          title = "Diagnostic Hints";
          order = (builtins.length apiSections) + 2;
          pages = diagHintsPages;
          banner = "Per-key diagnostic Hint pages, one per blame-path-suffix · classifier-pattern key — each compiler `Hint::<key>` resolves to its own page in one fetch.";
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

in
  pkgs.linkFarm "nix-effects-kleisli-docs"
    ([ projectEntry indexEntry ] ++ guideEntries ++ apiEntries ++ diagHintsEntries)
