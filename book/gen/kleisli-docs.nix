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

  # Add YAML front matter to markdown content.
  # Strips leading "# Title\n" from body if present (since title is in front matter).
  addFrontMatter = title: body:
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
    in
    "---\ntitle: \"${title}\"\n---\n\n${strippedBody}";

  # Render an API module page with front matter.
  renderApiPage = title: node:
    let
      moduleDoc = lib.optionalString (node ? doc && node.doc != "")
        (lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } node.doc) + "\n\n");

      entries = lib.filterAttrs (k: _: k != "doc" && k != "tests") node;

      renderEntry = name: entry:
        lib.optionalString (entry ? doc)
          "## `${name}`\n\n${lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } entry.doc)}\n\n";

      body = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);
    in
    addFrontMatter title "${moduleDoc}${body}";

  # Map of hand-written chapters to their display titles.
  guideChapters = {
    introduction = "Introduction";
    getting-started = "Getting Started";
    theory = "Theory";
    trampoline = "Trampoline";
  };

  # Capitalise a module name for display: "state" -> "State", "acc" -> "Acc".
  capitalise = s:
    let
      first = builtins.substring 0 1 s;
      rest = builtins.substring 1 (builtins.stringLength s) s;
    in lib.toUpper first + rest;

  # Rewrite internal mdBook links (e.g. [Trampoline](trampoline.md)) to
  # kleisli-docs route format (/nix-effects/guide/trampoline).
  rewriteGuideLinks = body:
    builtins.replaceStrings
      (map (f: "](${f}.md)") (builtins.attrNames guideChapters))
      (map (f: "](/nix-effects/guide/${f})") (builtins.attrNames guideChapters))
      body;

  # Generate linkFarm entries for hand-written guide chapters.
  guideEntries = lib.mapAttrsToList (filename: title: {
    name = "nix-effects/guide/${filename}.md";
    path = pkgs.writeText "${filename}.md"
      (addFrontMatter title (rewriteGuideLinks (builtins.readFile (bookSrc + "/${filename}.md"))));
  }) guideChapters;

  # Generate linkFarm entries for API docs.
  # Maps extractDocs tree structure to flat section directories.
  apiEntries =
    let
      # Core API modules — derived dynamically from extractDocs.
      # Everything at the top level that isn't a sub-namespace container
      # (effects, types, stream) and has documentation.
      subNamespaces = [ "effects" "types" "stream" ];
      coreModules = builtins.filter
        (name: !(builtins.elem name subNamespaces)
               && builtins.isAttrs docs.${name}
               && docs.${name} ? doc)
        (builtins.attrNames docs);
      coreEntries = builtins.filter (e: e != null) (map (name:
        if docs ? ${name} then {
          name = "nix-effects/core-api/${name}.md";
          path = pkgs.writeText "${name}.md" (renderApiPage (capitalise name) docs.${name});
        } else null
      ) coreModules);

      # Effects modules
      effectsEntries = lib.optionals (docs ? effects)
        (lib.mapAttrsToList (name: node: {
          name = "nix-effects/effects/${name}.md";
          path = pkgs.writeText "${name}.md" (renderApiPage (capitalise name) node);
        }) (lib.filterAttrs (k: v: builtins.isAttrs v && v ? doc) docs.effects));

      # Types modules
      typesEntries = lib.optionals (docs ? types)
        (lib.mapAttrsToList (name: node: {
          name = "nix-effects/types/${name}.md";
          path = pkgs.writeText "${name}.md" (renderApiPage (capitalise name) node);
        }) (lib.filterAttrs (k: v: builtins.isAttrs v && v ? doc) docs.types));

      # Stream modules
      streamEntries = lib.optionals (docs ? stream)
        (lib.mapAttrsToList (name: node: {
          name = "nix-effects/streams/${name}.md";
          path = pkgs.writeText "${name}.md" (renderApiPage (capitalise name) node);
        }) (lib.filterAttrs (k: v: builtins.isAttrs v && v ? doc) docs.stream));

    in coreEntries ++ effectsEntries ++ typesEntries ++ streamEntries;

  # project.json — standard contract for the doc service to auto-discover
  # this project. Section ordering, reference flags, and banner templates
  # are all declared here so the Lisp server needs zero project-specific code.
  projectJson = builtins.toJSON {
    id = "nix-effects";
    name = "nix-effects";
    description = "Algebraic effects, dependent contracts, and refinement types in pure Nix.";
    source-url = "https://github.com/kleisli-io/nix-effects";
    sections = [
      { slug = "guide"; title = "Guide"; order = 1; }
      { slug = "core-api"; title = "Core API"; order = 2;
        reference = true;
        banner = "Auto-generated API reference from nix-effects source."; }
      { slug = "effects"; title = "Effects"; order = 3;
        reference = true;
        banner = "Auto-generated API reference from nix-effects source."; }
      { slug = "types"; title = "Types"; order = 4;
        reference = true;
        banner = "Auto-generated API reference from nix-effects source."; }
      { slug = "streams"; title = "Streams"; order = 5;
        reference = true;
        banner = "Auto-generated API reference from nix-effects source."; }
    ];
  };

  projectEntry = {
    name = "nix-effects/project.json";
    path = pkgs.writeText "project.json" projectJson;
  };

in
  pkgs.linkFarm "nix-effects-kleisli-docs" ([ projectEntry ] ++ guideEntries ++ apiEntries)
