# nix-effects API doc generator
#
# Produces a linkFarm of per-module markdown files from extractDocs.
# Pure Nix string interpolation — no eval-in-build, no external tools.
#
# Output structure:
#   kernel.md, trampoline.md, adapt.md, queue.md
#   effects/state.md, effects/error.md, ...
#   types/foundation.md, types/primitives.md, ...
#   stream/core.md, stream/transform.md, ...
{ pkgs, lib, nix-effects }:

let
  docs = nix-effects.extractDocs;
  metaKeys = [ "title" "doc" "description" "signature" "sections" "tests" "appendix" ];

  # Render a module page from a node with shape:
  #   { doc?, tests?, fnName = { doc, tests }, ... }
  # Produces a markdown string with a title, module-level doc, and ## sections
  # for each documented entry.
  renderPage = title: node:
    let
      moduleDocText =
        if node ? doc && node.doc != "" then node.doc
        else node.description or "";
      moduleDoc = lib.optionalString (moduleDocText != "")
        (lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } moduleDocText) + "\n\n");

      entries = lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;

      renderEntry = name: entry:
        let
          hasDesc = entry ? description && entry.description != "";
          hasDoc = entry ? doc && entry.doc != "";
          hasSig = entry ? signature && entry.signature != "";
          trim = s: lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } s);
          descBlock = lib.optionalString hasDesc "_${trim entry.description}_\n\n";
          sigBlock = lib.optionalString hasSig "```\n${trim entry.signature}\n```\n\n";
          docBlock = lib.optionalString hasDoc "${trim entry.doc}\n\n";
        in
        lib.optionalString (hasDesc || hasDoc || hasSig)
          "## `${name}`\n\n${descBlock}${sigBlock}${docBlock}";

      body = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);
    in
    "# ${title}\n\n${moduleDoc}${body}";

  # A node is a directory-level container if it has no module-level doc.
  # Containers are not rendered as pages; their children are.
  isContainer = node:
    builtins.isAttrs node
    && !(node ? doc)
    && !(node ? description)
    && !(node ? signature);

  # Metadata fields describe the containing node, not child pages.
  children = node: lib.filterAttrs (k: _: !(builtins.elem k metaKeys)) node;

  # Recursively generate { name (relative path), path (store path) } entries.
  genEntries = prefix: node:
    lib.foldlAttrs
      (acc: key: value:
        if isContainer value
        then acc ++ genEntries "${prefix}${key}/" value
        else acc ++ [{
          name = "${prefix}${key}.md";
          path = pkgs.writeText "${key}.md" (renderPage key value);
        }]
      ) [ ]
      (children node);

in
pkgs.linkFarm "nix-effects-api-docs" (genEntries "" docs)
