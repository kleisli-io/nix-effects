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

  # Render a module page from a node with shape:
  #   { doc?, tests?, fnName = { doc, tests }, ... }
  # Produces a markdown string with a title, module-level doc, and ## sections
  # for each documented entry.
  renderPage = title: node:
    let
      moduleDoc = lib.optionalString (node ? doc && node.doc != "")
        (lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } node.doc) + "\n\n");

      entries = lib.filterAttrs (k: _: k != "doc" && k != "tests") node;

      renderEntry = name: entry:
        lib.optionalString (entry ? doc)
          "## `${name}`\n\n${lib.removeSuffix "\n" (lib.trimWith { start = true; end = true; } entry.doc)}\n\n";

      body = lib.concatStringsSep "" (lib.mapAttrsToList renderEntry entries);
    in
    "# ${title}\n\n${moduleDoc}${body}";

  # A node is a directory-level container if it has no module-level doc.
  # Containers are not rendered as pages; their children are.
  isContainer = node: builtins.isAttrs node && !(node ? doc);

  # Recursively generate { name (relative path), path (store path) } entries.
  genEntries = prefix: node:
    lib.foldlAttrs (acc: key: value:
      if isContainer value
      then acc ++ genEntries "${prefix}${key}/" value
      else acc ++ [{
        name = "${prefix}${key}.md";
        path = pkgs.writeText "${key}.md" (renderPage key value);
      }]
    ) [] node;

in
  pkgs.linkFarm "nix-effects-api-docs" (genEntries "" docs)
