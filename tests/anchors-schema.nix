# Schema-driven anchor-stability check for diag Hints.
#
# Asserts a three-axis invariant against the kleisli-docs content derivation,
# using the Hint registry (`src.diag.hints.hints`) as the single source of
# truth:
#
#   1. Path axis: every Hint key K has a `nix-effects/diag-hints/<slug>.md`
#      file in the derivation, where `slug = lastPath hint.docLink` — the same
#      rule `book/gen/kleisli-docs.nix:319` uses to emit pages. The rule lives
#      once in the renderer; the test reuses `hint.docLink` directly, so no
#      slugify logic is duplicated here.
#   2. In-page anchor axis: every Hint key K has a `### K` heading in
#      `nix-effects/diag/hints.md` (the in-page registry overview).
#   3. No-orphans axis: the number of files under `nix-effects/diag-hints/`
#      equals `length (attrNames hints)` — catches a page lingering after its
#      key is dropped from the registry.
#
# Build:
#   nix-build -A tests.anchors-schema
#
# Failure semantics: any failed axis exits before `$out` is written, so the
# Nix build itself fails with the diagnostic in stderr.
{ pkgs, lib, src, kleisliDocs }:

let
  hints = src.diag.hints.hints;
  keys = builtins.attrNames hints;
  slugOf = k: lib.last (lib.splitString "/" hints.${k}.docLink);

  perKeyChecks = lib.concatMapStringsSep "\n" (k:
    let slug = slugOf k; in ''
      if [ ! -f "${kleisliDocs}/nix-effects/diag-hints/${slug}.md" ]; then
        echo "FAIL: Hint::${k} → missing page nix-effects/diag-hints/${slug}.md"
        failed=1
      fi
      if ! grep -qxF '### ${k}' "${kleisliDocs}/nix-effects/diag/hints.md"; then
        echo "FAIL: Hint::${k} → missing in-page anchor '### ${k}' in nix-effects/diag/hints.md"
        failed=1
      fi
    ''
  ) keys;

  expectedCount = toString (builtins.length keys);
in
  pkgs.runCommand "diag-hints-anchors-schema" { } ''
    set -eu
    failed=0

    ${perKeyChecks}

    actualCount=$(find "${kleisliDocs}/nix-effects/diag-hints" -maxdepth 1 -type l -name '*.md' | wc -l)
    if [ "$actualCount" != "${expectedCount}" ]; then
      echo "FAIL: orphan check — found $actualCount files under nix-effects/diag-hints/, expected ${expectedCount}"
      failed=1
    fi

    if [ "$failed" = "1" ]; then
      echo ""
      echo "Schema-driven anchor check failed."
      echo "  Source of truth: src/diag/hints.nix"
      echo "  Renderer:        book/gen/kleisli-docs.nix"
      exit 1
    fi

    printf 'ok: %s Hint keys → %s pages + %s in-page anchors + no orphans\n' \
      "${expectedCount}" "${expectedCount}" "${expectedCount}" > $out
  ''
