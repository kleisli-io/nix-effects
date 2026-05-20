# Schema-driven anchor-stability check for diag Hints.
#
# Asserts a three-axis invariant against the produced docs corpus, using
# the Hint registry (`src.diag.hints.hints`) as the single source of
# truth:
#
#   1. Path axis: every Hint key K has a `nix-effects/diag-hints/<slug>.md`
#      file in the corpus, where `slug = lastPath hint.docLink` — the same
#      rule `book/gen/docs-content.nix` uses to emit pages. The rule lives
#      once in the renderer; the test reuses `hint.docLink` directly, so no
#      slugify logic is duplicated here.
#   2. In-page anchor axis: every Hint key K has a `### K` heading in
#      `nix-effects/diag/hints.md` (the in-page registry overview).
#   3. No-orphans axis: the number of files under `nix-effects/diag-hints/`
#      excluding `index.md` equals `length (attrNames hints)` — catches a page
#      lingering after its key is dropped from the registry.
#
# Build:
#   nix-build -A tests.anchors-schema
#
# Failure semantics: any failed axis exits before `$out` is written, so the
# Nix build itself fails with the diagnostic in stderr.
{ pkgs, lib, src, corpus }:

let
  hints = src.diag.hints.hints;
  keys = builtins.attrNames hints;
  slugOf = k: lib.last (lib.splitString "/" hints.${k}.docLink);
  hintToken = k:
    if lib.strings.hasPrefix "::" k
    then "Hint::${lib.strings.removePrefix "::" k}"
    else "Hint::${k}";

  perKeyChecks = lib.concatMapStringsSep "\n"
    (k:
      let
        slug = slugOf k;
        token = hintToken k;
      in
      ''
        if [ ! -f "${corpus}/nix-effects/diag-hints/${slug}.md" ]; then
          echo "FAIL: Hint::${k} → missing page nix-effects/diag-hints/${slug}.md"
          failed=1
        fi
        if ! grep -qxF '### ${k}' "${corpus}/nix-effects/diag/hints.md"; then
          echo "FAIL: Hint::${k} → missing in-page anchor '### ${k}' in nix-effects/diag/hints.md"
          failed=1
        fi
        if ! grep -qxF '## Example' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → missing example section in nix-effects/diag-hints/${slug}.md"
          failed=1
        fi
        if ! grep -qF '${token}' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page does not mention ${token}"
          failed=1
        fi
        if grep -qF 'Hint::::' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page renders wildcard hint token with four colons"
          failed=1
        fi
        if grep -qF 'diagnostic shape' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page leaks internal classifier wording"
          failed=1
        fi
        if grep -qF 'executable fixture' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page leaks executable fixture wording"
          failed=1
        fi
        if grep -qF 'minimal diagnostic error shape' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page leaks diagnostic harness wording"
          failed=1
        fi
        if grep -qF 'fx.diag.hints.resolve' "${corpus}/nix-effects/diag-hints/${slug}.md"; then
          echo "FAIL: Hint::${k} → example page renders the hidden resolver harness"
          failed=1
        fi
      ''
    )
    keys;

  expectedCount = toString (builtins.length keys);
in
pkgs.runCommand "diag-hints-anchors-schema" { } ''
  set -eu
  failed=0

  ${perKeyChecks}

  actualCount=$(find "${corpus}/nix-effects/diag-hints" -maxdepth 1 -type l -name '*.md' ! -name 'index.md' | wc -l)
  if [ "$actualCount" != "${expectedCount}" ]; then
    echo "FAIL: orphan check — found $actualCount files under nix-effects/diag-hints/, expected ${expectedCount}"
    failed=1
  fi

  if [ "$failed" = "1" ]; then
    echo ""
    echo "Schema-driven anchor check failed."
    echo "  Source of truth: src/diag/hints.nix"
    echo "  Renderer:        book/gen/docs-content.nix"
    exit 1
  fi

  printf 'ok: %s Hint keys → %s pages + %s in-page anchors + no orphans\n' \
    "${expectedCount}" "${expectedCount}" "${expectedCount}" > $out
''
