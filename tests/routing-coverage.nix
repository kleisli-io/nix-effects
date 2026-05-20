# Asserts every `.md` in the produced docs corpus has a path shape an
# external consumer's route table can serve under the layout contract.
# Catches builder drift before it ships.
#
# Route shape required:
#
#   /:project                  — project landing  (1 segment)
#   /:project/:section         — section landing  (2 segments)
#   /:project/:section/*page   — page splat       (3+ segments)
#
# Relpath = path under the linkFarm root with `.md` stripped. The only
# routing invariant is `slashes >= 1` — every page must be project-prefixed
# so a route table can dispatch it. The page splat is depth-agnostic, so
# there is no maximum bound to enforce here. A *styling* bound (the
# consumer's nested-link CSS rule inventory) lives in the consumer depot
# and is gated there, separately, so this file remains a pure routing
# concern.
{ pkgs, lib, corpus }:

pkgs.runCommand "nix-effects-routing-coverage" { } ''
  set -eu
  failed=0
  total=0

  while read -r f; do
    total=$((total + 1))
    rel="''${f#${corpus}/}"
    slashes=$(printf '%s' "$rel" | tr -cd '/' | wc -c)
    if [ "$slashes" -lt 1 ]; then
      echo "FAIL: $rel — root-level .md (no project prefix)."
      failed=1
    fi
    if [ "$rel" != "nix-effects/internals/kernel-spec.md" ]; then
      if grep -qF '§' "$f"; then
        echo "FAIL: $rel — paragraph glyph outside the formal kernel spec."
        failed=1
      fi
      if grep -qF 'kernel-spec.md' "$f"; then
        echo "FAIL: $rel — internal kernel-spec filename leaked into rendered docs."
        failed=1
      fi
    fi
    if grep -qE '^\*\*Source:\*\* `|^- `src/' "$f"; then
      echo "FAIL: $rel — source references must be GitHub links."
      failed=1
    fi
  done < <(find "${corpus}" -type l -name '*.md')

  if [ "$failed" = "1" ]; then
    echo ""
    echo "Routing contract violated: every .md must be project-prefixed."
    exit 1
  fi

  printf 'ok: %s .md files routable under /:project, /:project/:section, /:project/:section/*page\n' \
    "$total" > $out
''
