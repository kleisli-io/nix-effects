# Anchor-stability gate for hand-written book chapters.
#
# Walks `bookSrc` recursively, extracts H2 and H3 headings, slugifies them
# using a pure-Nix port of the kleisli-content heading-id rule, and asserts
# the sorted `<rel>#<slug>` list equals `goldenFile`.
#
# The companion regenerator (`tests/regenerate_anchors_golden.py`) writes
# the same data from a Python re-implementation of the same slug rule;
# this test failing means either the book source headings drifted or the
# two implementations diverged. The regenerator is the maintenance path:
#
#   nix-build -A regenerateAnchorsGolden
#   ./result/bin/regenerate-anchors-golden
#
# Build:
#   nix-build -A tests.anchors-golden
{ pkgs, lib, bookSrc, goldenFile }:

let
  # Pure-Nix slugify, byte-for-byte equivalent to the Python regenerator's
  # rule (which itself mirrors the runtime HTML renderer): trim leading
  # and trailing space/tab, lowercase, replace `[^a-z0-9-]` with `-`,
  # collapse runs of `-` to one.
  slugify = text:
    let
      m = builtins.match "[\t ]*(.*[^\t ])[\t ]*" text;
      trimmed = if m == null then "" else builtins.head m;
      lowered = lib.toLower trimmed;
      chars = lib.stringToCharacters lowered;
      sanitized = lib.concatStrings (map (c:
        if (c >= "a" && c <= "z") || (c >= "0" && c <= "9") || c == "-"
        then c else "-"
      ) chars);
      collapse = s:
        let s' = builtins.replaceStrings [ "--" ] [ "-" ] s;
        in if s' == s then s else collapse s';
    in collapse sanitized;

  # Recursively collect every `.md` file under `dir` with its relative
  # path from the root.
  walkMd = dir:
    let
      entries = builtins.readDir dir;
      mdHere = lib.filter
        (n: entries.${n} == "regular" && lib.hasSuffix ".md" n)
        (builtins.attrNames entries);
      subdirsHere = lib.filter
        (n: entries.${n} == "directory")
        (builtins.attrNames entries);
      here = map (n: { rel = n; path = dir + "/${n}"; }) mdHere;
      nested = lib.concatMap
        (sub: map (e: { rel = "${sub}/${e.rel}"; path = e.path; })
                  (walkMd (dir + "/${sub}")))
        subdirsHere;
    in here ++ nested;

  # H2/H3-only: any other heading level is ignored. Matches the runtime
  # HTML renderer, which only emits `id=` attributes on `<h2>` / `<h3>`.
  fileAnchors = { rel, path }:
    let
      lines = lib.splitString "\n" (builtins.readFile path);
      anchorOf = line:
        let m = builtins.match "(#+)[ \t]+(.*[^ \t])[ \t]*" line;
        in if m == null then null
           else let
             markerLen = lib.stringLength (builtins.head m);
             text = builtins.elemAt m 1;
           in if markerLen == 2 || markerLen == 3
              then "${rel}#${slugify text}"
              else null;
    in lib.filter (a: a != null) (map anchorOf lines);

  allAnchors = lib.concatMap fileAnchors (walkMd bookSrc);
  expected = (lib.concatStringsSep "\n" (lib.sort (a: b: a < b) allAnchors))
             + "\n";
in
  pkgs.runCommand "book-anchors-golden" {
    inherit expected;
    golden = goldenFile;
    passAsFile = [ "expected" ];
  } ''
    set -eu
    if diff -u "$golden" "$expectedPath" > diff.out 2>&1; then
      lines=$(wc -l < "$expectedPath")
      printf 'ok: %s anchors match golden\n' "$lines" > $out
      exit 0
    fi
    echo "FAIL: anchor-stability golden drift detected."
    echo ""
    echo "Diff (- golden, + live extraction):"
    cat diff.out
    echo ""
    echo "To regenerate:"
    echo "  nix-build -A regenerateAnchorsGolden"
    echo "  ./result/bin/regenerate-anchors-golden"
    exit 1
  ''
