# Maintenance tool: regenerate `tests/anchors-golden.txt` from the live
# heading set in `book/src/**/*.md`.
#
# Build:
#   nix-build -A regenerateAnchorsGolden
#
# Run from the nix-effects repo root (so the default relative paths
# resolve); override either argument for non-standard layouts:
#   ./result/bin/regenerate-anchors-golden
#   ./result/bin/regenerate-anchors-golden <book-src-dir> <out-file>
{ pkgs }:

pkgs.writeShellApplication {
  name = "regenerate-anchors-golden";
  runtimeInputs = [ pkgs.python3 ];
  text = ''
    src_dir="''${1:-book/src}"
    out_file="''${2:-tests/anchors-golden.txt}"
    exec python3 ${./regenerate_anchors_golden.py} "$src_dir" "$out_file"
  '';
}
