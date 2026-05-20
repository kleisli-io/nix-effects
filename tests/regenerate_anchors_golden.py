#!/usr/bin/env python3
"""Regenerate the anchor-stability golden file for the nix-effects book.

Walks the given source directory for `*.md` files, extracts H2 and H3
headings, slugifies, and writes one `<rel>#<slug>` line per anchor to
the output file, sorted.

Slug rule (same one downstream HTML renderers use to emit heading IDs):
  1. trim leading/trailing space + tab from the heading text
  2. lowercase
  3. replace any character not in `[a-z0-9-]` with `-`
  4. collapse runs of `-` to a single `-`

Per-document disambiguation (mirrors `kleisli-content:unique-slugify`):
  Within a single `.md`, headings are walked in document order with a
  used-set; the first occurrence of a slug wins the bare form, the
  second gets `-2`, the third `-3`, … so headings whose text differs
  only in capitalisation each receive a distinct id. The runtime HTML
  renderer and the TOC walk both apply the same rule with a fresh
  per-document state; this script must stay in lock-step.

Usage:
  regenerate_anchors_golden <book-src-dir> <out-file>

The companion test (`tests/anchors-golden.nix`) re-implements the same
slug rule in Nix and asserts equality against this file. Updating
content requires re-running this script and committing the result.
"""

import re
import sys
from pathlib import Path

HEADING_RE = re.compile(r"^(##|###)\s+(.+?)\s*$")


def slugify(text: str) -> str:
    s = text.strip(" \t").lower()
    s = re.sub(r"[^a-z0-9-]", "-", s)
    s = re.sub(r"-+", "-", s)
    return s


def unique_slugify(text: str, used: set[str]) -> str:
    base = slugify(text)
    slug = base
    n = 1
    while slug in used:
        n += 1
        slug = f"{base}-{n}"
    used.add(slug)
    return slug


def extract_anchors(md_path: Path, src_dir: Path) -> list[str]:
    rel = md_path.relative_to(src_dir).as_posix()
    used: set[str] = set()
    out = []
    for line in md_path.read_text().splitlines():
        m = HEADING_RE.match(line)
        if m:
            slug = unique_slugify(m.group(2), used)
            out.append(f"{rel}#{slug}")
    return out


def main() -> int:
    if len(sys.argv) != 3:
        print(
            "usage: regenerate_anchors_golden <book-src-dir> <out-file>",
            file=sys.stderr,
        )
        return 2
    src_arg, out_arg = sys.argv[1], sys.argv[2]
    src_dir = Path(src_arg).resolve()
    out_path = Path(out_arg).resolve()

    if not src_dir.is_dir():
        print(f"error: {src_arg} is not a directory", file=sys.stderr)
        return 1

    anchors: list[str] = []
    for md in sorted(src_dir.rglob("*.md")):
        anchors.extend(extract_anchors(md, src_dir))
    anchors.sort()

    out_path.write_text("\n".join(anchors) + "\n")
    print(f"wrote {len(anchors)} anchors to {out_arg}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
