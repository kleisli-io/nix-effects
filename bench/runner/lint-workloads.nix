# Flag workloads in bench/workloads/**/*.nix whose body references
# `.allPass` but which are not in budgets.toml's `allocNoiseLimited`.
# `.allPass` definitionally folds over every test in a sub-tree, so
# alloc counts scale with unrelated test additions.
#
# Text-based: scans indent-2 bindings per file, reconstructs workload
# path from path (default.nix is its parent namespace), skips `let`
# blocks. Iteration-driven tree-forcers that don't use `.allPass`
# (e.g. a let-bound helper that folds over an `.tests` attrset) are
# out of scope for static detection and need manual registration in
# `allocNoiseLimited`.
{ pkgs }:

let
  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-lint-workloads";
    runtimeInputs = [ pkgs.jq pkgs.gawk pkgs.coreutils pkgs.findutils pkgs.gnugrep pkgs.gnused ];
    text = ''
      bench_dir="$PWD/bench"
      strict=0

      usage() {
        cat >&2 <<'EOF'
      Usage: nix-effects-bench-lint-workloads [options]

      Scan bench/workloads/**/*.nix for top-level workload bindings whose
      body references `.allPass`. Every such workload must appear in
      bench/budgets.toml's `allocNoiseLimited` array.

      Options:
        --strict          Exit 1 on any violation (default: report only).
        --bench-dir <p>   Bench directory (default: \$PWD/bench).
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --strict)    strict=1; shift ;;
          --bench-dir) bench_dir="$2"; shift 2 ;;
          -h|--help)   usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -d "$bench_dir" ]]           || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      [[ -d "$bench_dir/workloads" ]] || { echo "workloads dir not found: $bench_dir/workloads" >&2; exit 2; }
      [[ -f "$bench_dir/budgets.toml" ]] || { echo "budgets.toml not found: $bench_dir/budgets.toml" >&2; exit 2; }

      # Pull allocNoiseLimited quoted strings from budgets.toml.
      alloc_nl_file=$(mktemp)
      trap 'rm -f "$alloc_nl_file" "$report"' EXIT
      awk '
        /^allocNoiseLimited[[:space:]]*=[[:space:]]*\[/ { in_list=1; next }
        in_list && /^\]/ { in_list=0; next }
        in_list { print }
      ' "$bench_dir/budgets.toml" | grep -oE '"[^"]+"' | tr -d '"' > "$alloc_nl_file"

      report=$(mktemp)

      while IFS= read -r -d "" f; do
        rel="''${f#"$bench_dir"/workloads/}"
        # default.nix → parent namespace; foo.nix → foo namespace.
        prefix=$(printf '%s' "$rel" | sed -E 's|/default\.nix$||; s|\.nix$||; s|/|.|g')

        # Only scan bindings inside the returned attrset. `let` at col 0
        # opens an inactive block; `in {` or `in` at col 0 re-activates.
        # Files with no `let` are active from the start.
        gawk -v prefix="$prefix" -v file="$f" '
          function flush() {
            if (name != "") {
              if (body ~ /\.allPass/) {
                print prefix "." name "\t" file ":" startline
              }
              name = ""; body = ""; startline = 0
            }
          }
          BEGIN { name=""; body=""; startline=0; active=1 }
          /^let[[:space:]]*$/ || /^let[[:space:]]+/ { flush(); active=0; next }
          /^in[[:space:]]*\{/ || /^in[[:space:]]*$/ { active=1; next }
          !active { next }
          /^  [a-zA-Z_][a-zA-Z0-9_-]*[[:space:]]*=/ {
            flush()
            line = $0
            sub(/^  /, "", line)
            match(line, /^[a-zA-Z_][a-zA-Z0-9_-]*/)
            name = substr(line, RSTART, RLENGTH)
            body = $0
            startline = NR
            next
          }
          name != "" { body = body "\n" $0 }
          END { flush() }
        ' "$f" >> "$report"
      done < <(find "$bench_dir/workloads" -type f -name '*.nix' ! -name 'meta.nix' -print0 | sort -z)

      if [[ ! -s "$report" ]]; then
        echo "bench-lint-workloads: no workloads reference .allPass" >&2
        exit 0
      fi

      echo "bench-lint-workloads: workloads referencing .allPass" >&2
      echo "" >&2
      printf '%-50s  %s\n' "WORKLOAD" "ALLOCNOISELIMITED" >&2
      printf '%-50s  %s\n' "--------" "-----------------" >&2
      violations=0
      while IFS=$'\t' read -r wl_path loc; do
        if grep -qFx -- "$wl_path" "$alloc_nl_file"; then
          status="yes"
        else
          status="NO — add to bench/budgets.toml"
          violations=$((violations + 1))
        fi
        printf '%-50s  %s\n' "$wl_path" "$status" >&2
        printf '  at %s\n' "$loc" >&2
      done < "$report"

      echo "" >&2
      if [[ $violations -gt 0 ]]; then
        echo "bench-lint-workloads: $violations workload(s) not in allocNoiseLimited" >&2
        if [[ $strict -eq 1 ]]; then
          exit 1
        fi
        exit 0
      fi

      echo "bench-lint-workloads: all .allPass workloads are in allocNoiseLimited" >&2
    '';
  };
in script
