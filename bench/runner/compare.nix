# Bench comparison driver.
#
# Given two history JSON files (typically `baseline.json` and
# `current.json`), emits the gate classification markdown and exits
# non-zero on any hard fail. No git-trailer awareness — see gate.nix
# for the variant that pre-parses commit trailers.
{ lib, pkgs }:

let
  finalizer = ./finalize-gate.nix;

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-compare";
    runtimeInputs = [ pkgs.jq pkgs.coreutils pkgs.nix ];
    text = ''
      FINALIZER=${finalizer}

      bench_dir="$PWD/bench"
      baseline=""
      current=""
      budgets=""
      output=""

      usage() {
        cat >&2 <<'EOF'
      Usage: nix-effects-bench-compare --baseline <path> --current <path> [options]

      Options:
        --baseline <path>    Baseline history JSON (required).
        --current  <path>    Current history JSON (required).
        --budgets  <path>    budgets.toml (optional; without it, cpu gating is off).
        --output   <path>    Write markdown to file (default: stdout).
        --bench-dir <p>      Path to bench directory (default: $PWD/bench).

      Exit:
        0 — no hard fails (pass).
        1 — one or more hard fails.
        2 — usage error.
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --baseline)  baseline="$2"; shift 2 ;;
          --current)   current="$2";  shift 2 ;;
          --budgets)   budgets="$2";  shift 2 ;;
          --output)    output="$2";   shift 2 ;;
          --bench-dir) bench_dir="$2"; shift 2 ;;
          -h|--help)   usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -n "$baseline" && -f "$baseline" ]] || { echo "--baseline file required and must exist" >&2; exit 2; }
      [[ -n "$current"  && -f "$current"  ]] || { echo "--current file required and must exist" >&2; exit 2; }
      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      baseline="$(realpath "$baseline")"
      current="$(realpath "$current")"
      bench_dir="$(realpath "$bench_dir")"

      baseline_name=$(basename "$baseline" .json)
      current_name=$(basename "$current" .json)

      # Flake-pinned nixpkgs path; see run.nix for rationale.
      npkgs="${pkgs.path}"

      # Budgets path is inlined as either a Nix path literal or `null`.
      if [[ -n "$budgets" ]]; then
        [[ -f "$budgets" ]] || { echo "budgets file not found: $budgets" >&2; exit 2; }
        budgets="$(realpath "$budgets")"
        budgets_arg="$budgets"
      else
        budgets_arg="null"
      fi

      finalize_expr="(import $FINALIZER {
        benchPath = $bench_dir;
        baselinePath = $baseline;
        currentPath = $current;
        budgetsPath = $budgets_arg;
        trailersPath = null;
        baselineName = \"$baseline_name\";
        currentName = \"$current_name\";
      })"

      md=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.markdown" | jq -r .)

      pass=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.pass" | jq -r .)

      if [[ -n "$output" ]]; then
        printf '%s\n' "$md" > "$output"
        echo "bench-compare: wrote $output" >&2
      else
        printf '%s\n' "$md"
      fi

      if [[ "$pass" == "true" ]]; then exit 0; else exit 1; fi
    '';
  };
in script
