# Un-recovered perf-regression audit.
#
# Walks `git log <since>` for `Perf-regression: <workload>, <reason>`
# trailers and classifies each against a supplied baseline / current
# pair + budgets.toml. A regression is "recovered" when the workload's
# current metrics are within budget relative to the baseline; "open"
# otherwise. The recovery check uses the same gate logic applied on
# every PR, so an acknowledged regression clears the audit the moment
# its workload passes the gate again.
#
# Typical usage:
#
#   # After a phase lands, capture a fresh baseline.
#   nix-effects-bench-run --name "baseline-$(git rev-parse --short HEAD)" ...
#
#   # Audit all acknowledged regressions since the last release tag.
#   nix-effects-bench-open-regressions \
#     --baseline bench/history/baseline-<prev>.json \
#     --current  bench/history/baseline-<head>.json \
#     --budgets  bench/budgets.toml \
#     --since    "v0.7.0..HEAD"
#
# Exit: 0 if every acknowledged regression in range is recovered or
# structurally gone; 1 if any remain open; 2 usage error.
{ lib, pkgs }:

let
  finalizer = ./finalize-open-regressions.nix;

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-open-regressions";
    runtimeInputs = [ pkgs.jq pkgs.coreutils pkgs.nix pkgs.git pkgs.gnugrep pkgs.gnused ];
    text = ''
      FINALIZER=${finalizer}

      bench_dir="$PWD/bench"
      repo_root="$PWD"
      baseline=""
      current=""
      budgets=""
      output=""
      since="origin/main..HEAD"

      usage() {
        cat >&2 <<'EOF'
      Usage: nix-effects-bench-open-regressions --baseline <path> --current <path> [options]

      Options:
        --baseline <path>    Reference baseline history JSON (required).
        --current  <path>    Current history JSON to audit (required).
        --budgets  <path>    budgets.toml (optional; without it, cpu gating is off).
        --output   <path>    Write markdown to file (default: stdout).
        --since    <range>   git-log revision range (default: origin/main..HEAD).
        --bench-dir <p>      Path to bench directory (default: $PWD/bench).
        --repo-root <p>      Repo root for git log (default: $PWD).

      Exit:
        0 — no open regressions (all recovered / unmeasured).
        1 — one or more open regressions remain.
        2 — usage error.
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --baseline)  baseline="$2";  shift 2 ;;
          --current)   current="$2";   shift 2 ;;
          --budgets)   budgets="$2";   shift 2 ;;
          --output)    output="$2";    shift 2 ;;
          --since)     since="$2";     shift 2 ;;
          --bench-dir) bench_dir="$2"; shift 2 ;;
          --repo-root) repo_root="$2"; shift 2 ;;
          -h|--help)   usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -n "$baseline" && -f "$baseline" ]] || { echo "--baseline file required and must exist" >&2; exit 2; }
      [[ -n "$current"  && -f "$current"  ]] || { echo "--current file required and must exist" >&2; exit 2; }
      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      [[ -d "$repo_root" ]] || { echo "repo root not found: $repo_root" >&2; exit 2; }
      baseline="$(realpath "$baseline")"
      current="$(realpath "$current")"
      bench_dir="$(realpath "$bench_dir")"
      repo_root="$(realpath "$repo_root")"

      tmpdir=$(mktemp -d)
      trap 'rm -rf "$tmpdir"' EXIT

      trailers_json="$tmpdir/trailers.json"
      printf '[]' > "$trailers_json"

      log=$(git -C "$repo_root" log --format='%H%x1f%B%x1e' "$since" 2>/dev/null || true)

      if [[ -n "$log" ]]; then
        while IFS= read -r -d $'\x1e' entry; do
          sha="''${entry%%$'\x1f'*}"
          body="''${entry#*$'\x1f'}"
          while IFS= read -r line; do
            case "$line" in
              Perf-regression:*)
                payload="''${line#Perf-regression:}"
                payload="''${payload# }"
                if [[ "$payload" != *,* ]]; then
                  continue
                fi
                workload="''${payload%%,*}"
                reason="''${payload#*,}"
                workload="''${workload# }"; workload="''${workload% }"
                reason="''${reason# }"; reason="''${reason% }"
                jq --arg s "$sha" --arg w "$workload" --arg r "$reason" \
                  '. + [{ sha: $s, workload: $w, reason: $r }]' \
                  "$trailers_json" > "$trailers_json.tmp"
                mv "$trailers_json.tmp" "$trailers_json"
                ;;
            esac
          done <<< "$body"
        done <<< "$log"
      fi

      n_trailers=$(jq 'length' "$trailers_json")
      echo "bench-open-regressions: $n_trailers Perf-regression trailer(s) in range" >&2

      if [[ -n "$budgets" ]]; then
        [[ -f "$budgets" ]] || { echo "budgets file not found: $budgets" >&2; exit 2; }
        budgets_arg="$budgets"
      else
        budgets_arg="null"
      fi

      # Flake-pinned nixpkgs path; see run.nix for rationale.
      npkgs="${pkgs.path}"

      finalize_expr="(import $FINALIZER {
        benchPath = $bench_dir;
        baselinePath = $baseline;
        currentPath = $current;
        budgetsPath = $budgets_arg;
        trailersPath = $trailers_json;
        since = \"$since\";
      })"

      md=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.markdown" | jq -r .)

      pass=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.pass" | jq -r .)

      if [[ -n "$output" ]]; then
        printf '%s\n' "$md" > "$output"
        echo "bench-open-regressions: wrote $output" >&2
      else
        printf '%s\n' "$md"
      fi

      if [[ "$pass" == "true" ]]; then exit 0; else exit 1; fi
    '';
  };
in script
