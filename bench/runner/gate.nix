# Bench gate: compare + commit-trailer override layer.
#
# Scans `git log <since>` for `Perf-regression:` trailers, validates
# them, and threads the validated list into the gate finalizer as
# override records. Every other mechanic is identical to compare.nix —
# this runner is the one CI calls.
#
# Trailer syntax:
#   Perf-regression: <workload>, <reason>
#
# A commit that knowingly introduces a regression on <workload> must
# carry this trailer to pass the gate. The gate demotes the matching
# workload's hard-fail to "overridden" and records the reason in the
# markdown. <reason> must be a human-readable justification (≥20 chars).
#
# Validation rules (rejecting the whole gate run on any failure):
#   - wildcards in <workload> → rejected.
#   - <workload> not in the current run's results → rejected.
#   - <reason> shorter than 20 characters → rejected.
#
# Recovery of acknowledged regressions is audited by the
# open-regressions runner, which cross-references `Perf-regression:`
# trailers against a current baseline's metrics. A regression is
# considered recovered when its workload passes the gate again.
#
# Gate modes:
#   default      — both alloc and cpu gating against --budgets.
#   --alloc-only — cpu budgets ignored; only alloc counts gate. Used in
#                  CI where the baseline's cpu percentiles were captured
#                  on different hardware than the PR runner's. Alloc
#                  counters are evaluator-deterministic (see
#                  finalize-gate.nix's Nix-version guard) and remain a
#                  valid universal gate.
{ lib, pkgs }:

let
  finalizer = ./finalize-gate.nix;

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-gate";
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
      alloc_only=0

      usage() {
        cat >&2 <<'EOF'
      Usage: nix-effects-bench-gate --baseline <path> --current <path> [options]

      Options:
        --baseline <path>    Baseline history JSON (required).
        --current  <path>    Current history JSON (required).
        --budgets  <path>    budgets.toml (optional; without it, cpu gating is off).
        --alloc-only         Ignore the [cpu] table of --budgets; gate on alloc
                             counts only. Use when cpu timings in the baseline are
                             not comparable with the current run's environment
                             (e.g. CI on shared runners vs. a baseline captured on
                             a developer workstation). Alloc counters are
                             evaluator-deterministic and remain gated.
        --output   <path>    Write markdown to file (default: stdout).
        --since    <range>   git-log revision range (default: origin/main..HEAD).
        --bench-dir <p>      Path to bench directory (default: $PWD/bench).
        --repo-root <p>      Repo root for git log (default: $PWD).

      Exit:
        0 — pass.
        1 — hard fails.
        2 — usage error.
        3 — trailer validation error.
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --baseline)   baseline="$2";  shift 2 ;;
          --current)    current="$2";   shift 2 ;;
          --budgets)    budgets="$2";   shift 2 ;;
          --alloc-only) alloc_only=1;   shift ;;
          --output)     output="$2";    shift 2 ;;
          --since)      since="$2";     shift 2 ;;
          --bench-dir)  bench_dir="$2"; shift 2 ;;
          --repo-root)  repo_root="$2"; shift 2 ;;
          -h|--help)    usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -n "$baseline" && -f "$baseline" ]] || { echo "--baseline file required and must exist" >&2; exit 2; }
      [[ -n "$current"  && -f "$current"  ]] || { echo "--current file required and must exist" >&2; exit 2; }
      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      [[ -d "$repo_root" ]] || { echo "repo root not found: $repo_root" >&2; exit 2; }

      baseline_name=$(basename "$baseline" .json)
      current_name=$(basename "$current" .json)

      # Fast-fail Nix-version mismatch with a clean message. The same
      # invariant is re-asserted in finalize-gate.nix for any non-CLI
      # caller; this check exists purely so the CLI user doesn't see a
      # Nix eval stack trace wrapping the actual error.
      baseline_nix=$(jq -r '.nix // "unknown"' "$baseline")
      current_nix=$(jq -r '.nix // "unknown"' "$current")
      if [[ "$baseline_nix" != "$current_nix" ]]; then
        cat >&2 <<EOF
      bench-gate: Nix version mismatch between baseline and current run.
        baseline ($baseline_name): $baseline_nix
        current  ($current_name):  $current_nix

      Allocation counters are evaluator-version-specific; comparing across
      versions produces false regressions. Either re-capture the baseline
      with Nix $current_nix, or pin the gate invocation's Nix to
      $baseline_nix.
      EOF
        exit 2
      fi

      # Flake-pinned nixpkgs path; see run.nix for rationale.
      npkgs="${pkgs.path}"

      # ---- Trailer extraction + validation ----
      #
      # Valid workload list: attrNames of current.results.
      known_workloads=$(jq -r '.results | keys[]' "$current")

      tmpdir=$(mktemp -d)
      trap 'rm -rf "$tmpdir"' EXIT

      trailers_json="$tmpdir/trailers.json"
      printf '[]' > "$trailers_json"

      commit_bodies=$(cd "$repo_root" && git log --format='%B%x1e' "$since" 2>/dev/null || true)

      fail_trailer() {
        echo "bench-gate: trailer validation: $*" >&2
        exit 3
      }

      if [[ -n "$commit_bodies" ]]; then
        while IFS= read -r -d $'\x1e' body; do
          while IFS= read -r line; do
            case "$line" in
              Perf-regression:*)
                payload="''${line#Perf-regression:}"
                payload="''${payload# }"
                if [[ "$payload" != *,* ]]; then
                  fail_trailer "Perf-regression without comma: '$line'"
                fi
                workload="''${payload%%,*}"
                reason="''${payload#*,}"
                workload="''${workload# }"; workload="''${workload% }"
                reason="''${reason# }"; reason="''${reason% }"
                case "$workload" in
                  *\**|*\?*|*\[*) fail_trailer "wildcard in workload: '$workload'" ;;
                esac
                if ! grep -Fxq "$workload" <<< "$known_workloads"; then
                  fail_trailer "unknown workload: '$workload'"
                fi
                if [[ "''${#reason}" -lt 20 ]]; then
                  fail_trailer "reason <20 chars for '$workload': '$reason'"
                fi
                jq --arg w "$workload" --arg r "$reason" \
                  '. + [{ workload: $w, reason: $r }]' \
                  "$trailers_json" > "$trailers_json.tmp"
                mv "$trailers_json.tmp" "$trailers_json"
                ;;
            esac
          done <<< "$body"
        done <<< "$commit_bodies"
      fi

      n_trailers=$(jq 'length' "$trailers_json")
      echo "bench-gate: $n_trailers validated trailer override(s)" >&2

      if [[ -n "$budgets" ]]; then
        [[ -f "$budgets" ]] || { echo "budgets file not found: $budgets" >&2; exit 2; }
        budgets_arg="$budgets"
      else
        budgets_arg="null"
      fi

      if [[ "$alloc_only" -eq 1 ]]; then
        cpu_gating_arg="false"
      else
        cpu_gating_arg="true"
      fi

      finalize_expr="(import $FINALIZER {
        benchPath = $bench_dir;
        baselinePath = $baseline;
        currentPath = $current;
        budgetsPath = $budgets_arg;
        trailersPath = $trailers_json;
        cpuGating = $cpu_gating_arg;
        baselineName = \"$baseline_name\";
        currentName = \"$current_name\";
      })"

      md=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.markdown" | jq -r .)

      pass=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "$finalize_expr.pass" | jq -r .)

      if [[ -n "$output" ]]; then
        printf '%s\n' "$md" > "$output"
        echo "bench-gate: wrote $output" >&2
      else
        printf '%s\n' "$md"
      fi

      if [[ "$pass" == "true" ]]; then exit 0; else exit 1; fi
    '';
  };
in script
