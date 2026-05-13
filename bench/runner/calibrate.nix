# Calibration driver.
#
# Drives the run harness with a large `--runs` count (default 20) on the
# selected tier, then post-processes the emitted history JSON into a
# proposed `budgets.toml`. Emits both the proposal and a
# human-readable per-workload summary of p50 / p95 / budget.
#
# The calibration history file lives at
# `<history-dir>/calibrate-<timestamp>.json` by default so repeated calls
# don't collide.
#
# If the canonical `<bench-dir>/budgets.toml` exists, it is consulted for
# its `noiseLimited` array — those workloads are excluded from the
# emitted `[cpu]` section and the array round-trips verbatim into the
# proposal so the declaration survives re-calibration. Override or
# disable via `--existing-budgets <path>` (pass an empty string to
# opt out).
{ lib, pkgs }:

let
  finalizer = ./finalize-calibrate.nix;
  runner = import ./run.nix { inherit lib pkgs; };

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-calibrate";
    runtimeInputs = [ pkgs.jq pkgs.coreutils pkgs.nix ];
    text = ''
      FINALIZER=${finalizer}
      RUNNER=${runner}/bin/nix-effects-bench-run

      bench_dir="$PWD/bench"
      history_dir=""
      runs=20
      warmup=1
      tier="quick,standard"
      filter=""
      output=""
      min_budget=3
      existing_budgets="__auto__"

      usage() {
        cat >&2 <<'EOF'
      Usage: nix-effects-bench-calibrate [options]

      Options:
        --runs <n>        Measurement runs per workload (default 20).
        --warmup <n>      Warmup samples (default 1).
        --tier <list>     Comma-separated tiers or 'all' (default quick,standard).
        --filter <regex>  Regex on workload path.
        --bench-dir <p>   Bench directory (default: $PWD/bench).
        --history-dir <p> Where to write the calibration history JSON
                          (default: <bench-dir>/history).
        --output <p>      Write proposed TOML to this path (default: stdout).
        --min-budget <n>  Minimum cpu budget percent (default 3).
        --existing-budgets <p>
                          Canonical budgets.toml whose noiseLimited array
                          should be preserved into the proposal. Defaults to
                          <bench-dir>/budgets.toml if present. Pass an empty
                          string to disable and emit cpu budgets for every
                          workload.
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --runs)             runs="$2"; shift 2 ;;
          --warmup)           warmup="$2"; shift 2 ;;
          --tier)             tier="$2"; shift 2 ;;
          --filter)           filter="$2"; shift 2 ;;
          --bench-dir)        bench_dir="$2"; shift 2 ;;
          --history-dir)      history_dir="$2"; shift 2 ;;
          --output)           output="$2"; shift 2 ;;
          --min-budget)       min_budget="$2"; shift 2 ;;
          --existing-budgets) existing_budgets="$2"; shift 2 ;;
          -h|--help)          usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      bench_dir="$(realpath "$bench_dir")"
      [[ -n "$history_dir" ]] || history_dir="$bench_dir/history"
      history_dir="$(realpath -m "$history_dir")"
      mkdir -p "$history_dir"

      # Resolve existing-budgets: explicit value wins; sentinel means
      # auto-default to <bench-dir>/budgets.toml iff the file exists.
      if [[ "$existing_budgets" == "__auto__" ]]; then
        if [[ -f "$bench_dir/budgets.toml" ]]; then
          existing_budgets="$bench_dir/budgets.toml"
        else
          existing_budgets=""
        fi
      fi
      if [[ -n "$existing_budgets" && ! -f "$existing_budgets" ]]; then
        echo "bench-calibrate: --existing-budgets file not found: $existing_budgets" >&2
        exit 2
      fi
      if [[ -n "$existing_budgets" ]]; then
        existing_budgets="$(realpath "$existing_budgets")"
        existing_budgets_arg="$existing_budgets"
        echo "bench-calibrate: preserving noiseLimited from $existing_budgets" >&2
      else
        existing_budgets_arg="null"
      fi

      ts=$(date -u +%Y%m%d-%H%M%S)
      name="calibrate-$ts"
      run_json="$history_dir/$name.json"

      echo "bench-calibrate: driving $RUNNER with --runs $runs --tier $tier" >&2
      "$RUNNER" \
        --name "$name" \
        --runs "$runs" \
        --warmup "$warmup" \
        --tier "$tier" \
        --filter "$filter" \
        --bench-dir "$bench_dir" \
        --history-dir "$history_dir"

      [[ -f "$run_json" ]] || { echo "bench-calibrate: run did not produce $run_json" >&2; exit 1; }

      # Flake-pinned nixpkgs path; see run.nix for rationale.
      npkgs="${pkgs.path}"

      toml=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "(import $FINALIZER {
          runPath = $run_json;
          benchPath = $bench_dir;
          existingBudgetsPath = $existing_budgets_arg;
          minBudget = $min_budget;
        }).toml" | jq -r .)

      summary=$(NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "(import $FINALIZER {
          runPath = $run_json;
          benchPath = $bench_dir;
          existingBudgetsPath = $existing_budgets_arg;
          minBudget = $min_budget;
        }).summary" | jq -r .)

      echo "bench-calibrate: per-workload summary" >&2
      printf '%s\n' "$summary" >&2

      if [[ -n "$output" ]]; then
        printf '%s' "$toml" > "$output"
        echo "bench-calibrate: wrote $output" >&2
      else
        printf '%s' "$toml"
      fi
    '';
  };
in script
