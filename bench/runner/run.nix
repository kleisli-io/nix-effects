# Dual-metric bench runner.
#
# Collects `NIX_SHOW_STATS`-derived allocation counts and cpuTime across
# N samples per workload, aggregates via `bench.measure.summarize`, and
# emits `history/<name>.{json,md}` via `bench.format.emit*`.
#
# Hermeticity: each workload invocation runs with
# `NIX_PATH=nixpkgs=$NPKGS` where `$NPKGS` is pinned once up-front from
# the ambient channel. `bench/default.nix` takes `lib ? (import <nixpkgs>
# {}).lib`, so stripping NIX_PATH entirely breaks the default; passing a
# single resolved channel root keeps the workload call hermetic while
# letting `lib` resolve.
#
# Workload enumeration walks `bench.workloads` down to non-attrset leaves;
# the resulting dotted path is the key used in `bench.meta.tiers` and in
# per-workload filtering/budgets. Tier default is `standard` per meta.nix.
#
# Per-run measurement:
#   - wall-clock: `date +%s%N` bracketing the nix-instantiate call. Integer
#     milliseconds. Startup-dominated on <50ms workloads; report only.
#   - stats: `NIX_SHOW_STATS_PATH=<file>` writes the evaluator's JSON
#     summary to a per-sample file; the runner reads it as a raw
#     attrset and feeds it to `measure.pickAllocs`/`pickCpu`/`pickGc`
#     via the finalize-run helper.
#
# On any sample failing (nix-instantiate non-zero exit or missing stats),
# the runner aborts with the workload + sample index: no partial history.
{ lib, pkgs }:

let
  finalizer = ./finalize-run.nix;

  # Shell-embedded Nix enumerator: prints a JSON array of `{ path, tier }`
  # records. Sourced from `bench.meta.tiers` — the authoritative workload
  # registry — so enumeration never forces workload values. A tree-walk
  # over `bench.workloads` would force each leaf during `builtins.isAttrs`
  # and can exceed the evaluator's call-depth on long chains
  # (e.g. `effects.interp.ack33`).
  enumerateExpr = ''
    benchPath:
    let
      bench = import benchPath { };
      paths = builtins.attrNames bench.meta.tiers;
    in map (p: { path = p; tier = bench.meta.lookup p; }) paths
  '';

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-run";
    runtimeInputs = [ pkgs.jq pkgs.coreutils pkgs.nix ];
    text = ''
      # shellcheck disable=SC2016
      ENUM_EXPR=${lib.escapeShellArg enumerateExpr}
      FINALIZER=${finalizer}

      bench_dir="$PWD/bench"
      history_dir=""
      name=""
      runs=5
      warmup=1
      tier="quick"
      filter=""

      usage() {
        cat >&2 <<EOF
      Usage: nix-effects-bench-run --name <label> [options]

      Options:
        --name <s>        Label for history files (required).
        --runs <n>        Measured samples per workload (default 5).
        --warmup <n>      Warmup samples discarded per workload (default 1).
        --tier <list>     Comma-separated tiers: quick,standard,heavy, or 'all'
                          (default: quick,standard).
        --filter <regex>  Additional regex on workload dotted path.
        --bench-dir <p>   Path to bench directory (default: \$PWD/bench).
        --history-dir <p> Output directory (default: <bench-dir>/history).
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --name)        name="$2"; shift 2 ;;
          --runs)        runs="$2"; shift 2 ;;
          --warmup)      warmup="$2"; shift 2 ;;
          --tier)        tier="$2"; shift 2 ;;
          --filter)      filter="$2"; shift 2 ;;
          --bench-dir)   bench_dir="$2"; shift 2 ;;
          --history-dir) history_dir="$2"; shift 2 ;;
          -h|--help)     usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -n "$name" ]] || { echo "--name is required" >&2; exit 2; }
      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      bench_dir="$(realpath "$bench_dir")"
      [[ -n "$history_dir" ]] || history_dir="$bench_dir/history"
      history_dir="$(realpath -m "$history_dir")"
      mkdir -p "$history_dir"

      # Pin nixpkgs to the flake-locked store path baked in at build
      # time. Using the host's `<nixpkgs>` would make workload evaluation
      # depend on the ambient channel (different `lib` → different alloc
      # counts on different machines), silently invalidating the
      # alloc-determinism invariant that the gate relies on.
      npkgs="${pkgs.path}"

      echo "bench-run: name=$name runs=$runs warmup=$warmup tier=$tier filter='$filter'" >&2
      echo "bench-run: bench_dir=$bench_dir history_dir=$history_dir" >&2
      echo "bench-run: nixpkgs=$npkgs" >&2

      # Enumerate workloads. Bench path is inlined as a literal path in the
      # expression — `--argstr` is not applied in `--eval` mode.
      workloads_json="$(
        NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
          --expr "(let f = $ENUM_EXPR; in f $bench_dir)"
      )"

      # Filter by tier and regex.
      if [[ "$tier" == "all" ]]; then
        tier_pattern=""
      else
        tier_pattern="^($(echo "$tier" | tr ',' '|'))$"
      fi

      selected="$(echo "$workloads_json" | jq -r \
        --arg tp "$tier_pattern" \
        --arg fl "$filter" \
        'map(select(
          (($tp == "") or (.tier | test($tp))) and
          (($fl == "") or (.path | test($fl)))
        )) | sort_by(.path) | .[] | .path')"

      n_selected="$(echo "$selected" | grep -c . || true)"
      if [[ "$n_selected" -eq 0 ]]; then
        echo "bench-run: no workloads matched tier=$tier filter='$filter'" >&2
        exit 2
      fi
      echo "bench-run: $n_selected workload(s) selected" >&2

      # Collect samples into a JSON object keyed by workload path.
      samples_dir="$(mktemp -d)"
      trap 'rm -rf "$samples_dir"' EXIT

      workloads_obj="$samples_dir/workloads.json"
      printf '{}' > "$workloads_obj"

      measure_one() {
        local path="$1" idx="$2"
        local stats_file="$samples_dir/$path.$idx.stats.json"
        local expr="(import \"$bench_dir\" { }).workloads.$path"
        local t0_ns t1_ns wall_ms
        t0_ns=$(date +%s%N)
        NIX_PATH="nixpkgs=$npkgs" NIX_SHOW_STATS=1 NIX_SHOW_STATS_PATH="$stats_file" \
          nix-instantiate --eval --strict --json --expr "$expr" >/dev/null 2>/dev/null
        t1_ns=$(date +%s%N)
        wall_ms=$(( (t1_ns - t0_ns) / 1000000 ))
        [[ -s "$stats_file" ]] || {
          echo "bench-run: FAIL $path sample $idx produced no stats file" >&2
          return 1
        }
        echo "$wall_ms:$stats_file"
      }

      i=0
      for path in $selected; do
        i=$((i + 1))
        echo "[$i/$n_selected] $path" >&2

        # Warmup samples — ignored.
        for ((w=0; w<warmup; w++)); do
          measure_one "$path" "w$w" >/dev/null
        done

        # Measured samples.
        samples_arr="$samples_dir/$path.samples.json"
        printf '[]' > "$samples_arr"
        for ((r=0; r<runs; r++)); do
          line="$(measure_one "$path" "$r")"
          wall_ms="''${line%%:*}"
          stats_file="''${line#*:}"
          jq --argjson wall "$wall_ms" --slurpfile stats "$stats_file" \
            '. + [{ wallMs: $wall, stats: $stats[0] }]' \
            "$samples_arr" > "$samples_arr.tmp"
          mv "$samples_arr.tmp" "$samples_arr"
        done

        jq --arg k "$path" --slurpfile s "$samples_arr" \
          '. + { ($k): $s[0] }' "$workloads_obj" > "$workloads_obj.tmp"
        mv "$workloads_obj.tmp" "$workloads_obj"
      done

      # Assemble the run envelope consumed by finalize-run.nix.
      run_envelope="$samples_dir/run.json"
      nix_version="$(nix --version | awk '{print $NF}')"
      system="$(nix eval --raw --impure --expr 'builtins.currentSystem')"
      timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

      jq -n \
        --arg name "$name" \
        --arg ts "$timestamp" \
        --arg nx "$nix_version" \
        --arg sys "$system" \
        --argjson rpw "$runs" \
        --slurpfile ws "$workloads_obj" \
        '{ name: $name, timestamp: $ts, nix: $nx, system: $sys,
           runsPerWorkload: $rpw, workloads: $ws[0] }' \
        > "$run_envelope"

      # Finalize: summarize + render via the pure Nix helper. `--eval --json`
      # returns a JSON-quoted string for each attribute; `jq -r .` strips the
      # quoting + unescapes to land the real file bytes.
      json_file="$history_dir/$name.json"
      md_file="$history_dir/$name.md"

      NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "(import $FINALIZER { benchPath = $bench_dir; samplesPath = $run_envelope; }).json" \
        | jq -r . > "$json_file"

      NIX_PATH="nixpkgs=$npkgs" nix-instantiate --eval --strict --json \
        --expr "(import $FINALIZER { benchPath = $bench_dir; samplesPath = $run_envelope; }).markdown" \
        | jq -r . > "$md_file"

      echo "bench-run: wrote $json_file" >&2
      echo "bench-run: wrote $md_file" >&2
    '';
  };
in script
