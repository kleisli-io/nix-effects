# Stack-safety gate runner.
#
# Runs each `workloads.tc.stress-depth` leaf in its own resource-capped
# subprocess and classifies the exit: a host stack overflow is not
# catchable inside the evaluator, so the totality verdict lives at the
# process boundary, not in an in-evaluator value. Classification:
#   ok              exit 0 — the walk completed (heap-bounded)
#   stack-overflow  the walk exhausted the host call stack
#   oom             the subprocess hit the memory cap
#   timeout         the subprocess hit the runtime cap
#
# A leaf PASSES iff `ok`. The gate is RED while any walk is still native
# and turns GREEN as each is defunctionalized into a heap machine; the
# `control` leaves (below crossover) must stay GREEN as a construction
# check. Exits non-zero if any leaf is not `ok` (suppress with --report).
#
# A crossover depth only means something against a fixed evaluator and a
# fixed recursion ceiling. `nix-instantiate` is `pkgs.nix` (pinned via
# pins.nix) and every probe runs with an explicit `--option
# max-call-depth`, so a witness that overflows here overflows anywhere —
# not just under whatever `max-call-depth` the ambient environment sets.
{ lib, pkgs }:

let
  enumerateExpr = ''
    benchPath:
    let
      bench = import benchPath { };
      sd = bench.workloads.tc."stress-depth";
      probes = builtins.attrNames sd;
    in builtins.concatMap
      (p: map (l: p + "." + l) (builtins.attrNames sd.''${p}))
      probes
  '';

  script = pkgs.writeShellApplication {
    name = "nix-effects-bench-stress";
    runtimeInputs = [ pkgs.jq pkgs.coreutils pkgs.gnugrep pkgs.nix pkgs.systemd ];
    text = ''
      # shellcheck disable=SC2016
      ENUM_EXPR=${lib.escapeShellArg enumerateExpr}

      bench_dir="$PWD/bench"
      mem="6G"
      timeout_s=90
      mcd=10000
      filter=""
      report=0

      usage() {
        cat >&2 <<EOF
      Usage: nix-effects-bench-stress [options]

      Run each tc.stress-depth probe leaf in a capped subprocess and
      classify the exit (ok / stack-overflow / oom / timeout).

      Options:
        --mem <s>         MemoryMax for each probe (default 6G).
        --timeout <n>     RuntimeMaxSec for each probe (default 90).
        --max-call-depth <n>  Pinned evaluator call-depth ceiling (default 10000).
        --filter <regex>  Run only leaves whose '<probe>.<leaf>' matches.
        --report          Print the table but always exit 0.
        --bench-dir <p>   Path to bench directory (default: \$PWD/bench).
      EOF
        exit "$1"
      }

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --mem)        mem="$2"; shift 2 ;;
          --timeout)    timeout_s="$2"; shift 2 ;;
          --max-call-depth) mcd="$2"; shift 2 ;;
          --filter)     filter="$2"; shift 2 ;;
          --report)     report=1; shift ;;
          --bench-dir)  bench_dir="$2"; shift 2 ;;
          -h|--help)    usage 0 ;;
          *) echo "unknown arg: $1" >&2; usage 2 ;;
        esac
      done

      [[ -d "$bench_dir" ]] || { echo "bench dir not found: $bench_dir" >&2; exit 2; }
      bench_dir="$(realpath "$bench_dir")"

      leaves="$(
        nix-instantiate --eval --strict --json \
          --expr "(let f = $ENUM_EXPR; in f $bench_dir)" | jq -r '.[]'
      )"

      printf '%-22s %-8s %s\n' "PROBE.LEAF" "VERDICT" "PASS"
      printf '%-22s %-8s %s\n' "----------------------" "--------" "----"

      fail=0
      for leaf in $leaves; do
        [[ -z "$filter" || "$leaf" =~ $filter ]] || continue
        probe="''${leaf%.*}"; sub="''${leaf#*.}"
        expr="(import \"$bench_dir\" { }).workloads.tc.\"stress-depth\".\"$probe\".\"$sub\""

        if out="$(systemd-run --user --scope \
          -p MemoryMax="$mem" -p MemorySwapMax=0 -p RuntimeMaxSec="$timeout_s" -q \
          nix-instantiate --option max-call-depth "$mcd" --eval --strict --expr "$expr" 2>&1)"; then rc=0; else rc=$?; fi

        if [[ $rc -eq 0 ]]; then verdict="ok"
        elif grep -qi 'stack overflow' <<<"$out"; then verdict="overflow"
        elif [[ $rc -eq 137 ]] || grep -qiE 'out of memory|cannot allocate' <<<"$out"; then verdict="oom"
        elif [[ $rc -eq 124 ]] || grep -qiE 'timeout|time limit' <<<"$out"; then verdict="timeout"
        else verdict="other($rc)"
        fi

        if [[ "$verdict" == "ok" ]]; then pass="yes"; else pass="NO"; fail=$((fail + 1)); fi
        printf '%-22s %-8s %s\n' "$leaf" "$verdict" "$pass"
      done

      echo ""
      if [[ "$fail" -eq 0 ]]; then
        echo "stress: all probes heap-bounded (GREEN)"
      else
        echo "stress: $fail probe(s) still native (RED)"
      fi
      [[ "$report" -eq 1 || "$fail" -eq 0 ]] && exit 0
      exit 1
    '';
  };
in
script
