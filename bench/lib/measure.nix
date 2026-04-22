# Pure measurement helpers: stats-JSON projection and sample aggregation.
#
# Consumers pass in the attrset that `NIX_SHOW_STATS=1` writes to stderr
# (parsed through `builtins.fromJSON`). We project the fields we gate on,
# then aggregate across N runs into median / p95 summaries.
#
# Alloc counts are deterministic across runs of the same expression on the
# same Nix version: identical counts → `alloc_deterministic = true`, any
# divergence → `false` and the workload is excluded from alloc-based gating.
{ lib }:

let
  # Project the stats fields we gate on into a flat record. Defaults to 0 for
  # missing fields so different Nix versions don't crash the comparator.
  pickAllocs = stats: {
    values                = stats.values.number                   or 0;
    valuesBytes           = stats.values.bytes                    or 0;
    envs                  = stats.envs.number                     or 0;
    envsElements          = stats.envs.elements                   or 0;
    envsBytes             = stats.envs.bytes                      or 0;
    listElements          = stats.list.elements                   or 0;
    listConcats           = stats.list.concats                    or 0;
    listBytes             = stats.list.bytes                      or 0;
    sets                  = stats.sets.number                     or 0;
    setsElements          = stats.sets.elements                   or 0;
    setsBytes             = stats.sets.bytes                      or 0;
    symbols               = stats.symbols.number                  or 0;
    symbolsBytes          = stats.symbols.bytes                   or 0;
    thunks                = stats.nrThunks                        or 0;
    functionCalls         = stats.nrFunctionCalls                 or 0;
    primOpCalls           = stats.nrPrimOpCalls                   or 0;
    lookups               = stats.nrLookups                       or 0;
    avoided               = stats.nrAvoided                       or 0;
    opUpdates             = stats.nrOpUpdates                     or 0;
    opUpdateValuesCopied  = stats.nrOpUpdateValuesCopied          or 0;
  };

  # cpuTime: in-process seconds reported by the evaluator (excludes nix-instantiate
  # startup). Preferred over wall-clock for CPU-axis regression signal.
  pickCpu = stats: stats.cpuTime or 0.0;

  # Informational only; not gated. Surfaced in reports.
  pickGc = stats: {
    cycles    = stats.gc.cycles     or 0;
    bytes     = stats.gc.totalBytes or 0;
    heapSize  = stats.gc.heapSize   or 0;
  };

  # Median of a numeric list. Integer inputs yield truncated-int output for the
  # even-length case; float inputs yield float output.
  median = xs:
    let
      sorted = lib.sort (a: b: a < b) xs;
      n = builtins.length sorted;
      mid = n / 2;
      isOdd = (mid * 2) != n;
    in
      if n == 0 then 0
      else if isOdd then builtins.elemAt sorted mid
      else
        let a = builtins.elemAt sorted (mid - 1);
            b = builtins.elemAt sorted mid;
        in (a + b) / 2;

  # 95th percentile (nearest-rank method). For N samples, returns the
  # ⌈0.95·N⌉-th smallest value (1-indexed), which for N=5 gives sample[4]
  # (max of 5), for N=20 gives sample[18] (second largest).
  p95 = xs:
    let
      sorted = lib.sort (a: b: a < b) xs;
      n = builtins.length sorted;
      ceilRank = (95 * n + 99) / 100;
      idx = if ceilRank < 1 then 0 else ceilRank - 1;
    in
      if n == 0 then 0 else builtins.elemAt sorted idx;

  # Signed percentage delta: 100 * (current - baseline) / baseline, int
  # arithmetic. Returns a sentinel 10^6 when baseline == 0 and current != 0.
  pctDelta = baseline: current:
    if baseline == 0 then (if current == 0 then 0 else 1000000)
    else ((current - baseline) * 100) / baseline;

  # Signed permille delta: 1000 * (current - baseline) / baseline. Finer
  # granularity than pct for alloc regressions — used by the gate's 0.5%
  # (= 5‰) tolerance.
  permilleDelta = baseline: current:
    if baseline == 0 then (if current == 0 then 0 else 10000000)
    else ((current - baseline) * 1000) / baseline;

  # True iff every allocation record in the list is attrset-equal to the first.
  # Deterministic expressions produce identical alloc records on the same Nix
  # version; divergence indicates evaluation-order sensitivity (e.g., GC-timing-
  # dependent laziness) and excludes the workload from alloc-based gating.
  allocsIdentical = allocsList:
    if builtins.length allocsList <= 1 then true
    else
      let first = builtins.head allocsList;
      in builtins.all (a: a == first) (builtins.tail allocsList);

  # Aggregate N samples of `{ allocs, cpu, wall, gc }` into a summary record.
  # Wall is optional (integer ms, captured by the runner); cpu is seconds float.
  summarize = samples:
    let
      allAllocs = map (s: s.allocs) samples;
      cpus = map (s: s.cpu) samples;
      walls = map (s: s.wall or 0) samples;
      deterministic = allocsIdentical allAllocs;
    in {
      alloc_deterministic = deterministic;
      allocs = if deterministic
               then builtins.head allAllocs
               else { };  # when non-deterministic, gate inspects allocs per-sample
      cpu = {
        p50 = median cpus;
        p95 = p95 cpus;
      };
      wall = {
        p50 = median walls;
        p95 = p95 walls;
      };
      runs = builtins.length samples;
    };

in {
  inherit pickAllocs pickCpu pickGc;
  inherit median p95 pctDelta permilleDelta;
  inherit allocsIdentical summarize;
}
