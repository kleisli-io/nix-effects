# Samples → run record.
#
# Reads a JSON samples file produced by the runner shell script and threads
# it through `bench.measure.summarize` + `bench.format.emit{JSON,RunMarkdown}`.
# Factored out of the shell driver so the math lives in Nix (consistent with
# gate + compare) while I/O lives in bash.
#
# Input samples JSON schema:
#   { name, timestamp, nix, system, runsPerWorkload,
#     workloads = { <dotted-path> = [ { stats = <NIX_SHOW_STATS json>;
#                                       wallMs = <int>; }, ... ]; ... }; }
#
# Output:
#   { json = <string>; markdown = <string>; run = <run record>; }
{ benchPath, samplesPath }:

let
  bench = import benchPath { };
  measure = bench.measure;
  format = bench.format;

  input = builtins.fromJSON (builtins.readFile samplesPath);

  buildSample = s: {
    allocs = measure.pickAllocs s.stats;
    cpu = measure.pickCpu s.stats;
    gc = measure.pickGc s.stats;
    wall = s.wallMs or 0;
  };

  results = builtins.mapAttrs
    (_: samples: measure.summarize (map buildSample samples))
    input.workloads;

  run = {
    inherit (input) name timestamp nix system runsPerWorkload;
    inherit results;
  };
in {
  json = format.emitJSON run;
  markdown = format.emitRunMarkdown run;
  inherit run;
}
