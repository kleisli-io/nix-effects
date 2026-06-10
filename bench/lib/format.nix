# Pure serialisers: bench runs and gate results to JSON / markdown.
#
# Emitted JSON is stable-sorted at every attrset level so byte-wise diffs
# between runs reflect only value changes.
#
# Markdown tables compute column widths from the data they render. The
# width of a variable column is max(header-word length, longest cell
# content, table-specific minimum). Separators match the computed cell
# widths exactly so GFM renderers and terminal `cat` both align.
{ lib }:

let
  sortKeys = v:
    if builtins.isAttrs v then
      lib.listToAttrs
        (map (k: { name = k; value = sortKeys v.${k}; })
          (lib.sort (a: b: a < b) (builtins.attrNames v)))
    else if builtins.isList v then map sortKeys v
    else v;

  emitJSON = run: builtins.toJSON (sortKeys run);

  # Build a run of `n` copies of `c` — avoids truncation bugs that bit the
  # previous fixed-length fill string at large column widths.
  repeatChar = c: n:
    if n <= 0 then ""
    else lib.concatStrings (lib.lists.replicate n c);

  padRight = n: s:
    let len = builtins.stringLength s;
    in if len >= n then s else s + repeatChar " " (n - len);

  padLeft = n: s:
    let len = builtins.stringLength s;
    in if len >= n then s else repeatChar " " (n - len) + s;

  # Signed string: "+42" or "-3".
  signed = n: if n > 0 then "+" + toString n else toString n;

  # Right-aligned GFM column separator of total width n (n-1 dashes + ':').
  rightAlignSep = n: repeatChar "-" (n - 1) + ":";

  # Left-aligned GFM column separator of total width n.
  leftAlignSep = n: repeatChar "-" n;

  # Longest string in `xs`, floored at `minLen`.
  maxLen = minLen: xs:
    builtins.foldl'
      (acc: s: let l = builtins.stringLength s; in if l > acc then l else acc)
      minLen
      xs;

  # Gate status symbol. The same vocabulary is used by open-regressions
  # (prefix "OPEN" / "RECOVERED" / "UNMEASURED") so the status column
  # width is computed dynamically from actual values.
  gateStatusSym = status:
    {
      pass = "PASS";
      fail_allocs = "FAIL allocs";
      fail_cpu = "FAIL cpu";
      warn_cpu = "WARN cpu";
      warn_heap = "WARN heap";
    }.${status} or status;

  auditStatusSym = status:
    {
      recovered = "RECOVERED";
      open_allocs = "OPEN allocs";
      open_cpu = "OPEN cpu";
      open_warn = "OPEN warn";
      unmeasured = "UNMEASURED";
    }.${status} or status;

  # ---- Run report ----

  emitRunMarkdown = run:
    let
      names = lib.sort (a: b: a < b) (builtins.attrNames run.results);
      workloadWidth = maxLen (builtins.stringLength "Workload") names;

      # Numeric columns are bounded by observable workload costs; hold them
      # static so independent runs on different subsets retain a uniform
      # visual footprint.
      valuesWidth = 10;
      thunksWidth = 10;
      cpuWidth = 8;
      wallWidth = 8;

      row = w:
        let
          r = run.results.${w};
          allocs = toString (r.allocs.values or 0);
          thunks = toString (r.allocs.thunks or 0);
          cpuMs = toString (builtins.floor (r.cpu.p50 * 1000));
          wallMs = toString r.wall.p50;
        in
        "| ${padRight workloadWidth w} | ${padLeft valuesWidth allocs} | ${padLeft thunksWidth thunks} | ${padLeft cpuWidth cpuMs} | ${padLeft wallWidth wallMs} |";

      header = "| ${padRight workloadWidth "Workload"} | ${padLeft valuesWidth "values"} | ${padLeft thunksWidth "thunks"} | ${padLeft cpuWidth "cpu ms"} | ${padLeft wallWidth "wall ms"} |";
      sep = "|" + leftAlignSep (workloadWidth + 2) + "|"
        + rightAlignSep (valuesWidth + 2) + "|" + rightAlignSep (thunksWidth + 2) + "|"
        + rightAlignSep (cpuWidth + 2) + "|" + rightAlignSep (wallWidth + 2) + "|";
      rows = map row names;

      meta = ''
        # Bench run: ${run.name or "unnamed"}

        - **Timestamp**: ${run.timestamp or "?"}
        - **Nix**: ${run.nix or "?"}
        - **System**: ${run.system or "?"}
        - **Runs per workload**: ${toString (run.runsPerWorkload or 0)}

      '';
    in
    meta + header + "\n" + sep + "\n" + builtins.concatStringsSep "\n" rows + "\n";

  # ---- Gate report ----

  emitGateMarkdown = { gateResult, baselineName ? "baseline", currentName ? "current" }:
    let
      classifications = gateResult.classifications;
      workloadWidth = maxLen
        (builtins.stringLength "Workload")
        (map (c: c.workload) classifications);
      statusWidth = maxLen
        (builtins.stringLength "Status")
        (map (c: gateStatusSym c.status) classifications);
      reasonWidth = maxLen
        (builtins.stringLength "Reason")
        (map (c: c.reason) classifications);

      row = c:
        "| ${padRight workloadWidth c.workload} | ${padRight statusWidth (gateStatusSym c.status)} | ${padRight reasonWidth c.reason} |";

      header = "| ${padRight workloadWidth "Workload"} | ${padRight statusWidth "Status"} | ${padRight reasonWidth "Reason"} |";
      sep = "|" + leftAlignSep (workloadWidth + 2) + "|"
        + leftAlignSep (statusWidth + 2) + "|"
        + leftAlignSep (reasonWidth + 2) + "|";
      rows = map row classifications;

      # Per-failing-workload blame: top ± counters with base→cur (±‰),
      # decreases included, so a relocation reads at a glance.
      blameOf = c:
        let
          movers = lib.take 6 (c.blame or [ ]);
          fmt = m:
            "- `${m.field}`: ${toString m.baseline} → ${toString m.current} (${signed m.deltaPermille}‰)"
            + (lib.optionalString m.codeSize "  [code-size]");
        in
        if movers == [ ]
        then null
        else "**${c.workload}**\n" + builtins.concatStringsSep "\n" (map fmt movers);

      blameBlocks = builtins.filter (b: b != null) (map blameOf gateResult.hardFails);
      blameSection =
        if blameBlocks == [ ]
        then ""
        else "\n## Blame (top ± movers per failing workload)\n\n"
          + builtins.concatStringsSep "\n\n" blameBlocks + "\n";

      # Work axis: per-probe step slope vs the declared contract. Omitted
      # entirely when no probes are gated.
      stepResults = gateResult.stepResults or [ ];
      stepStatusSym = status:
        { pass = "PASS"; fail_steps = "FAIL steps"; }.${status} or status;
      stepSection =
        if stepResults == [ ]
        then ""
        else
          let
            probeWidth = maxLen (builtins.stringLength "Probe") (map (s: s.probe) stepResults);
            contractWidth = maxLen (builtins.stringLength "Contract") (map (s: toString s.contractSlope) stepResults);
            measuredWidth = maxLen (builtins.stringLength "Measured") (map (s: toString s.measuredSlope) stepResults);
            deltaWidth = maxLen (builtins.stringLength "Delta") (map (s: signed s.deltaPermille) stepResults);
            sStatusWidth = maxLen (builtins.stringLength "Status") (map (s: stepStatusSym s.status) stepResults);
            sRow = s:
              "| ${padRight probeWidth s.probe} | ${padLeft contractWidth (toString s.contractSlope)} | ${padLeft measuredWidth (toString s.measuredSlope)} | ${padLeft deltaWidth (signed s.deltaPermille)} | ${padRight sStatusWidth (stepStatusSym s.status)} |";
            sHeader = "| ${padRight probeWidth "Probe"} | ${padLeft contractWidth "Contract"} | ${padLeft measuredWidth "Measured"} | ${padLeft deltaWidth "Delta"} | ${padRight sStatusWidth "Status"} |";
            sSep = "|" + leftAlignSep (probeWidth + 2) + "|"
              + rightAlignSep (contractWidth + 2) + "|" + rightAlignSep (measuredWidth + 2) + "|"
              + rightAlignSep (deltaWidth + 2) + "|" + leftAlignSep (sStatusWidth + 2) + "|";
          in
          "\n## Step axis (work)\n\n"
          + "Per-level CEK transition slope vs the declared contract (delta in ‰).\n\n"
          + sHeader + "\n" + sSep + "\n"
          + builtins.concatStringsSep "\n" (map sRow stepResults) + "\n";

      stepFailsLine =
        lib.optionalString (stepResults != [ ])
          "- **Step-axis fails**: ${toString (builtins.length (gateResult.stepFails or [ ]))}\n";

      summary = ''
        # Bench gate: ${baselineName} → ${currentName}

        - **Hard fails**: ${toString (builtins.length gateResult.hardFails)}
        - **Overridden (trailer)**: ${toString (builtins.length gateResult.overridden)}
        - **Soft warns**: ${toString (builtins.length gateResult.softWarns)}
        - **New workloads (no baseline)**: ${toString (builtins.length gateResult.newWorkloads)}
        - **Retired workloads (absent from current)**: ${toString (builtins.length gateResult.retiredWorkloads)}
        ${stepFailsLine}- **Verdict**: ${if gateResult.pass then "PASS" else "FAIL"}

      '';
    in
    summary + header + "\n" + sep + "\n" + builtins.concatStringsSep "\n" rows + "\n" + stepSection + blameSection;

  # ---- Open-regressions audit ----

  emitOpenRegressionsMarkdown = { entries, since }:
    let
      commitWidth = 10; # substring-capped in the finalizer.
      workloadWidth = maxLen
        (builtins.stringLength "Workload")
        (map (e: e.workload) entries);
      statusWidth = maxLen
        (builtins.stringLength "Status")
        (map (e: auditStatusSym e.status) entries);
      reasonWidth = maxLen
        (builtins.stringLength "Reason")
        (map (e: e.reason) entries);

      row = e:
        "| ${padRight commitWidth (builtins.substring 0 commitWidth e.sha)} | ${padRight workloadWidth e.workload} | ${padRight statusWidth (auditStatusSym e.status)} | ${padRight reasonWidth e.reason} |";

      header = "| ${padRight commitWidth "Commit"} | ${padRight workloadWidth "Workload"} | ${padRight statusWidth "Status"} | ${padRight reasonWidth "Reason"} |";
      sep = "|" + leftAlignSep (commitWidth + 2) + "|"
        + leftAlignSep (workloadWidth + 2) + "|"
        + leftAlignSep (statusWidth + 2) + "|"
        + leftAlignSep (reasonWidth + 2) + "|";
      rows = map row entries;

      openCount = builtins.length (builtins.filter (e: e.status != "recovered") entries);
      recoveredCount = builtins.length (builtins.filter (e: e.status == "recovered") entries);

      summary = ''
        # Open perf regressions (range: ${since})

        - **Acknowledged regressions in range**: ${toString (builtins.length entries)}
        - **Recovered** (within budget at current metrics): ${toString recoveredCount}
        - **Open** (still above budget): ${toString openCount}

      '';
      body =
        if entries == [ ]
        then "_No Perf-regression trailers in range._\n"
        else header + "\n" + sep + "\n" + builtins.concatStringsSep "\n" rows + "\n";
    in
    summary + body;

in
{
  inherit sortKeys emitJSON emitRunMarkdown emitGateMarkdown emitOpenRegressionsMarkdown;
  inherit padLeft padRight signed maxLen;
}
