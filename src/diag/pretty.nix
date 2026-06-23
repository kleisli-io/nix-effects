# Pretty-printing for diagnostic Errors.
#
# Three output forms:
#
#   pathSegments : Error -> [String]
#     Rendered position strings along the single-child chain from the
#     root to the first leaf or branching point. At a branching node,
#     the chain ends; per-sibling rendering is the caller's job.
#
#   oneLine : Error -> String
#     Single-line summary: `[Layer] msg @ seg -> seg -> ...`.
#
#   multiLine : Error -> String
#     Multi-line trace: summary, blame path (one segment per line),
#     layer-dispatched detail block (Kernel vs Generic), and the
#     optional hint. A branching endpoint contributes one indented
#     sub-trace per child.
#
# Chain walking is stack-safe by construction: direct recursion up to
# `fastPathLimit` frames, then a `builtins.genericClosure` worklist.
# The slow path's `key` depends on `builtins.seq` of the next node
# (WHNF only) so cross-step references resolve without rebuilding the
# chain at force time. `deepSeq` is wrong here: the payload is a
# recursive Error whose `children` holds the entire remaining chain,
# and forcing it deeply cascades through every descendant.
{ lib, fx, api, ... }:
let
  inherit (fx.diag.positions) renderSegment;

  fastPathLimit = 500;

  # Walk a single-child Error chain and collect `children[].position`
  # from root to leaf (or to the first branching node).
  chainPositions = err: chainFast [ ] err 0;

  chainFast = acc: err: depth:
    if builtins.length err.children != 1
    then acc
    else if depth >= fastPathLimit
    then chainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in chainFast (acc ++ [ edge.position ]) edge.error (depth + 1);

  # Slow path: genericClosure worklist. `key` WHNF-forces `nextErr` so
  # the next step reads a resolved attrset instead of re-entering the
  # prior chain at force time. Forcing `newAcc` keeps the ++ chain
  # short without touching the Error payload's structure.
  chainSlow = acc0: err0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _acc = acc0; _err = err0; }];
        operator = st:
          if builtins.length st._err.children != 1 then [ ]
          else
            let
              edge = builtins.elemAt st._err.children 0;
              nextErr = edge.error;
              newAcc = st._acc ++ [ edge.position ];
            in
            [{
              key = builtins.seq nextErr
                (builtins.seq newAcc (st.key + 1));
              _acc = newAcc;
              _err = nextErr;
            }];
      };
    in
    (lib.last steps)._acc;

  # Walk to the endpoint of the chain (the first node with
  # !=1 children).
  chainEndpoint = err: endpointFast err 0;

  endpointFast = err: depth:
    if builtins.length err.children != 1 then err
    else if depth >= fastPathLimit then endpointSlow err
    else endpointFast (builtins.elemAt err.children 0).error (depth + 1);

  endpointSlow = err0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _err = err0; }];
        operator = st:
          if builtins.length st._err.children != 1 then [ ]
          else
            let nextErr = (builtins.elemAt st._err.children 0).error;
            in [{
              key = builtins.seq nextErr (st.key + 1);
              _err = nextErr;
            }];
      };
    in
    (lib.last steps)._err;

  # Render an arbitrary Nix value compactly. Native recursion descends
  # once per nesting level, so a deep value (e.g. a quoted type on an
  # error path) overflows the host stack. Drive it with an explicit
  # task stack: `emit` appends a literal, `render` expands a value into
  # emit/render subtasks pushed in document order. Totality comes from
  # the worklist alone; `renderBudget` is an independent readability cap
  # (a decoupled display policy), never the safety mechanism.
  renderBudget = 4096;

  # Expand one value into the ordered task fragments that render it.
  renderTasks = v:
    if v == null then [{ emit = "null"; }]
    else if builtins.isString v then [{ emit = v; }]
    else if builtins.isBool v then [{ emit = if v then "true" else "false"; }]
    else if builtins.isInt v || builtins.isFloat v then [{ emit = toString v; }]
    else if builtins.isAttrs v && v ? tag then
      let extras = removeAttrs v [ "tag" "_tag" ]; in
      if extras == { }
      then [{ emit = v.tag; }]
      else [{ emit = "${v.tag}("; }] ++ fieldTasks ", " extras ++ [{ emit = ")"; }]
    else if builtins.isAttrs v then
      [{ emit = "{"; }] ++ fieldTasks "; " v ++ [{ emit = "}"; }]
    else if builtins.isList v then
      [{ emit = "["; }] ++ elemTasks ", " v ++ [{ emit = "]"; }]
    else if builtins.isFunction v then [{ emit = "<function>"; }]
    else [{ emit = "<?>"; }];

  # `k=<render val>` per attr in attr-name order, joined by `sep`.
  fieldTasks = sep: attrs:
    let
      pairs = lib.mapAttrsToList (k: val: { inherit k val; }) attrs;
      n = builtins.length pairs;
      frag = i:
        let p = builtins.elemAt pairs i; in
        [{ emit = "${p.k}="; } { render = p.val; }]
        ++ (if i < n - 1 then [{ emit = sep; }] else [ ]);
    in builtins.concatMap frag (builtins.genList (x: x) n);

  # `<render elem>` per element, joined by `sep`.
  elemTasks = sep: xs:
    let
      n = builtins.length xs;
      frag = i:
        [{ render = builtins.elemAt xs i; }]
        ++ (if i < n - 1 then [{ emit = sep; }] else [ ]);
    in builtins.concatMap frag (builtins.genList (x: x) n);

  # Push tasks so element 0 becomes the new head, preserving document order.
  pushTasks = tasks: s:
    let n = builtins.length tasks;
    in builtins.foldl'
      (st: i: { head = builtins.elemAt tasks (n - 1 - i); tail = st; })
      s
      (builtins.genList (x: x) n);

  renderValue = v0:
    let
      closure = builtins.genericClosure {
        startSet = [{ key = 0; stack = pushTasks [{ render = v0; }] null; out = ""; trunc = false; }];
        operator = item:
          if item.stack == null then [ ]
          else
            let
              h = item.stack.head;
              rest = item.stack.tail;
              isEmit = h ? emit;
              # The worklist drains the whole structure regardless of its
              # size, so totality is the stack's alone — disabling the
              # budget below leaves it total. The budget only bounds the
              # rendered string: once `out` fills, emit one `…` and drop
              # later literals while the walk runs to completion. Force
              # `out` each step or the lazily-threaded concat builds a
              # deferred chain whose final force recurses step-count deep.
              over = !item.trunc && builtins.stringLength item.out >= renderBudget;
              nextOut =
                if item.trunc || !isEmit then item.out
                else if over then item.out + "…"
                else item.out + h.emit;
              nextStack =
                if isEmit then rest
                else pushTasks (renderTasks h.render) rest;
            in builtins.seq nextOut [{
              key = item.key + 1;
              stack = nextStack;
              out = nextOut;
              trunc = item.trunc || over;
            }];
      };
      final = builtins.head (builtins.filter (it: it.stack == null) closure);
    in final.out;

  # Path rendering. Joined path uses " -> " so it reads in the same
  # direction as the descent (outer to inner).
  pathSegments = err: map renderSegment (chainPositions err);
  pathString = err:
    let segs = pathSegments err;
    in if segs == [ ] then ""
    else lib.concatStringsSep " -> " segs;

  # Layer tag for display. Safe on either Layer constant.
  layerTag = err: err.layer.tag;

  # One-line summary. Includes the path suffix only when non-empty.
  oneLine = err:
    let
      path = pathString err;
      suffix = if path == "" then "" else " @ ${path}";
    in
    "[${layerTag err}] ${err.msg}${suffix}";

  # Layer-dispatched detail block. Null fields are skipped so the
  # Kernel / Generic / Contract renderers share a uniform null-guard idiom.
  line = key: val:
    if val == null then null else "  ${key}: ${renderValue val}";

  kernelCoreLines = d: lib.filter (l: l != null) [
    (line "rule" d.rule)
    (line "expected" d.expected)
    (line "got" d.got)
    (line "ctx_depth" d.ctx_depth)
  ];

  # Cap on the binder list rendered under `frame.names`. Above this,
  # the rendered list is truncated and a `+N more` suffix is appended;
  # `frame.depth` always renders the true depth.
  frameBinderCap = 12;

  termLines = d:
    if d.term == null then [ ]
    else
      let
        tagPart = [ "  term: ${d.term.tag or "?"}" ];
        quotedPart =
          if (d.term.quoted or null) == null
          then [ ]
          else [ "  term.quoted: ${renderValue d.term.quoted}" ];
      in
      tagPart ++ quotedPart;

  frameLines = d:
    if d.frame == null then [ ]
    else
      let
        depth = d.frame.depth or 0;
        names = d.frame.names or [ ];
        nNames = builtins.length names;
        capped =
          if nNames > frameBinderCap
          then lib.take frameBinderCap names
          else names;
        listBody = lib.concatStringsSep ", " capped;
        truncSuffix =
          if nNames > frameBinderCap
          then " (+${toString (nNames - frameBinderCap)} more)"
          else "";
        namesLine = "  frame.names: [${listBody}]${truncSuffix}";
      in
      [
        "  frame.depth: ${toString depth}"
        namesLine
      ];

  traceLines = d:
    let trace = d.trace or [ ]; in
    if trace == [ ] then [ ]
    else
      let
        renderEntry = i:
          let
            entry = builtins.elemAt trace i;
            rule = entry.rule or null;
            seg = renderSegment entry.position;
            ruleStr = if rule == null then "(no rule)" else rule;
          in
          "    [${toString i}] rule=${ruleStr} via ${seg}";
        entries = builtins.genList renderEntry (builtins.length trace);
      in
      [ "  trace:" ] ++ entries;

  kernelDetailLines = d:
    kernelCoreLines d ++ termLines d ++ frameLines d ++ traceLines d;

  genericDetailLines = d: lib.filter (l: l != null) [
    (line "type" d.type)
    (line "context" d.context)
    (line "value" d.value)
    (line "desc" d.desc)
    (line "index" d.index)
    (if d.guard == null then null
    else "  guard: ${renderValue d.guard.predicate}")
  ];

  contractDetailLines = d: lib.filter (l: l != null) [
    (line "type" d.type)
    (line "context" d.context)
    (line "value" d.value)
    (if d.guard == null then null
    else "  guard: ${renderValue (d.guard.predicate or d.guard)}")
  ];

  detailLines = err:
    let tag = err.layer.tag; in
    if tag == "Kernel" then kernelDetailLines err.detail
    else if tag == "Generic" then genericDetailLines err.detail
    else if tag == "Contract" then contractDetailLines err.detail
    else [ ];

  # Render an intent-stack block from an already-computed positions
  # list. Factored out of `intentStackLines` so `multiLine` can reuse a
  # single chain walk for both `path` and `intent` rendering.
  intentLinesFromPositions = positions:
    let
      intents = lib.filter (s: builtins.isString s && s != "")
        (map (p: p.intent or null) positions);
    in
    if intents == [ ]
    then [ ]
    else [ "  intent:" ] ++ map (i: "    - ${i}") intents;

  # Per-position intent stack: walk the chain and render the intent
  # gloss. Standalone wrapper around `intentLinesFromPositions` for
  # consumers that don't already have the positions list in hand.
  intentStackLines = err: intentLinesFromPositions (chainPositions err);

  hintLines = err:
    if err.hint == null then [ ] else [ "  hint: ${err.hint.text}" ];

  # Indent every line of a multi-line block by two spaces.
  indent = s:
    let ls = lib.splitString "\n" s;
    in lib.concatStringsSep "\n" (map (l: "  ${l}") ls);

  # Multi-line trace. At a branching endpoint, emits one indented
  # sub-trace per child. Intent stack renders only on the chained form
  # (path non-empty); a leaf-only Error has no positions to gloss.
  #
  # Position chain is walked exactly once and reused for both `path` and
  # `intent:` block — `pathString err`/`intentStackLines err` would each
  # call `chainPositions err` independently.
  multiLine = err:
    let
      positions = chainPositions err;
      pathSegs = map renderSegment positions;
      path =
        if pathSegs == [ ] then ""
        else lib.concatStringsSep " -> " pathSegs;
      intentLines = intentLinesFromPositions positions;
      intentBlock =
        if intentLines == [ ] then ""
        else "\n" + lib.concatStringsSep "\n" intentLines;
      header =
        if path == ""
        then "[${layerTag err}] ${err.msg}"
        else "[${layerTag err}] ${err.msg}\n  path: ${path}${intentBlock}";
      endpoint = chainEndpoint err;
      leafBlock = lib.concatStringsSep "\n"
        (detailLines endpoint ++ hintLines endpoint);
      childrenOfEndpoint = endpoint.children;
      isBranch = builtins.length childrenOfEndpoint > 1;
      childBlocks = map
        (edge:
          let
            p = renderSegment edge.position;
            sub = multiLine edge.error;
          in
          "  at ${p}:\n${indent sub}"
        )
        childrenOfEndpoint;
      bodyLines =
        if isBranch
        then [ header ] ++ childBlocks
        else if leafBlock == ""
        then [ header ]
        else [ header leafBlock ];
    in
    lib.concatStringsSep "\n" bodyLines;

  # -- Chain fixtures reused by construction and walker tests. --
  leafErr = fx.diag.error.mkKernelError {
    rule = "check";
    msg = "type mismatch";
    expected = { tag = "VU"; level = 0; };
    got = { tag = "VU"; level = 1; };
  };

  # Build an n-deep nestUnder chain over a single leaf. Each hop is
  # an O(1) attrset build; foldl' threads the accumulator iteratively.
  chain5000 =
    builtins.foldl'
      (inner: _:
        fx.diag.error.nestUnder fx.diag.positions.DArgSort inner
      )
      leafErr
      (lib.range 1 5000);

in
api.namespace {
  description = "fx.diag.pretty: pretty-print diagnostic Errors — `pathSegments`/`pathString`/`oneLine`/`multiLine` walkers, stack-safe via genericClosure past 500 frames.";
  doc = ''
    Pretty-printing for diagnostic Errors.

    Exports:
      pathSegments : Error -> [String]
      pathString   : Error -> String
      oneLine      : Error -> String
      multiLine    : Error -> String

    Chain walkers recurse directly up to ${toString fastPathLimit}
    frames, then fall through to a `builtins.genericClosure` slow
    path that WHNF-forces the next node at each step.

    Pure data -> string; no effects.
  '';
  tests = {
    # -- pathSegments / pathString on leaves and chains --
    "pathSegments-leaf" = {
      expr = pathSegments leafErr;
      expected = [ ];
    };
    "pathString-leaf" = {
      expr = pathString leafErr;
      expected = "";
    };
    "pathSegments-one-hop" = {
      expr = pathSegments (fx.diag.error.nestUnder
        fx.diag.positions.DArgSort
        leafErr);
      expected = [ "arg.S" ];
    };
    "pathSegments-two-hops" = {
      expr = pathSegments
        (fx.diag.error.nestUnder fx.diag.positions.DArgSort
          (fx.diag.error.nestUnder fx.diag.positions.DPlusL
            leafErr));
      expected = [ "arg.S" "plus.L" ];
    };
    "pathString-two-hops" = {
      expr = pathString
        (fx.diag.error.nestUnder fx.diag.positions.DArgSort
          (fx.diag.error.nestUnder fx.diag.positions.DPlusL
            leafErr));
      expected = "arg.S -> plus.L";
    };

    # -- oneLine --
    "oneLine-leaf" = {
      expr = oneLine leafErr;
      expected = "[Kernel] type mismatch";
    };
    "oneLine-with-path" = {
      expr = oneLine (fx.diag.error.nestUnder
        fx.diag.positions.DArgSort
        leafErr);
      expected = "[Kernel] type mismatch @ arg.S";
    };
    "oneLine-generic" = {
      expr = oneLine (fx.diag.error.mkGenericError {
        value = 42;
        msg = "value does not inhabit description";
      });
      expected = "[Generic] value does not inhabit description";
    };

    # -- multiLine: Kernel leaf --
    "multiLine-kernel-leaf-has-header" = {
      expr =
        let ls = lib.splitString "\n" (multiLine leafErr);
        in builtins.elemAt ls 0;
      expected = "[Kernel] type mismatch";
    };
    "multiLine-kernel-leaf-has-rule" = {
      expr =
        let ls = lib.splitString "\n" (multiLine leafErr);
        in builtins.any (l: l == "  rule: check") ls;
      expected = true;
    };
    "multiLine-kernel-leaf-has-expected" = {
      expr =
        let ls = lib.splitString "\n" (multiLine leafErr);
        in builtins.any (l: l == "  expected: VU(level=0)") ls;
      expected = true;
    };
    "multiLine-kernel-leaf-has-got" = {
      expr =
        let ls = lib.splitString "\n" (multiLine leafErr);
        in builtins.any (l: l == "  got: VU(level=1)") ls;
      expected = true;
    };
    "multiLine-kernel-chain-has-path" = {
      expr =
        let
          err = fx.diag.error.nestUnder fx.diag.positions.DArgSort leafErr;
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  path: arg.S") ls;
      expected = true;
    };

    # -- multiLine: Generic leaf --
    "multiLine-generic-has-value" = {
      expr =
        let
          err = fx.diag.error.mkGenericError {
            type = "PersonT";
            value = { n = "wrong"; };
            msg = "m";
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  type: PersonT") ls;
      expected = true;
    };
    "multiLine-generic-guard-predicate-rendered" = {
      expr =
        let
          err = fx.diag.error.mkGenericError {
            value = 17;
            guard = { predicate = "x > 18"; };
            msg = "refinement failed";
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  guard: x > 18") ls;
      expected = true;
    };
    "multiLine-hint-rendered" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "desc-arg";
            msg = "m";
            hint = fx.diag.hints.mkHint "universe" "try using u 0";
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  hint: try using u 0") ls;
      expected = true;
    };

    # -- Branching endpoint renders one sub-trace per child --
    "multiLine-branch-renders-each-child" = {
      expr =
        let
          root = fx.diag.error.mkGenericError {
            type = "PersonT";
            value = { };
            msg = "record validation failed";
          };
          c1 = fx.diag.error.mkGenericError {
            value = "wrong";
            msg = "string is not Nat";
          };
          c2 = fx.diag.error.mkGenericError {
            value = 42;
            msg = "int is not String";
          };
          r1 = fx.diag.error.addChild (fx.diag.positions.Field "n") root c1;
          r2 = fx.diag.error.addChild (fx.diag.positions.Field "s") r1 c2;
          s = multiLine r2;
        in
        lib.all (sub: lib.strings.hasInfix sub s) [
          "at .n"
          "at .s"
          "string is not Nat"
          "int is not String"
        ];
      expected = true;
    };

    # -- Stack-safety stress: 5000-deep chain must complete. --
    "pathSegments-5000-deep-chain-length" = {
      expr = builtins.length (pathSegments chain5000);
      expected = 5000;
    };
    "pathString-5000-deep-chain-has-prefix" = {
      expr = lib.strings.hasPrefix "arg.S -> arg.S -> arg.S"
        (pathString chain5000);
      expected = true;
    };
    "oneLine-5000-deep-chain-has-header" = {
      expr = lib.strings.hasPrefix "[Kernel] type mismatch @ arg.S"
        (oneLine chain5000);
      expected = true;
    };
    "multiLine-5000-deep-chain-has-path-line" = {
      expr =
        let
          s = multiLine chain5000;
          ls = lib.splitString "\n" s;
        in
        builtins.any
          (l: lib.strings.hasPrefix "  path: arg.S -> arg.S" l)
          ls;
      expected = true;
    };

    # -- 3-layer detail dispatch --
    "multiLine-contract-renders-type" = {
      expr =
        let
          err = fx.diag.error.mkContractError {
            type = "PositiveInt";
            value = -3;
            guard = { predicate = "x > 0"; };
            msg = "refinement failed";
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  type: PositiveInt") ls;
      expected = true;
    };
    "multiLine-contract-renders-guard" = {
      expr =
        let
          err = fx.diag.error.mkContractError {
            value = -3;
            guard = { predicate = "x > 0"; };
            msg = "refinement failed";
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  guard: x > 0") ls;
      expected = true;
    };
    "oneLine-contract" = {
      expr = oneLine (fx.diag.error.mkContractError {
        value = -3;
        guard = { predicate = "x > 0"; };
        msg = "refinement failed";
      });
      expected = "[Contract] refinement failed";
    };

    # -- term block --
    "multiLine-kernel-term-tag-renders" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "infer";
            msg = "no inference rule for term shape pair";
            term = { tag = "pair"; };
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  term: pair") ls;
      expected = true;
    };
    "multiLine-kernel-term-quoted-renders" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "infer";
            msg = "m";
            term = { tag = "pair"; quoted = { tag = "pair"; fst = "tt"; snd = "tt"; }; };
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (lib.strings.hasPrefix "  term.quoted: pair(") ls;
      expected = true;
    };
    "multiLine-kernel-term-null-omitted" = {
      expr =
        let
          err = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (lib.strings.hasPrefix "  term") ls;
      expected = false;
    };

    # -- frame block --
    "multiLine-kernel-frame-depth-renders" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "r";
            msg = "m";
            frame = { depth = 7; env = [ ]; types = [ ]; names = [ "a" "b" ]; };
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  frame.depth: 7") ls;
      expected = true;
    };
    "multiLine-kernel-frame-names-renders" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "r";
            msg = "m";
            frame = { depth = 3; env = [ ]; types = [ ]; names = [ "x" "y" "z" ]; };
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  frame.names: [x, y, z]") ls;
      expected = true;
    };
    "multiLine-kernel-frame-names-truncated-above-cap" = {
      expr =
        let
          names = builtins.genList (i: "v${toString i}") 20;
          err = fx.diag.error.mkKernelError {
            rule = "r";
            msg = "m";
            frame = { depth = 20; env = [ ]; types = [ ]; inherit names; };
          };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (lib.strings.hasInfix "(+8 more)") ls;
      expected = true;
    };
    "multiLine-kernel-frame-null-omitted" = {
      expr =
        let
          err = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (lib.strings.hasPrefix "  frame") ls;
      expected = false;
    };

    # -- trace block --
    "multiLine-kernel-trace-renders-header" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          err = fx.diag.error.appendTrace "check"
            fx.diag.positions.Sub
            leaf;
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  trace:") ls;
      expected = true;
    };
    "multiLine-kernel-trace-renders-rule-and-segment" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          err = fx.diag.error.appendTrace "check"
            fx.diag.positions.Sub
            leaf;
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "    [0] rule=check via sub") ls;
      expected = true;
    };
    "multiLine-kernel-trace-empty-omitted" = {
      expr =
        let
          err = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  trace:") ls;
      expected = false;
    };
    "multiLine-kernel-trace-null-rule-renders-placeholder" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          err = fx.diag.error.appendTrace null
            fx.diag.positions.AnnTerm
            leaf;
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "    [0] rule=(no rule) via ann.term") ls;
      expected = true;
    };

    # -- intent stack --
    "multiLine-chain-intent-renders-from-root-to-leaf" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          err = fx.diag.error.nestUnder fx.diag.positions.AppHead
            (fx.diag.error.nestUnder fx.diag.positions.LamBody leaf);
          ls = lib.splitString "\n" (multiLine err);
          intents = lib.filter (lib.strings.hasPrefix "    - ") ls;
        in
        intents;
      expected = [
        "    - the function applied"
        "    - the body of the lambda under its bound variable"
      ];
    };
    "multiLine-leaf-no-intent-block" = {
      expr =
        let
          err = fx.diag.error.mkKernelError { rule = "r"; msg = "m"; };
          ls = lib.splitString "\n" (multiLine err);
        in
        builtins.any (l: l == "  intent:") ls;
      expected = false;
    };

    # -- renderValue smoke --
    "renderValue-null" = {
      expr = renderValue null;
      expected = "null";
    };
    "renderValue-string" = {
      expr = renderValue "hello";
      expected = "hello";
    };
    "renderValue-int" = {
      expr = renderValue 42;
      expected = "42";
    };
    "renderValue-tag-only" = {
      expr = renderValue { tag = "VUnit"; };
      expected = "VUnit";
    };
    "renderValue-tag-with-field" = {
      expr = renderValue { tag = "VU"; level = 0; };
      expected = "VU(level=0)";
    };
  };

  value = {
    pathSegments = api.leaf {
      value = pathSegments;
      description = "pathSegments: walk an `Error` from root to leaf collecting position tags as strings; stack-safe to kernel-descent depth via the same fast/slow split as the other chain walkers.";
      signature = "pathSegments : Error -> [String]";
    };
    pathString = api.leaf {
      value = pathString;
      description = "pathString: render `Error`'s root-to-leaf positions as a dotted path (e.g. `\"DArgSort.PiCod.AppArg\"`); useful for log lines and one-line diagnostic summaries.";
      signature = "pathString : Error -> String";
    };
    oneLine = api.leaf {
      value = oneLine;
      description = "oneLine: render `Error` as a single-line diagnostic combining `pathString`, layer tag, msg, and (when present) hint text — suited for editor squigglies and terse log output.";
      signature = "oneLine : Error -> String";
    };
    multiLine = api.leaf {
      value = multiLine;
      description = "multiLine: render `Error` as a multi-line block — header line, blame path, detail fields rendered with `renderValue`, and the optional hint text indented under the leaf.";
      signature = "multiLine : Error -> String";
    };
    renderValue = api.leaf {
      value = renderValue;
      description = "renderValue: render an arbitrary detail value (term/type/payload) as a string suitable for inclusion in diagnostic output; centralises the formatting policy across `oneLine`/`multiLine`.";
      signature = "renderValue : Any -> String";
    };

  };
}
