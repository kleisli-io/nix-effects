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
  inherit (api) mk;
  inherit (fx.diag.positions) renderSegment;

  fastPathLimit = 500;

  # Walk a single-child Error chain and collect `children[].position`
  # from root to leaf (or to the first branching node).
  chainPositions = err: chainFast [] err 0;

  chainFast = acc: err: depth:
    if builtins.length err.children != 1
    then acc
    else if depth >= fastPathLimit
    then chainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in chainFast (acc ++ [edge.position]) edge.error (depth + 1);

  # Slow path: genericClosure worklist. `key` WHNF-forces `nextErr` so
  # the next step reads a resolved attrset instead of re-entering the
  # prior chain at force time. Forcing `newAcc` keeps the ++ chain
  # short without touching the Error payload's structure.
  chainSlow = acc0: err0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _acc = acc0; _err = err0; }];
        operator = st:
          if builtins.length st._err.children != 1 then []
          else
            let
              edge = builtins.elemAt st._err.children 0;
              nextErr = edge.error;
              newAcc = st._acc ++ [edge.position];
            in [{
              key = builtins.seq nextErr
                      (builtins.seq newAcc (st.key + 1));
              _acc = newAcc;
              _err = nextErr;
            }];
      };
    in (lib.last steps)._acc;

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
          if builtins.length st._err.children != 1 then []
          else
            let nextErr = (builtins.elemAt st._err.children 0).error;
            in [{
              key = builtins.seq nextErr (st.key + 1);
              _err = nextErr;
            }];
      };
    in (lib.last steps)._err;

  # Render an arbitrary Nix value compactly. Bounded by the shape of
  # the value itself (typically a tagged record with one or two
  # fields); no walker discipline needed.
  renderValue = v:
    if v == null then "null"
    else if builtins.isString v then v
    else if builtins.isBool v then (if v then "true" else "false")
    else if builtins.isInt v || builtins.isFloat v then toString v
    else if builtins.isAttrs v && v ? tag then
      let
        extras = removeAttrs v [ "tag" "_tag" ];
        fields = lib.mapAttrsToList
          (k: val: "${k}=${renderValue val}") extras;
      in if fields == []
         then v.tag
         else "${v.tag}(${lib.concatStringsSep ", " fields})"
    else if builtins.isAttrs v then
      "{${lib.concatStringsSep "; "
          (lib.mapAttrsToList
            (k: val: "${k}=${renderValue val}") v)}}"
    else if builtins.isList v then
      "[${lib.concatStringsSep ", " (map renderValue v)}]"
    else if builtins.isFunction v then "<function>"
    else "<?>";

  # Path rendering. Joined path uses " -> " so it reads in the same
  # direction as the descent (outer to inner).
  pathSegments = err: map renderSegment (chainPositions err);
  pathString = err:
    let segs = pathSegments err;
    in if segs == [] then ""
       else lib.concatStringsSep " -> " segs;

  # Layer tag for display. Safe on either Layer constant.
  layerTag = err: err.layer.tag;

  # One-line summary. Includes the path suffix only when non-empty.
  oneLine = err:
    let
      path = pathString err;
      suffix = if path == "" then "" else " @ ${path}";
    in "[${layerTag err}] ${err.msg}${suffix}";

  # Layer-dispatched detail block. Null fields are skipped so the
  # Kernel / Generic renderers share a uniform null-guard idiom.
  line = key: val:
    if val == null then null else "  ${key}: ${renderValue val}";

  kernelDetailLines = d: lib.filter (l: l != null) [
    (line "rule" d.rule)
    (line "expected" d.expected)
    (line "got" d.got)
    (line "ctx_depth" d.ctx_depth)
  ];

  genericDetailLines = d: lib.filter (l: l != null) [
    (line "type" d.type)
    (line "context" d.context)
    (line "value" d.value)
    (line "desc" d.desc)
    (line "index" d.index)
    (if d.guard == null then null
     else "  guard: ${renderValue d.guard.predicate}")
  ];

  detailLines = err:
    if err.layer.tag == "Kernel"
    then kernelDetailLines err.detail
    else genericDetailLines err.detail;

  hintLines = err:
    if err.hint == null then [] else [ "  hint: ${err.hint}" ];

  # Indent every line of a multi-line block by two spaces.
  indent = s:
    let ls = lib.splitString "\n" s;
    in lib.concatStringsSep "\n" (map (l: "  ${l}") ls);

  # Multi-line trace. At a branching endpoint, emits one indented
  # sub-trace per child.
  multiLine = err:
    let
      path = pathString err;
      header =
        if path == ""
        then "[${layerTag err}] ${err.msg}"
        else "[${layerTag err}] ${err.msg}\n  path: ${path}";
      endpoint = chainEndpoint err;
      leafBlock = lib.concatStringsSep "\n"
                    (detailLines endpoint ++ hintLines endpoint);
      childrenOfEndpoint = endpoint.children;
      isBranch = builtins.length childrenOfEndpoint > 1;
      childBlocks = map (edge:
        let
          p = renderSegment edge.position;
          sub = multiLine edge.error;
        in "  at ${p}:\n${indent sub}"
      ) childrenOfEndpoint;
      bodyLines =
        if isBranch
        then [ header ] ++ childBlocks
        else if leafBlock == ""
        then [ header ]
        else [ header leafBlock ];
    in lib.concatStringsSep "\n" bodyLines;

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
    builtins.foldl' (inner: _:
      fx.diag.error.nestUnder fx.diag.positions.DArgSort inner
    ) leafErr (lib.range 1 5000);

in mk {
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
  value = {
    inherit pathSegments pathString oneLine multiLine renderValue;
  };
  tests = {
    # -- pathSegments / pathString on leaves and chains --
    "pathSegments-leaf" = {
      expr = pathSegments leafErr;
      expected = [];
    };
    "pathString-leaf" = {
      expr = pathString leafErr;
      expected = "";
    };
    "pathSegments-one-hop" = {
      expr = pathSegments (fx.diag.error.nestUnder
                            fx.diag.positions.DArgSort leafErr);
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
                       fx.diag.positions.DArgSort leafErr);
      expected = "[Kernel] type mismatch @ arg.S";
    };
    "oneLine-generic" = {
      expr = oneLine (fx.diag.error.mkGenericError {
        value = 42; msg = "value does not inhabit description";
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
        in builtins.any (l: l == "  path: arg.S") ls;
      expected = true;
    };

    # -- multiLine: Generic leaf --
    "multiLine-generic-has-value" = {
      expr =
        let
          err = fx.diag.error.mkGenericError {
            type = "PersonT"; value = { n = "wrong"; }; msg = "m";
          };
          ls = lib.splitString "\n" (multiLine err);
        in builtins.any (l: l == "  type: PersonT") ls;
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
        in builtins.any (l: l == "  guard: x > 18") ls;
      expected = true;
    };
    "multiLine-hint-rendered" = {
      expr =
        let
          err = fx.diag.error.mkKernelError {
            rule = "desc-arg"; msg = "m"; hint = "try using u 0";
          };
          ls = lib.splitString "\n" (multiLine err);
        in builtins.any (l: l == "  hint: try using u 0") ls;
      expected = true;
    };

    # -- Branching endpoint renders one sub-trace per child --
    "multiLine-branch-renders-each-child" = {
      expr =
        let
          root = fx.diag.error.mkGenericError {
            type = "PersonT"; value = {}; msg = "record validation failed";
          };
          c1 = fx.diag.error.mkGenericError {
            value = "wrong"; msg = "string is not Nat";
          };
          c2 = fx.diag.error.mkGenericError {
            value = 42; msg = "int is not String";
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
        let s = multiLine chain5000;
            ls = lib.splitString "\n" s;
        in builtins.any
             (l: lib.strings.hasPrefix "  path: arg.S -> arg.S" l)
             ls;
      expected = true;
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
      expr = renderValue { tag = "VNat"; };
      expected = "VNat";
    };
    "renderValue-tag-with-field" = {
      expr = renderValue { tag = "VU"; level = 0; };
      expected = "VU(level=0)";
    };
  };
}
