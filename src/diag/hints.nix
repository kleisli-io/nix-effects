# Hint resolver for diagnostic Errors.
#
# Pairs `(leafPosition, detail-pattern)` with a human-readable hint.
# Keys are position-first; no kernel-rule strings appear as keys or
# in hint bodies, so rule retirement never invalidates hint text.
#
# Lookup:
#
#   resolve : Error -> String | null
#
# Walks the single-child chain from the given Error to the leaf,
# recovers the leaf's blame position, and classifies its Detail
# pattern. Looks the (position, pattern) pair up in the table.
# Returns null when no hint is registered or when the Error lacks
# a position (unwrapped leaf).
#
# Chain walking is stack-safe by construction: direct recursion up to
# `fastPathLimit` frames, then a `builtins.genericClosure` worklist
# that WHNF-forces the next Error node at each step. `deepSeq` is
# unsafe on recursive Error payloads; WHNF suffices because each step
# only reads `err.children` (one hop).
{ lib, fx, api, ... }:

let
  inherit (api) mk;

  fastPathLimit = 500;

  # Walk the children[0] chain; return the list of positions from
  # root to leaf (or to the first branching node). Fast-path recursion
  # up to fastPathLimit, then genericClosure.
  chainPositions = err: chainFast [] err 0;

  chainFast = acc: err: depth:
    if builtins.length err.children != 1
    then acc
    else if depth >= fastPathLimit
    then chainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in chainFast (acc ++ [edge.position]) edge.error (depth + 1);

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

  # Reach the endpoint (the first node with !=1 children). Same split.
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

  # Classify a leaf Error's Detail into a short pattern string. The
  # classifier is conservative: it reads only the Detail fields set
  # by mkKernelError / mkGenericError at emission sites. Unrecognised
  # shapes return "type-mismatch" (generic kernel) or "generic".
  tagOf = v: v.tag or null;
  levelOf = v: v.level or null;

  classify = err:
    if err.layer.tag == "Kernel" then classifyKernel err.detail
    else classifyGeneric err.detail;

  classifyKernel = d:
    if tagOf d.expected == "VU"
       && tagOf d.got == "VU"
       && levelOf d.expected != levelOf d.got
    then "universe-mismatch"
    else if tagOf d.expected == "VU" && tagOf d.got != "VU"
    then "not-a-type"
    else if tagOf d.expected == "VDesc" && tagOf d.got != "VDesc"
    then "not-a-desc"
    else if tagOf d.expected == "VPi" && tagOf d.got != "VPi"
    then "not-a-function"
    else if tagOf d.expected == "VSigma" && tagOf d.got != "VSigma"
    then "not-a-pair"
    else "type-mismatch";

  classifyGeneric = d:
    if d.guard != null then "refinement-failed"
    else "inhabitation-failed";

  # Hint table. Keys are "<Position.tag>::<pattern>" strings built
  # from the leaf Position and the Detail-classified pattern.
  # No kernel-rule strings appear; text is position-semantic.
  hints = {
    "DArgSort::universe-mismatch" =
      "the sort position of `arg` lives in U(0); descriptions carry \
      \only small types";
    "DArgBody::not-a-desc" =
      "the body of `arg` must produce a description (Desc I); return \
      \one of descRet / descArg / descRec / descPi / descPlus";
    "DPiSort::universe-mismatch" =
      "the sort position of `pi` lives in U(0)";
    "DPiBody::not-a-desc" =
      "the body of `pi` must produce a description for each input";
    "DRetIndex::type-mismatch" =
      "the index position of `ret` must match the Desc's index type";
    "DRecIndex::type-mismatch" =
      "the index position of `rec` must match the Desc's index type";
    "DRecTail::not-a-desc" =
      "the tail position of `rec` must itself be a description";
    "PiDom::not-a-type" =
      "the domain of Π must be a type (live in some U(k))";
    "PiCod::not-a-type" =
      "the codomain family of Π must be a type for each argument";
    "AnnType::not-a-type" =
      "the annotation position must be a type (live in some U(k))";
    "MuDesc::not-a-desc" =
      "the description argument of μ must be a Desc I term";
    "Scrut::type-mismatch" =
      "the scrutinee's type must match the eliminator's expected shape";
    "Motive::not-a-function" =
      "the motive must be a function from the scrutinee's type into a type";
    "JType::not-a-type" =
      "the type parameter of J must be a type";
  };

  # Entry point. Returns the hint string when the (position, pattern)
  # key is registered, null otherwise.
  resolve = err:
    let
      positions = chainPositions err;
    in
      if positions == [] then null
      else
        let
          leaf = chainEndpoint err;
          leafPos = lib.last positions;
          key = "${leafPos.tag}::${classify leaf}";
        in hints.${key} or null;

  # Build-chain helper for the stack-safety stress test. Matches the
  # pattern used in pretty.nix's tests.
  leafUMismatch = fx.diag.error.mkKernelError {
    rule = "check";
    msg = "type mismatch";
    expected = { tag = "VU"; level = 0; };
    got = { tag = "VU"; level = 1; };
  };

  chain5000 =
    builtins.foldl' (inner: _:
      fx.diag.error.nestUnder fx.diag.positions.DArgSort inner
    ) leafUMismatch (lib.range 1 5000);

in mk {
  doc = ''
    Hint resolver for diagnostic Errors.

    Exports:
      resolve  : Error -> String | null
      classify : Error -> String

    Keys are `(leaf Position, Detail pattern)` pairs encoded as
    `"<pos.tag>::<pattern>"`. Hint text is position-semantic: no
    kernel-rule strings, no source-file references.

    Chain walking recurses directly up to ${toString fastPathLimit}
    frames, then falls through to a `builtins.genericClosure` slow
    path that WHNF-forces the next node.
  '';
  value = {
    inherit resolve classify hints;
  };
  tests = {
    # -- resolve: happy-path hits covering the required ≥7 hints. --
    "resolve-DArgSort-universe-mismatch" = {
      expr = resolve (fx.diag.error.nestUnder
                       fx.diag.positions.DArgSort leafUMismatch);
      expected = hints."DArgSort::universe-mismatch";
    };
    "resolve-DPiSort-universe-mismatch" = {
      expr = resolve (fx.diag.error.nestUnder
                       fx.diag.positions.DPiSort leafUMismatch);
      expected = hints."DPiSort::universe-mismatch";
    };
    "resolve-DArgBody-not-a-desc" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "desc-arg";
              msg = "type mismatch";
              expected = { tag = "VDesc"; };
              got = { tag = "VNat"; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DArgBody leaf);
      expected = hints."DArgBody::not-a-desc";
    };
    "resolve-AnnType-not-a-type" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "ann";
              msg = "expected a type";
              expected = { tag = "VU"; level = 0; };
              got = { tag = "VNat"; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.AnnType leaf);
      expected = hints."AnnType::not-a-type";
    };
    "resolve-PiDom-not-a-type" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "pi-dom";
              msg = "expected a type";
              expected = { tag = "VU"; level = 0; };
              got = { tag = "VBool"; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.PiDom leaf);
      expected = hints."PiDom::not-a-type";
    };
    "resolve-MuDesc-not-a-desc" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "mu";
              msg = "type mismatch";
              expected = { tag = "VDesc"; };
              got = { tag = "VNat"; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.MuDesc leaf);
      expected = hints."MuDesc::not-a-desc";
    };
    "resolve-Motive-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "nat-elim";
              msg = "motive must be Π";
              expected = { tag = "VPi"; };
              got = { tag = "VU"; level = 0; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.Motive leaf);
      expected = hints."Motive::not-a-function";
    };

    # -- resolve: misses return null without error. --
    "resolve-unwrapped-leaf-returns-null" = {
      expr = resolve leafUMismatch;
      expected = null;
    };
    "resolve-unknown-position-returns-null" = {
      expr = resolve (fx.diag.error.nestUnder
                       fx.diag.positions.AppArg leafUMismatch);
      expected = null;
    };

    # -- classify: kernel patterns --
    "classify-universe-mismatch" = {
      expr = classify leafUMismatch;
      expected = "universe-mismatch";
    };
    "classify-not-a-type" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VNat"; };
      });
      expected = "not-a-type";
    };
    "classify-not-a-desc" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "VDesc"; };
        got = { tag = "VNat"; };
      });
      expected = "not-a-desc";
    };
    "classify-not-a-function" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "VPi"; };
        got = { tag = "VU"; level = 0; };
      });
      expected = "not-a-function";
    };
    "classify-not-a-pair" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "VSigma"; };
        got = { tag = "VNat"; };
      });
      expected = "not-a-pair";
    };
    "classify-refinement-failed" = {
      expr = classify (fx.diag.error.mkGenericError {
        value = 17;
        guard = { predicate = "x > 18"; };
        msg = "refinement failed";
      });
      expected = "refinement-failed";
    };
    "classify-inhabitation-failed" = {
      expr = classify (fx.diag.error.mkGenericError {
        value = "bad"; msg = "value does not inhabit description";
      });
      expected = "inhabitation-failed";
    };

    # -- Hint-table discipline: no rule-file substrings anywhere. --
    "hints-table-covers-at-least-seven-entries" = {
      expr = builtins.length (builtins.attrNames hints) >= 7;
      expected = true;
    };
    "hints-keys-have-no-rule-file-substrings" = {
      expr =
        let
          forbidden = [ "infer.nix" "check.nix" "type.nix" "rule" ];
          keys = builtins.attrNames hints;
        in builtins.all
             (k: builtins.all
                   (bad: !(lib.strings.hasInfix bad k)) forbidden)
             keys;
      expected = true;
    };
    "hints-text-references-no-rule-files" = {
      expr =
        let
          forbidden = [
            "infer.nix" "check.nix" "type.nix"
            "check/" "src/"
          ];
          values = builtins.attrValues hints;
        in builtins.all
             (v: builtins.all
                   (bad: !(lib.strings.hasInfix bad v)) forbidden)
             values;
      expected = true;
    };

    # -- Stack-safety stress: resolve on a 5000-deep chain. --
    "resolve-5000-deep-chain" = {
      expr = resolve chain5000;
      expected = hints."DArgSort::universe-mismatch";
    };
  };
}
