# Hint resolver for diagnostic Errors.
#
# Pairs a suffix of the blame path with a Detail-classified pattern
# and maps it to a structured Hint record. Keys are position-first;
# no kernel-rule strings appear as keys or in hint text, so rule
# retirement never invalidates hints.
#
# Lookup:
#
#   resolve : Error -> Hint | null
#
# Walks the single-child chain from the given Error to the leaf,
# classifies the leaf's Detail pattern, and returns the hint
# registered under the *longest* matching leaf-anchored suffix of
# the path's position tags. Returns null when no entry matches or
# when the Error lacks a position (unwrapped leaf).
#
# Key syntax: `"<pos1>.<pos2>...<posN>::<pattern>"`. The N position
# tags must match the last N elements of the blame path, in order.
# Longest matching suffix wins; existing 1-position keys continue to
# work as tail-of-length-1 matches.
#
# A Hint is `{ _tag = "Hint"; text; category; severity; docLink; }`.
# The `_tag` keeps it terminal for `api.extractValue`; all other
# fields are plain data consumable by renderers, LSPs, docs, and
# linters. Severity is `"error"` at this layer. `docLink` points at
# a per-key anchor inside the auto-generated diag module page on
# `docs.kleisli.io`; the anchor slug matches the docs-site markdown
# renderer's slug for the corresponding heading text.
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

  # Page URL of the auto-generated diag module on docs.kleisli.io
  # (served by depots/kleisli/projects/kleisli-docs). Per-key anchors
  # are appended via `slugify` below; the anchor scheme matches the
  # heading-id slugifier in
  # `depots/kleisli/projects/kleisli-content/src/markdown.lisp`, so
  # `docLink` fragment ↔ rendered heading id.
  docBase = "https://docs.kleisli.io/nix-effects/core-api/diag";

  # Slugify a hint key the same way kleisli-content's markdown renderer
  # slugifies heading text: lowercase, then replace any character not in
  # [a-z0-9-] with `-`, then collapse consecutive dashes. We avoid the
  # generic char-loop (slow under Nix) by using a fixed replacement
  # table covering the alphabet that actually appears in Hint keys
  # (alnum plus `:`, `.`, `_`, ` `).
  slugify = text:
    let
      lowered = lib.toLower text;
      replaced = builtins.replaceStrings
        [ "::" ":" "." "_" " " ]
        [ "-"  "-" "-" "-" "-" ]
        lowered;
      collapse = s:
        let s' = builtins.replaceStrings [ "--" ] [ "-" ] s;
        in if s' == s then s else collapse s';
    in collapse replaced;

  # Structured hint constructor. `_tag = "Hint"` stops api.extractValue
  # from recursing into the record (matches the Layer ADT's discipline).
  # `severity` exists so promoting a hint to a warning is an additive
  # override. `docLink` is set to the page root here and overridden
  # per-entry below with the per-key anchor.
  mkHint = category: text: {
    _tag     = "Hint";
    inherit category text;
    severity = "error";
    docLink  = docBase;
  };

  # Category taxonomy. Every hint entry's category must be one of these;
  # the `hints-categories-in-taxonomy` test enforces the closed set.
  taxonomy = [
    "universe"
    "sort"
    "description"
    "arity"
    "indexing"
    "inhabitation"
    "refinement"
    "elimination"
    "type-mismatch"
  ];

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
  #
  # Rules emit `expected` / `got` in one of three shapes:
  #   * kernel values   — tags `VU`, `VPi`, `VSigma`, `VDesc`
  #   * quoted terms    — tags `U`, `pi`, `sigma`, `desc` (after Q.quote)
  #   * literal markers — `{ tag = "U"; }`, `{ tag = "pi"; }` (surface hints)
  # The `isX` predicates accept all three so a single classifier covers
  # every emission path.
  tagOf = v: v.tag or null;
  levelOf = v: v.level or null;

  isU     = v: let t = tagOf v; in t == "VU"     || t == "U";
  isDesc  = v: let t = tagOf v; in t == "VDesc"  || t == "desc";
  isPi    = v: let t = tagOf v; in t == "VPi"    || t == "pi";
  isSigma = v: let t = tagOf v; in t == "VSigma" || t == "sigma";

  classify = err:
    if err.layer.tag == "Kernel" then classifyKernel err.detail
    else classifyGeneric err.detail;

  classifyKernel = d:
    if isU d.expected && isU d.got && levelOf d.expected != levelOf d.got
    then "universe-mismatch"
    else if isU     d.expected && !(isU     d.got) then "not-a-type"
    else if isDesc  d.expected && !(isDesc  d.got) then "not-a-desc"
    else if isPi    d.expected && !(isPi    d.got) then "not-a-function"
    else if isSigma d.expected && !(isSigma d.got) then "not-a-pair"
    else "type-mismatch";

  classifyGeneric = d:
    if d.guard != null then "refinement-failed"
    else "inhabitation-failed";

  # Hint table. Keys are "<Position.tag>::<pattern>" strings built
  # from the leaf Position and the Detail-classified pattern. Values
  # are Hint records (see mkHint). No kernel-rule strings appear in
  # keys or text; text is position-semantic.
  #
  # Each entry's `docLink` is rewritten below to point at the per-key
  # heading anchor on /nix-effects/core-api/diag, computed by `slugify`
  # so the URL fragment matches the heading id emitted by the docs
  # site's markdown renderer.
  hintsByKey = {
    "DArgSort::universe-mismatch" = mkHint "universe"
      "the sort position of `arg` must live in U(0); descriptions only carry small types. Pass `u 0`, or factor the dependency through `descRec` / `descPi` if a larger type is genuinely needed.";
    "DArgBody::not-a-desc" = mkHint "description"
      "the body of `arg` must produce a description (Desc I), not an ordinary value. Build one with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "DPiSort::universe-mismatch" = mkHint "universe"
      "the sort position of `pi` must live in U(0); `descPi` takes a small domain. Use `u 0`, or encode the dependency through an index instead of the Pi domain.";
    "DPiBody::not-a-desc" = mkHint "description"
      "the body of `pi` must produce a description for each input, not a plain term. Return a Desc I via `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "DRetIndex::type-mismatch" = mkHint "indexing"
      "the index position of `ret` must match the Desc's declared index type. Supply a term of that index type, or redefine the enclosing `μ I ...` over the index you actually have.";
    "DRecIndex::type-mismatch" = mkHint "indexing"
      "the index position of `rec` must match the Desc's declared index type. Pass a term of that index type, or adjust the enclosing `μ I ...` to match.";
    "DRecTail::not-a-desc" = mkHint "description"
      "the tail position of `rec` must itself be a description, not an ordinary term. Continue the spine with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "PiDom::not-a-type" = mkHint "sort"
      "the domain of Π must be a type (live in some U(k)), not a term or value. Supply a type expression like `nat`, `bool`, `u 0`, or a user-defined datatype.";
    "PiCod::not-a-type" = mkHint "sort"
      "the codomain family of Π must return a type for each argument, not an ordinary value. Provide a function whose body inhabits some `U k`.";
    "AnnType::not-a-type" = mkHint "sort"
      "the annotation position must be a type (live in some U(k)), not a term. Write a type expression such as `nat`, `bool`, `u 0`, or a user-defined datatype.";
    "MuDesc::not-a-desc" = mkHint "description"
      "the description argument of μ must be a Desc I term, not an ordinary value. Construct it with `descRet`, `descArg`, `descRec`, `descPi`, or `descPlus`.";
    "Scrut::type-mismatch" = mkHint "elimination"
      "the scrutinee's type must match the eliminator's expected shape. Annotate the scrutinee via `ann`, or switch to the eliminator that matches its inferred type.";
    "Motive::not-a-function" = mkHint "arity"
      "the motive must be a function from the scrutinee's type into a type, not a bare type or value. Supply a one-argument function whose body lives in some `U k`.";
    "JType::not-a-type" = mkHint "sort"
      "the type parameter of `J` must be a type (live in some U(k)), not a term. Pass a type expression like `nat`, `u 0`, or the type shared by J's two endpoints.";
    "DPiFn::not-a-function" = mkHint "arity"
      "the index selector `f` of `pi` must be a function `S -> I`";
    "DPiFn::type-mismatch" = mkHint "indexing"
      "the index selector's domain must match the declared sort `S`";
    "DPlusL::not-a-desc" = mkHint "description"
      "the left summand of `plus` must be a description (Desc I)";
    "DPlusR::not-a-desc" = mkHint "description"
      "the right summand of `plus` must be a description at the same index type as the left summand";
    "AnnTerm::type-mismatch" = mkHint "type-mismatch"
      "the annotated term does not match its declared type";
    "AppHead::not-a-function" = mkHint "arity"
      "the head of an application must have a function type (Pi)";
    "AppArg::type-mismatch" = mkHint "type-mismatch"
      "the argument does not match the function's domain";
    "MuIndex::type-mismatch" = mkHint "indexing"
      "the index passed to `con` must have the description's index type";
    "MuPayload::type-mismatch" = mkHint "indexing"
      "the payload of `con` must inhabit the description's interpretation at the given index";
    "OpaqueType::not-a-function" = mkHint "arity"
      "the annotation on an opaque lambda must be a Pi type";
    "OpaqueType::type-mismatch" = mkHint "type-mismatch"
      "the opaque lambda's declared domain does not match the expected domain";
    "Motive::not-a-type" = mkHint "sort"
      "an eliminator's motive must return a type (live in some U(k))";
    "JType::type-mismatch" = mkHint "type-mismatch"
      "the type parameter of `J` must match the type of its two endpoints";
    "Field::inhabitation-failed" = mkHint "inhabitation"
      "the field's value does not inhabit the declared field type";
    "Field::refinement-failed" = mkHint "refinement"
      "the field's value violates the field type's refinement predicate";
    "Elem::inhabitation-failed" = mkHint "inhabitation"
      "the element does not inhabit the list's element type";
    "Elem::refinement-failed" = mkHint "refinement"
      "the element violates the element type's refinement predicate";
    "Tag::inhabitation-failed" = mkHint "inhabitation"
      "the variant's payload does not inhabit the branch type";
    "Tag::refinement-failed" = mkHint "refinement"
      "the variant's payload violates the branch type's refinement predicate";
    "Case::type-mismatch" = mkHint "elimination"
      "this case-body's inferred type does not match the type the eliminator's motive requires";
    "SigmaFst::inhabitation-failed" = mkHint "inhabitation"
      "the first component does not inhabit the declared `fst` type";
    "SigmaSnd::inhabitation-failed" = mkHint "inhabitation"
      "the second component does not inhabit the dependent `snd` type";
    "SigmaFst::refinement-failed" = mkHint "refinement"
      "the first component violates the `fst` type's refinement predicate";
    "SigmaSnd::refinement-failed" = mkHint "refinement"
      "the second component violates the `snd` type's refinement predicate";
    "LevelSucPred::type-mismatch" = mkHint "universe"
      "the predecessor of `suc` must be a Level";
    "LevelMaxLhs::type-mismatch" = mkHint "universe"
      "the left operand of `max` must be a Level";
    "LevelMaxRhs::type-mismatch" = mkHint "universe"
      "the right operand of `max` must be a Level";
    "ULevel::type-mismatch" = mkHint "universe"
      "the level argument of `U` must be a Level";

    # -- Multi-hop entries. Match on a leaf-anchored suffix of the
    # blame path; longest-match wins against the single-position keys.
    "Motive.PiDom::not-a-type" = mkHint "sort"
      "the motive's domain must be a type (live in some U(k)). The motive receives the scrutinee's type as its domain and returns a type; supply a concrete type such as `nat`, `u 0`, or the datatype being eliminated.";
  };

  # Final hint table: rewrite each entry's docLink to point at the
  # per-key anchor on the diag docs page. The anchor slug is computed
  # by the same rule the docs-site markdown renderer uses, so the
  # docLink fragment dereferences to the rendered heading id.
  hints = lib.mapAttrs
    (key: hint: hint // { docLink = "${docBase}#${slugify key}"; })
    hintsByKey;

  # -- Key parsing and indexing (precomputed at module load).
  #
  # Each key decomposes into `(positions, pattern)` where `positions`
  # is the list of position tags parsed from the dot-separated prefix
  # and `pattern` is the classifier suffix after `::`. The index
  # `hintsByPattern` groups keys by pattern with each bucket sorted
  # descending by positions-length so `resolve` iterates candidates
  # longest-first and stops at the first tail-match.
  parseKey = k:
    let
      parts = lib.splitString "::" k;
      pattern = builtins.elemAt parts 1;
      posSpec = builtins.elemAt parts 0;
      positions = lib.splitString "." posSpec;
    in {
      inherit positions pattern;
      length = builtins.length positions;
      key = k;
    };

  parsedKeys = map parseKey (builtins.attrNames hints);

  hintsByPattern =
    let
      grouped = lib.groupBy (m: m.pattern) parsedKeys;
      sortDesc = ms: lib.sort (a: b: a.length > b.length) ms;
    in lib.mapAttrs (_: sortDesc) grouped;

  # Entry point. Returns the Hint record registered under the longest
  # leaf-anchored suffix of the blame path that classifies matches,
  # or null when no entry matches.
  resolve = err:
    let
      positions = chainPositions err;
      n = builtins.length positions;
    in
      if n == 0 then null
      else
        let
          leaf = chainEndpoint err;
          pattern = classify leaf;
          candidates = hintsByPattern.${pattern} or [];
          # Lazy suffix: materialise only k tags on demand. For the
          # 5000-deep bench workload with 1-position candidates this
          # allocates a single-element list after one elemAt.
          tailTags = k:
            builtins.genList
              (i: (builtins.elemAt positions (n - k + i)).tag) k;
          firstMatch = ms:
            if ms == [] then null
            else
              let m = builtins.head ms;
              in if m.length <= n && tailTags m.length == m.positions
                 then hints.${m.key}
                 else firstMatch (builtins.tail ms);
        in firstMatch candidates;

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
      resolve  : Error -> Hint | null
      classify : Error -> String
      hints    : { <key> = Hint; }

    A Hint is `{ _tag = "Hint"; text; category; severity; docLink; }`.
    The `_tag` marker keeps it terminal for `api.extractValue`, and
    the remaining fields are plain data consumable by renderers,
    LSPs, docs, and linters. Severity is `"error"` at this layer;
    `docLink` points at the per-key heading anchor on the
    auto-generated diag module page (`/nix-effects/core-api/diag`).
    The anchor slug matches the docs-site markdown renderer's
    heading-id slugification rule, so each hint's docLink lands
    precisely on the rendered section for its key.

    Keys encode a leaf-anchored suffix of the blame path plus the
    classifier pattern: `"<pos1>.<pos2>...<posN>::<pattern>"`. A key
    matches when its positions equal the last N tags of the blame
    path; `resolve` returns the hint under the longest matching
    suffix. Single-position keys are the 1-hop special case. Hint
    text is position-semantic: no kernel-rule strings, no source-file
    references.

    Chain walking recurses directly up to ${toString fastPathLimit}
    frames, then falls through to a `builtins.genericClosure` slow
    path that WHNF-forces the next node.
  '';
  value = {
    inherit resolve classify hints mkHint taxonomy;
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
              got = { tag = "VUnit"; };
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
              got = { tag = "VUnit"; };
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
              got = { tag = "VUnit"; };
            };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.MuDesc leaf);
      expected = hints."MuDesc::not-a-desc";
    };
    "resolve-Motive-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
              rule = "elim";
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
        got = { tag = "VUnit"; };
      });
      expected = "not-a-type";
    };
    "classify-not-a-desc" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "VDesc"; };
        got = { tag = "VUnit"; };
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
        got = { tag = "VUnit"; };
      });
      expected = "not-a-pair";
    };
    # Term-shape emissions (from Q.quote) must classify identically to
    # value-shape emissions so real kernel errors surface hints.
    "classify-term-shape-universe-mismatch" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "U"; level = 0; };
        got      = { tag = "U"; level = 3; };
      });
      expected = "universe-mismatch";
    };
    "classify-term-shape-not-a-type" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "U"; level = 0; };
        got      = { tag = "nat"; };
      });
      expected = "not-a-type";
    };
    "classify-term-shape-not-a-desc" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "desc"; };
        got      = { tag = "nat"; };
      });
      expected = "not-a-desc";
    };
    "classify-term-shape-not-a-function" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "pi"; };
        got      = { tag = "U"; level = 0; };
      });
      expected = "not-a-function";
    };
    "classify-term-shape-not-a-pair" = {
      expr = classify (fx.diag.error.mkKernelError {
        rule = "r"; msg = "m";
        expected = { tag = "sigma"; };
        got      = { tag = "nat"; };
      });
      expected = "not-a-pair";
    };
    "resolve-term-shape-DArgSort-universe" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "check"; msg = "type mismatch";
          expected = { tag = "U"; level = 0; };
          got      = { tag = "U"; level = 2; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DArgSort leaf);
      expected = hints."DArgSort::universe-mismatch";
    };
    "resolve-term-shape-PiDom-not-a-type" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "checkType"; msg = "expected a type";
          expected = { tag = "U"; level = 0; };
          got      = { tag = "nat"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.PiDom leaf);
      expected = hints."PiDom::not-a-type";
    };
    "resolve-term-shape-Motive-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "elim"; msg = "motive must be Π";
          expected = { tag = "pi"; };
          got      = { tag = "U"; level = 0; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.Motive leaf);
      expected = hints."Motive::not-a-function";
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
                   (bad: !(lib.strings.hasInfix bad v.text)) forbidden)
             values;
      expected = true;
    };

    # -- Schema discipline: every entry is a Hint record. --
    "hints-every-entry-has-Hint-schema" = {
      expr =
        let
          values = builtins.attrValues hints;
          wellFormed = v:
            builtins.isAttrs v
            && (v._tag or null) == "Hint"
            && builtins.isString (v.text or null)
            && builtins.isString (v.category or null)
            && builtins.isString (v.severity or null)
            && builtins.isString (v.docLink or null);
        in builtins.all wellFormed values;
      expected = true;
    };

    # -- Taxonomy discipline: every category is a taxonomy member. --
    "hints-categories-in-taxonomy" = {
      expr =
        let
          values = builtins.attrValues hints;
          allowed = cat: builtins.elem cat taxonomy;
        in builtins.all (v: allowed v.category) values;
      expected = true;
    };

    # -- Doc-link discipline: every entry points at the docs site. --
    "hints-docLinks-resolve-to-kleisli-docs" = {
      expr =
        let values = builtins.attrValues hints;
        in builtins.all
             (v: lib.strings.hasPrefix "https://docs.kleisli.io/" v.docLink)
             values;
      expected = true;
    };

    # -- Anchor coherence: every docLink decomposes as `${docBase}#${slugify key}`. --
    "hints-docLinks-have-matching-per-key-anchor" = {
      expr =
        let
          check = key: hint:
            let
              parts = lib.splitString "#" hint.docLink;
              base = builtins.elemAt parts 0;
              fragment =
                if builtins.length parts > 1
                then builtins.elemAt parts 1
                else "";
            in base == docBase && fragment == slugify key;
        in builtins.all
             (key: check key hints.${key})
             (builtins.attrNames hints);
      expected = true;
    };

    # -- Key syntax: every key parses to a non-empty positions list
    # with non-empty position tags. Guards against accidental empty
    # prefixes (e.g. `"::pat"`) or double-dots (`"A..B::pat"`).
    "hints-keys-parse-nonempty-positions" = {
      expr = builtins.all
        (m: m.length >= 1
            && builtins.all (p: p != "") m.positions)
        parsedKeys;
      expected = true;
    };

    # -- Stack-safety stress: resolve on a 5000-deep chain. --
    "resolve-5000-deep-chain" = {
      expr = resolve chain5000;
      expected = hints."DArgSort::universe-mismatch";
    };

    # -- Multi-hop resolve: longest suffix wins over the 1-hop leaf. --
    "resolve-multi-hop-Motive-PiDom-wins-over-PiDom" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType"; msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
          chain = fx.diag.error.nestUnder fx.diag.positions.Motive
                    (fx.diag.error.nestUnder fx.diag.positions.PiDom leaf);
        in resolve chain;
      expected = hints."Motive.PiDom::not-a-type";
    };
    "resolve-multi-hop-falls-back-to-leaf-PiDom" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType"; msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.PiDom leaf);
      expected = hints."PiDom::not-a-type";
    };
    # A 3-hop chain whose outer positions have no multi-hop entry must
    # still resolve via the longest matching suffix — here the 2-hop
    # `Motive.PiDom::not-a-type`. Any 3-hop prefix key would win over it
    # if registered; absent that, the 2-hop key is the longest match.
    "resolve-multi-hop-3-hop-longest-suffix-wins" = {
      expr =
        let
          leaf = fx.diag.error.mkKernelError {
            rule = "checkType"; msg = "expected a type";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VUnit"; };
          };
          chain =
            fx.diag.error.nestUnder fx.diag.positions.AppArg
              (fx.diag.error.nestUnder fx.diag.positions.Motive
                (fx.diag.error.nestUnder fx.diag.positions.PiDom leaf));
        in resolve chain;
      expected = hints."Motive.PiDom::not-a-type";
    };

    # -- resolve: Kernel-layer positions. --
    "resolve-DPiFn-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-pi"; msg = "f must have type S -> I";
          expected = { tag = "VPi"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DPiFn leaf);
      expected = hints."DPiFn::not-a-function";
    };
    "resolve-DPiFn-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-pi"; msg = "domain mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DPiFn leaf);
      expected = hints."DPiFn::type-mismatch";
    };
    "resolve-DPlusL-not-a-desc" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-plus"; msg = "A must be Desc";
          expected = { tag = "VDesc"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DPlusL leaf);
      expected = hints."DPlusL::not-a-desc";
    };
    "resolve-DPlusR-not-a-desc" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-plus"; msg = "B must be Desc";
          expected = { tag = "VDesc"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.DPlusR leaf);
      expected = hints."DPlusR::not-a-desc";
    };
    "resolve-AnnTerm-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "ann"; msg = "term does not match annotation";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.AnnTerm leaf);
      expected = hints."AnnTerm::type-mismatch";
    };
    "resolve-AppHead-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "app"; msg = "expected function type";
          expected = { tag = "VPi"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.AppHead leaf);
      expected = hints."AppHead::not-a-function";
    };
    "resolve-AppArg-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "app"; msg = "arg mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.AppArg leaf);
      expected = hints."AppArg::type-mismatch";
    };
    "resolve-MuIndex-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-con"; msg = "target index mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.MuIndex leaf);
      expected = hints."MuIndex::type-mismatch";
    };
    "resolve-MuPayload-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "desc-con"; msg = "payload mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.MuPayload leaf);
      expected = hints."MuPayload::type-mismatch";
    };
    "resolve-OpaqueType-not-a-function" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "opaque-lam"; msg = "annotation must be Pi";
          expected = { tag = "VPi"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.OpaqueType leaf);
      expected = hints."OpaqueType::not-a-function";
    };
    "resolve-OpaqueType-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "opaque-lam"; msg = "domain mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.OpaqueType leaf);
      expected = hints."OpaqueType::type-mismatch";
    };
    "resolve-Motive-not-a-type" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "checkMotive"; msg = "motive must return a type";
          expected = { tag = "VU"; level = 0; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.Motive leaf);
      expected = hints."Motive::not-a-type";
    };
    "resolve-JType-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "j"; msg = "type mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.JType leaf);
      expected = hints."JType::type-mismatch";
    };

    # -- resolve: Generic-layer positions and eliminator case-bodies. --
    "resolve-Field-inhabitation-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = 42; msg = "field is not a String";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Field "name") leaf);
      expected = hints."Field::inhabitation-failed";
    };
    "resolve-Field-refinement-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = 17;
          guard = { predicate = "x > 18"; };
          msg = "refinement failed";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Field "age") leaf);
      expected = hints."Field::refinement-failed";
    };
    "resolve-Elem-inhabitation-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = "bad"; msg = "element is not an Int";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Elem 3) leaf);
      expected = hints."Elem::inhabitation-failed";
    };
    "resolve-Elem-refinement-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = (-5);
          guard = { predicate = "x >= 0"; };
          msg = "refinement failed";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Elem 0) leaf);
      expected = hints."Elem::refinement-failed";
    };
    "resolve-Tag-inhabitation-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = 42; msg = "payload does not inhabit branch type";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Tag "Some") leaf);
      expected = hints."Tag::inhabitation-failed";
    };
    "resolve-Tag-refinement-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = 3;
          guard = { predicate = "x > 10"; };
          msg = "refinement failed";
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Tag "Big") leaf);
      expected = hints."Tag::refinement-failed";
    };
    "resolve-Case-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "elim"; msg = "case body mismatch";
          expected = { tag = "VUnit"; };
          got      = { tag = "VString"; };
        };
        in resolve (fx.diag.error.nestUnder
                     (fx.diag.positions.Case "succ") leaf);
      expected = hints."Case::type-mismatch";
    };
    "resolve-SigmaFst-inhabitation-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = "bad"; msg = "fst does not inhabit";
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.SigmaFst leaf);
      expected = hints."SigmaFst::inhabitation-failed";
    };
    "resolve-SigmaSnd-inhabitation-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = "bad"; msg = "snd does not inhabit";
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.SigmaSnd leaf);
      expected = hints."SigmaSnd::inhabitation-failed";
    };
    "resolve-SigmaFst-refinement-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = (-1);
          guard = { predicate = "x >= 0"; };
          msg = "refinement";
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.SigmaFst leaf);
      expected = hints."SigmaFst::refinement-failed";
    };
    "resolve-SigmaSnd-refinement-failed" = {
      expr =
        let leaf = fx.diag.error.mkGenericError {
          value = (-1);
          guard = { predicate = "x >= 0"; };
          msg = "refinement";
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.SigmaSnd leaf);
      expected = hints."SigmaSnd::refinement-failed";
    };

    # -- resolve: Level-sort positions. --
    "resolve-LevelSucPred-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "level-suc"; msg = "pred must be Level";
          expected = { tag = "VLevel"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.LevelSucPred leaf);
      expected = hints."LevelSucPred::type-mismatch";
    };
    "resolve-LevelMaxLhs-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "level-max"; msg = "lhs must be Level";
          expected = { tag = "VLevel"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.LevelMaxLhs leaf);
      expected = hints."LevelMaxLhs::type-mismatch";
    };
    "resolve-LevelMaxRhs-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "level-max"; msg = "rhs must be Level";
          expected = { tag = "VLevel"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.LevelMaxRhs leaf);
      expected = hints."LevelMaxRhs::type-mismatch";
    };
    "resolve-ULevel-type-mismatch" = {
      expr =
        let leaf = fx.diag.error.mkKernelError {
          rule = "U"; msg = "level argument must be Level";
          expected = { tag = "VLevel"; };
          got      = { tag = "VUnit"; };
        };
        in resolve (fx.diag.error.nestUnder
                     fx.diag.positions.ULevel leaf);
      expected = hints."ULevel::type-mismatch";
    };
  };
}
