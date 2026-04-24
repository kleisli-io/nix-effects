# SourceMap: parallel structure threaded alongside elaborated Tms.
#
# A SourceMap mirrors the shape of an elaborated Tm, carrying at each
# node an opaque HOAS-origin reference plus a map from `Position` keys
# to child SourceMaps. Its sole purpose is back-mapping: given an error
# raised by the kernel during `check`/`infer` — whose blame is expressed
# as a chain of `Position`s threaded through `Error.children` by
# `bindP` — resolve that chain to the HOAS surface node that produced
# the offending sub-Tm.
#
# The structure is deliberately minimal:
#
#   SourceMap = {
#     _tag = "SourceMap";
#     hoas : Any | null;                 # HOAS-origin reference (opaque)
#     subs : AttrSet SourceMap;          # keyed by positionKey(Position)
#   }
#
# `hoas` is opaque to this module — the elaborator chooses what to
# stash (typically a HOAS tree node). `subs` is keyed by a string
# derived from `Position` so that descents are attrset lookups, not
# linear scans. The alphabet of keys is exactly what
# `src/diag/positions.nix` produces via `positionKey`.
#
# Chain walking over an Error's children uses the same fast/slow split
# as `src/diag/pretty.nix` — direct recursion up to `fastPathLimit`,
# `builtins.genericClosure` beyond. The slow path's `key` depends on
# a WHNF force of the next Error so cross-step references resolve
# without rebuilding the chain at result-force time.
{ lib, fx, ... }:

let
  fastPathLimit = 500;

  # Serialise a Position to an attrset key. Nullary positions use their
  # tag directly; parameterised positions suffix the parameter. The
  # function is injective over the alphabet in `src/diag/positions.nix`
  # because the tag namespace is disjoint from parameter-value syntax.
  positionKey = pos:
    if pos.tag == "Field"    then "Field:${pos.name}"
    else if pos.tag == "Elem" then "Elem:${toString pos.idx}"
    else if pos.tag == "Tag"  then "Tag:${pos.name}"
    else if pos.tag == "Case" then "Case:${pos.name}"
    else pos.tag;

  mkNode = hoas: subs:
    { _tag = "SourceMap"; inherit hoas subs; };

  leaf    = hoas: mkNode hoas {};
  node    = hoas: subs: mkNode hoas subs;
  opaque  = mkNode null {};

  isSourceMap = x:
    builtins.isAttrs x
    && (x._tag or null) == "SourceMap"
    && x ? hoas && x ? subs;

  # Single-hop descent. Returns null when the sub-map is absent.
  descend = pos: sm:
    let k = positionKey pos; in
    if sm.subs ? ${k} then sm.subs.${k} else null;

  # Multi-hop descent along a Position chain. Null-propagates: any
  # missing hop yields null.
  descendChain = positions: sm0:
    builtins.foldl'
      (sm: pos: if sm == null then null else descend pos sm)
      sm0
      positions;

  # Hoas origin at the end of a Position chain, or null on miss.
  hoasAt = positions: sm:
    let t = descendChain positions sm; in
    if t == null then null else t.hoas;

  # Walk an Error's single-child chain, collecting `children[].position`
  # from root to first leaf or branching node. Stops when
  # `children` is empty (leaf) or has length != 1 (branching).
  chainPositions = err: chainFast [] err 0;

  chainFast = acc: err: depth:
    if builtins.length err.children != 1
    then acc
    else if depth >= fastPathLimit
    then chainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in chainFast (acc ++ [edge.position]) edge.error (depth + 1);

  # Slow path: genericClosure worklist. `key` forces WHNF of `nextErr`
  # and `newAcc` so the chain does not rebuild thunks at result time.
  # `deepSeq` would cascade through the remaining descendants held by
  # `children` and overflow.
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

  # Back-map an Error's blame to a HOAS origin through a SourceMap.
  # Null if the chain leaves the mapped sub-tree.
  hoasAtError = err: sm: hoasAt (chainPositions err) sm;

in {
  scope = {
    sourceMap = {
      inherit
        leaf node opaque
        positionKey descend descendChain hoasAt
        chainPositions hoasAtError
        isSourceMap;
    };
  };
  tests =
    let
      P = fx.diag.positions;
      D = fx.diag.error;

      # Sample SourceMap: desc-arg at the root with sort/body children,
      # each a leaf carrying a distinctive hoas tag for identification.
      smDescArg = node "outer" {
        "DArgSort" = leaf "sort-hoas";
        "DArgBody" = leaf "body-hoas";
      };

      # Deep nested SourceMap: PiDom -> DArgSort -> leaf.
      smNested = node "root" {
        "PiDom" = node "dom" {
          "DArgSort" = leaf "sort-at-dom";
        };
        "PiCod" = leaf "cod-hoas";
      };

      # Parameterised-position SourceMap: Field "age" and Elem 2.
      smParams = node "record" {
        "Field:age" = leaf "age-hoas";
        "Field:name" = leaf "name-hoas";
        "Elem:2" = leaf "elem2-hoas";
        "Tag:Some" = leaf "tag-some-hoas";
        "Case:zero" = leaf "case-zero-hoas";
      };

      # Kernel error with a two-hop chain matching smNested's descent
      # order: outermost bindP fires last, so wrapping inner-first
      # yields chain [PiDom, DArgSort] when walking children[0].
      leafErr = D.mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      };
      nested2 = D.nestUnder P.DArgSort leafErr;
      nested3 = D.nestUnder P.PiDom nested2;

      # 5000-deep stress chain for stack-safety.
      deepErr =
        builtins.foldl' (err: _: D.nestUnder P.DArgSort err)
          leafErr
          (lib.range 1 5000);
    in {
      # -- positionKey --
      "positionKey-DArgSort" = {
        expr = positionKey P.DArgSort;
        expected = "DArgSort";
      };
      "positionKey-PiDom" = {
        expr = positionKey P.PiDom;
        expected = "PiDom";
      };
      "positionKey-Field" = {
        expr = positionKey (P.Field "age");
        expected = "Field:age";
      };
      "positionKey-Elem" = {
        expr = positionKey (P.Elem 3);
        expected = "Elem:3";
      };
      "positionKey-Tag" = {
        expr = positionKey (P.Tag "Some");
        expected = "Tag:Some";
      };
      "positionKey-Case" = {
        expr = positionKey (P.Case "zero");
        expected = "Case:zero";
      };

      # -- Constructors / predicate --
      "leaf-is-sourceMap" = {
        expr = isSourceMap (leaf "x");
        expected = true;
      };
      "node-is-sourceMap" = {
        expr = isSourceMap (node "x" {});
        expected = true;
      };
      "opaque-is-sourceMap" = {
        expr = isSourceMap opaque;
        expected = true;
      };
      "plain-attrset-is-not-sourceMap" = {
        expr = isSourceMap { hoas = "x"; subs = {}; };
        expected = false;
      };
      "leaf-has-empty-subs" = {
        expr = (leaf "x").subs;
        expected = {};
      };
      "leaf-carries-hoas" = {
        expr = (leaf "some-hoas").hoas;
        expected = "some-hoas";
      };
      "opaque-has-null-hoas" = {
        expr = opaque.hoas;
        expected = null;
      };
      "node-carries-hoas-and-subs" = {
        expr =
          let sm = node "h" { "DArgSort" = leaf "c"; };
          in { h = sm.hoas; ck = sm.subs ? "DArgSort"; };
        expected = { h = "h"; ck = true; };
      };

      # -- descend --
      "descend-existing-child" = {
        expr = (descend P.DArgSort smDescArg).hoas;
        expected = "sort-hoas";
      };
      "descend-missing-child-is-null" = {
        expr = descend P.PiDom smDescArg;
        expected = null;
      };
      "descend-parameterised-Field" = {
        expr = (descend (P.Field "age") smParams).hoas;
        expected = "age-hoas";
      };
      "descend-parameterised-Elem" = {
        expr = (descend (P.Elem 2) smParams).hoas;
        expected = "elem2-hoas";
      };
      "descend-parameterised-Tag" = {
        expr = (descend (P.Tag "Some") smParams).hoas;
        expected = "tag-some-hoas";
      };
      "descend-parameterised-Case" = {
        expr = (descend (P.Case "zero") smParams).hoas;
        expected = "case-zero-hoas";
      };
      "descend-wrong-param-is-null" = {
        expr = descend (P.Field "missing") smParams;
        expected = null;
      };

      # -- descendChain --
      "descendChain-empty-is-identity" = {
        expr = (descendChain [] smDescArg).hoas;
        expected = "outer";
      };
      "descendChain-single-hop" = {
        expr = (descendChain [ P.DArgSort ] smDescArg).hoas;
        expected = "sort-hoas";
      };
      "descendChain-multi-hop" = {
        expr = (descendChain [ P.PiDom P.DArgSort ] smNested).hoas;
        expected = "sort-at-dom";
      };
      "descendChain-missing-step-is-null" = {
        expr = descendChain [ P.PiDom P.PiCod ] smNested;
        expected = null;
      };
      "descendChain-miss-at-leaf-is-null" = {
        expr = descendChain [ P.DArgSort P.PiDom ] smDescArg;
        expected = null;
      };

      # -- hoasAt --
      "hoasAt-root" = {
        expr = hoasAt [] smNested;
        expected = "root";
      };
      "hoasAt-deep" = {
        expr = hoasAt [ P.PiDom P.DArgSort ] smNested;
        expected = "sort-at-dom";
      };
      "hoasAt-missing-is-null" = {
        expr = hoasAt [ P.PiDom P.PiCod ] smNested;
        expected = null;
      };

      # -- chainPositions --
      "chainPositions-leaf-error-is-empty" = {
        expr = chainPositions leafErr;
        expected = [];
      };
      "chainPositions-one-hop" = {
        expr = map (p: p.tag) (chainPositions nested2);
        expected = [ "DArgSort" ];
      };
      "chainPositions-two-hops" = {
        expr = map (p: p.tag) (chainPositions nested3);
        expected = [ "PiDom" "DArgSort" ];
      };
      "chainPositions-stops-at-branching" = {
        expr =
          let branched = D.addChild P.PiCod nested2 leafErr;
          in map (p: p.tag) (chainPositions branched);
        expected = [];
      };

      # -- hoasAtError --
      "hoasAtError-root-on-leaf-error" = {
        expr = hoasAtError leafErr smNested;
        expected = "root";
      };
      "hoasAtError-nested-resolves" = {
        expr = hoasAtError nested3 smNested;
        expected = "sort-at-dom";
      };
      "hoasAtError-missing-is-null" = {
        expr = hoasAtError (D.nestUnder P.SigmaFst leafErr) smNested;
        expected = null;
      };

      # -- Stack safety on a 5000-deep chain --
      "chainPositions-5000-deep-length" = {
        expr = builtins.length (chainPositions deepErr);
        expected = 5000;
      };
      "chainPositions-5000-deep-leaf-tag" = {
        expr =
          let positions = chainPositions deepErr;
          in (builtins.elemAt positions 4999).tag;
        expected = "DArgSort";
      };
    };
}
