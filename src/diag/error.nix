# Error: the diagnostic ADT.
#
# An Error carries:
#   - layer    : Layer        (Kernel | Generic | Contract)
#   - detail   : Detail       (Σ-type: Layer × DetailFor(Layer))
#   - msg      : String       (short human-readable summary)
#   - hint     : Hint | null  (resolved later by hints.nix;
#                               Hint = { _tag = "Hint"; text;
#                                        category; severity; docLink; })
#   - children : [{ position : Position; error : Error }]
#
# A leaf is an Error with `children = []`. A non-empty children list marks
# a descent frame (one child) or a collection of sibling failures (many).
# The absolute blame path is the root-to-leaf sequence of children[].position,
# reconstructed at rendering time; the path is the tree shape, never stored
# duplicatedly.
#
# Layer ADT (proper sum type):
#   Kernel   — a term the type-checker rejected during check/infer.
#   Generic  — a value whose shape fails to inhabit a description.
#   Contract — a value with the correct shape that violates a refinement
#              predicate (guard).
#
# Detail ADT (Σ-type: Layer × DetailFor(Layer)):
#   KernelDetail   { rule, expected, got, ctx_depth, term, frame, trace }
#   GenericDetail  { type, desc, value, context, index, guard? }
#   ContractDetail { type, value, guard, context }
#
# Each Detail record carries `_tag = "Detail"` (terminal for
# api.extractValue / extractTests) and `layer = "<Kernel|Generic|Contract>"`
# as a self-discriminator agreeing with the enclosing Error's `layer.tag`.
#
# KernelDetail provenance fields:
#   - `term`  : `{ tag, quoted? } | null` — failing surface-term shape.
#   - `frame` : `{ depth, env, types, names } | null` — Ctx snapshot
#                via `captureFrame ctx`.
#   - `trace` : `[{ rule, position }]` — descent chain auto-appended
#                by `bindP`/`bindPR`, innermost-first.
#
# `ctx_depth` is a fast-read shadow of `frame.depth`.
#
# `GenericDetail.guard` lets refinement-failure producers that still
# emit Generic populate it; the renderer treats `guard != null` as a
# contract-violation regardless of layer.
#
# This module is pure data. No effects; combinators build attrsets. The
# kernel consumes `Position` constants and pure combinators from here
# (via fx.diag); this module itself depends only on `api` and the sibling
# positions module.
{ lib, fx, api, ... }:
let
  inherit (fx.diag.positions) DArgSort DArgBody Field Elem;

  # Stack-safety switchover point for chain-walking combinators. Direct
  # recursion up to this depth, then a genericClosure worklist that
  # WHNF-forces the next node. Matches pretty.nix / hints.nix.
  fastPathLimit = 500;

  # -- Layer ADT constants.
  # Tagged attrsets with `_tag = "Layer"` mark these as terminal values
  # (not traversed by api.extractValue/extractTests).
  Kernel = { _tag = "Layer"; tag = "Kernel"; };
  Generic = { _tag = "Layer"; tag = "Generic"; };
  Contract = { _tag = "Layer"; tag = "Contract"; };

  # -- Per-layer empty Detail records. Each is a Σ-type witness: the
  # `layer` field is the discriminator (must agree with the enclosing
  # Error's `layer.tag`); `_tag = "Detail"` makes the record terminal so
  # api.extractValue / extractTests does not recurse into the field
  # values (defensive against future fields that may be attrsets with
  # `expr` / `expected` keys by accident).
  emptyKernelDetail = {
    _tag = "Detail";
    layer = "Kernel";
    rule = null;
    expected = null;
    got = null;
    ctx_depth = null;
    term = null;
    frame = null;
    trace = [ ];
  };
  emptyGenericDetail = {
    _tag = "Detail";
    layer = "Generic";
    type = null;
    desc = null;
    value = null;
    context = null;
    index = null;
    # Slot for refinement-failure producers that still emit Generic
    # rather than Contract. Renderer dispatches on `guard != null`.
    guard = null;
  };
  emptyContractDetail = {
    _tag = "Detail";
    layer = "Contract";
    type = null;
    value = null;
    guard = null;
    context = null;
  };

  mkKernelDetail = overrides: emptyKernelDetail // overrides;
  mkGenericDetail = overrides: emptyGenericDetail // overrides;
  mkContractDetail = overrides: emptyContractDetail // overrides;

  # -- Internal: build a leaf Error. children = [].
  mkLeaf = { layer, detail, msg, hint ? null }:
    {
      _tag = "Error";
      inherit layer detail msg hint;
      children = [ ];
    };

  # -- mkKernelError: a Kernel-layer leaf. `position`, when supplied, is
  # added as an outer hop via nestUnder so the rule can declare its own
  # descent coordinate at the emission site.
  mkKernelError =
    { position ? null
    , rule
    , msg
    , expected ? null
    , got ? null
    , ctx_depth ? null
    , term ? null
    , frame ? null
    , trace ? [ ]
    , hint ? null
    ,
    }:
    let
      leaf = mkLeaf {
        layer = Kernel;
        detail = mkKernelDetail {
          inherit rule expected got ctx_depth term frame trace;
        };
        inherit msg hint;
      };
    in
    if position == null then leaf
    else nestUnder position leaf;

  # -- captureFrame: project a Ctx into a `{ depth, env, types, names }`
  # record. `ctx.names` is read defensively for Ctx values without
  # name tracking.
  captureFrame = ctx:
    let
      # Materialise a de Bruijn spine (env-style cons cells, or a plain Nix
      # list from elaborate-layer contexts) into an index-ordered list for
      # display. Iterative (genericClosure) so deep contexts stay
      # host-stack-flat; tolerates a null- or list-terminated spine.
      spineList = e:
        if builtins.isList e then e
        else if e == null then [ ]
        else
          let
            cells = builtins.genericClosure {
              startSet = [ { key = 0; cur = e; } ];
              operator = s:
                if builtins.isAttrs s.cur.tail
                then [ { key = s.key + 1; cur = s.cur.tail; } ]
                else [ ];
            };
            last = (builtins.elemAt cells (builtins.length cells - 1)).cur.tail;
            tailList = if builtins.isList last then last else [ ];
          in
          map (s: s.cur.head) cells ++ tailList;
    in
    {
      inherit (ctx) depth env;
      types = spineList ctx.types;
      names = spineList (ctx.names or [ ]);
    };

  # -- appendTrace: append a `{ rule, position }` entry to a
  # Kernel-layer error's `detail.trace`; non-Kernel errors pass through.
  #
  # Built by explicit field-by-field reconstruction rather than
  # `err // { detail = err.detail // {...}; }`. The `//` operator is
  # forced on every `.msg` lookup through the slow-path chain
  # (`nestUnder` inherits `msg` from the appendTrace result), and on a
  # 5000-deep slow path each `//` compounds into the dominant alloc
  # blame (`opUpdates`). Attribute-set literal construction avoids the
  # `//` entirely. Schema coupling to `mkLeaf` / `emptyKernelDetail` is
  # acceptable because both shapes are closed records local to this
  # module.
  appendTrace = rule: position: err:
    if err.layer.tag != "Kernel"
    then err
    else
      let
        d = err.detail;
        entry = { inherit rule position; };
      in
      {
        inherit (err) _tag layer msg hint children;
        detail = {
          inherit (d) _tag layer rule expected got ctx_depth term frame;
          trace = (d.trace or [ ]) ++ [ entry ];
        };
      };

  # -- mkGenericError: a Generic-layer leaf. `value` is the thing that
  # failed to inhabit the description (or the applicable sugar type).
  mkGenericError =
    { type ? null
    , context ? null
    , value
    , desc ? null
    , index ? null
    , guard ? null
    , msg
    , hint ? null
    ,
    }:
    mkLeaf {
      layer = Generic;
      detail = mkGenericDetail { inherit type context value desc index guard; };
      inherit msg hint;
    };

  # -- mkContractError: a Contract-layer leaf. `value` has the correct
  # shape but the refinement `guard` rejected it. `guard` is mandatory
  # here; without it the failure belongs in Generic.
  mkContractError =
    { type ? null
    , context ? null
    , value
    , guard
    , msg
    , hint ? null
    ,
    }:
    mkLeaf {
      layer = Contract;
      detail = mkContractDetail { inherit type context value guard; };
      inherit msg hint;
    };

  # -- nestUnder: add a positional hop above an existing Error. The wrapper
  # inherits the inner's layer/detail/msg/hint (pass-through) so renderer
  # dispatch and leaf-content rendering work at any depth of the chain;
  # the blame path is encoded in the children edges.
  nestUnder = position: inner:
    {
      _tag = "Error";
      inherit (inner) layer detail msg hint;
      children = [{ inherit position; error = inner; }];
    };

  # -- addChild: append a keyed child Error to a branching root. Used by
  # collecting handlers that gather multiple sibling failures under one
  # root. Original children are preserved; the new child is appended.
  addChild = position: parent: child:
    parent // {
      children = parent.children ++ [{ inherit position; error = child; }];
    };

  # -- setLeafHint: walk the single-child chain to the leaf and
  # overwrite its `hint` field. Returns a structurally-equivalent tree
  # with all path edges preserved. If the chain endpoint is a
  # branching node (children count > 1), returns the tree unchanged —
  # sibling-specific hint attachment is the caller's responsibility.
  #
  # Stack-safe: direct recursion up to fastPathLimit frames, then a
  # genericClosure worklist that WHNF-forces the next node. Required
  # because checkHoas feeds error trees up to the full kernel descent
  # depth into this function.
  #
  # Implementation: (1) walk to the endpoint, collecting positions;
  # (2) rebuild the chain by folding nestUnder over the positions in
  # reverse. Step (2) is O(n) attrset allocation and uses no recursion.
  splitChainFast = acc: err: depth:
    if builtins.length err.children != 1
    then { positions = acc; endpoint = err; }
    else if depth >= fastPathLimit
    then splitChainSlow acc err
    else
      let edge = builtins.elemAt err.children 0;
      in splitChainFast (acc ++ [ edge.position ]) edge.error (depth + 1);

  splitChainSlow = acc0: err0:
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
      final = lib.last steps;
    in
    { positions = final._acc; endpoint = final._err; };

  setLeafHint = hint: err:
    let
      split = splitChainFast [ ] err 0;
      endpoint = split.endpoint;
      newLeaf =
        if builtins.length endpoint.children == 0
        then endpoint // { inherit hint; }
        else endpoint;
      n = builtins.length split.positions;
      reversed = builtins.genList
        (i: builtins.elemAt split.positions (n - 1 - i))
        n;
    in
    builtins.foldl' (inner: pos: nestUnder pos inner)
      newLeaf
      reversed;

  # -- Predicates.
  isLayer = x:
    builtins.isAttrs x
    && (x._tag or null) == "Layer"
    && x ? tag;

  isKernel = x: isLayer x && x.tag == "Kernel";
  isGeneric = x: isLayer x && x.tag == "Generic";
  isContract = x: isLayer x && x.tag == "Contract";

  isError = x:
    builtins.isAttrs x
    && (x._tag or null) == "Error"
    && x ? layer
    && x ? detail
    && x ? msg
    && x ? children;

  isDetail = x:
    builtins.isAttrs x
    && (x._tag or null) == "Detail"
    && x ? layer;

  # -- Structural equality. Works because Nix compares attrsets by content.
  eq = a: b: a == b;

in
api.namespace {
  description = "fx.diag.error: diagnostic Error ADT — Layer (Kernel/Generic/Contract), layer-discriminated Detail, msg, hint, and children tree carrying the blame path.";
  doc = ''
    Diagnostic Error ADT.

    An Error has a Layer (Kernel | Generic | Contract), a layer-discriminated
    Detail record, a short msg, an optional hint, and a list of children.
    A leaf has `children = []`; a branch has a non-empty children list
    whose entries are `{ position, error }` pairs. Sibling failures produce
    many children; a chained descent produces one child; a leaf has none.

    Constructors:
      mkKernelError   { position?, rule, msg, expected?, got?, ctx_depth?, hint? }
      mkGenericError  { type?, context?, value, desc?, index?, guard?, msg, hint? }
      mkContractError { type?, context?, value, guard, msg, hint? }

    Per-layer Detail builders:
      mkKernelDetail / mkGenericDetail / mkContractDetail

    Combinators:
      nestUnder  : Position -> Error -> Error
      addChild   : Position -> Error -> Error -> Error
      setLeafHint : Hint -> Error -> Error

    Layer constants: Kernel, Generic, Contract.
    Predicates: isError, isLayer, isDetail, isKernel, isGeneric, isContract.
    Equality: eq (structural).

    Pure data. No dependencies on kernel, trampoline, effects, tc, or
    types modules.
  '';
  tests = {
    # -- Layer ADT --
    "Kernel-is-layer" = {
      expr = isLayer Kernel;
      expected = true;
    };
    "Generic-is-layer" = {
      expr = isLayer Generic;
      expected = true;
    };
    "Kernel-has-tag" = {
      expr = Kernel.tag;
      expected = "Kernel";
    };
    "Generic-has-tag" = {
      expr = Generic.tag;
      expected = "Generic";
    };
    "plain-attrset-is-not-layer" = {
      expr = isLayer { tag = "Kernel"; };
      expected = false;
    };
    "Kernel-neq-Generic" = {
      expr = Kernel == Generic;
      expected = false;
    };

    # -- mkKernelError, no position --
    "kernel-error-no-position-is-leaf" = {
      expr = (mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = { tag = "VUnit"; };
        got = { tag = "VString"; };
      }).children;
      expected = [ ];
    };
    "kernel-error-layer-is-Kernel" = {
      expr = (mkKernelError { rule = "check"; msg = "m"; }).layer.tag;
      expected = "Kernel";
    };
    "kernel-error-carries-rule" = {
      expr = (mkKernelError { rule = "desc-arg"; msg = "m"; }).detail.rule;
      expected = "desc-arg";
    };
    "kernel-error-carries-expected" = {
      expr = (mkKernelError {
        rule = "check";
        msg = "m";
        expected = { tag = "VU"; level = 0; };
      }).detail.expected;
      expected = { tag = "VU"; level = 0; };
    };
    "kernel-error-carries-got" = {
      expr = (mkKernelError {
        rule = "check";
        msg = "m";
        got = { tag = "VU"; level = 1; };
      }).detail.got;
      expected = { tag = "VU"; level = 1; };
    };
    "kernel-error-default-ctx_depth-null" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).detail.ctx_depth;
      expected = null;
    };
    "kernel-error-default-hint-null" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).hint;
      expected = null;
    };
    "kernel-error-hint-passthrough" = {
      expr = (mkKernelError {
        rule = "r";
        msg = "m";
        hint = fx.diag.hints.mkHint "universe" "try using u 0";
      }).hint;
      expected = fx.diag.hints.mkHint "universe" "try using u 0";
    };
    "kernel-error-is-error" = {
      expr = isError (mkKernelError { rule = "r"; msg = "m"; });
      expected = true;
    };

    # -- mkKernelError with position --
    "kernel-error-with-position-has-one-child" = {
      expr = builtins.length (mkKernelError {
        position = DArgBody;
        rule = "desc-arg";
        msg = "body must have type Desc I";
      }).children;
      expected = 1;
    };
    "kernel-error-with-position-edge-is-position" = {
      expr = (builtins.elemAt (mkKernelError {
        position = DArgBody;
        rule = "desc-arg";
        msg = "body must have type Desc I";
      }).children 0).position;
      expected = DArgBody;
    };
    "kernel-error-with-position-inner-is-leaf" = {
      expr = (builtins.elemAt (mkKernelError {
        position = DArgBody;
        rule = "desc-arg";
        msg = "body must have type Desc I";
      }).children 0).error.children;
      expected = [ ];
    };
    "kernel-error-with-position-wrapper-layer-Kernel" = {
      expr = (mkKernelError {
        position = DArgBody;
        rule = "r";
        msg = "m";
      }).layer.tag;
      expected = "Kernel";
    };

    # -- mkGenericError --
    "generic-error-layer-is-Generic" = {
      expr = (mkGenericError {
        value = { n = "bad"; };
        msg = "value does not inhabit description";
      }).layer.tag;
      expected = "Generic";
    };
    "generic-error-carries-value" = {
      expr = (mkGenericError {
        value = { n = "bad"; };
        msg = "m";
      }).detail.value;
      expected = { n = "bad"; };
    };
    "generic-error-carries-type" = {
      expr = (mkGenericError {
        type = "PersonT";
        value = { };
        msg = "m";
      }).detail.type;
      expected = "PersonT";
    };
    "generic-error-carries-context" = {
      expr = (mkGenericError {
        type = "PersonT";
        context = "PersonT";
        value = { };
        msg = "m";
      }).detail.context;
      expected = "PersonT";
    };
    "generic-error-default-desc-null" = {
      expr = (mkGenericError { value = null; msg = "m"; }).detail.desc;
      expected = null;
    };
    "generic-error-guard-populated" = {
      expr = (mkGenericError {
        value = 17;
        guard = { predicate = "x > 18"; };
        msg = "refinement failed";
      }).detail.guard;
      expected = { predicate = "x > 18"; };
    };
    "generic-error-is-error" = {
      expr = isError (mkGenericError { value = 0; msg = "m"; });
      expected = true;
    };
    "generic-error-no-children" = {
      expr = (mkGenericError { value = 0; msg = "m"; }).children;
      expected = [ ];
    };
    # -- nestUnder --
    "nestUnder-wraps-as-sole-child" = {
      expr =
        let inner = mkKernelError { rule = "check"; msg = "type mismatch"; };
        in builtins.length (nestUnder DArgSort inner).children;
      expected = 1;
    };
    "nestUnder-child-has-given-position" = {
      expr =
        let inner = mkKernelError { rule = "check"; msg = "m"; };
        in (builtins.elemAt (nestUnder DArgSort inner).children 0).position;
      expected = DArgSort;
    };
    "nestUnder-child-error-is-inner" = {
      expr =
        let inner = mkKernelError { rule = "check"; msg = "m"; };
        in (builtins.elemAt (nestUnder DArgSort inner).children 0).error;
      expected = mkKernelError { rule = "check"; msg = "m"; };
    };
    "nestUnder-inherits-layer" = {
      expr =
        let inner = mkKernelError { rule = "r"; msg = "m"; };
        in (nestUnder DArgSort inner).layer.tag;
      expected = "Kernel";
    };
    "nestUnder-inherits-msg" = {
      expr =
        let inner = mkKernelError { rule = "r"; msg = "concrete message"; };
        in (nestUnder DArgSort inner).msg;
      expected = "concrete message";
    };
    "nestUnder-inherits-detail" = {
      expr =
        let
          inner = mkKernelError {
            rule = "desc-arg";
            msg = "m";
            expected = { tag = "VU"; level = 0; };
            got = { tag = "VU"; level = 1; };
          };
        in
        (nestUnder DArgSort inner).detail;
      expected = (mkKernelError {
        rule = "desc-arg";
        msg = "m";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      }).detail;
    };
    "nestUnder-stacks-two-levels" = {
      expr =
        let
          inner = mkKernelError { rule = "r"; msg = "m"; };
          hop1 = nestUnder DArgBody inner;
          hop2 = nestUnder DArgSort hop1;
          firstEdge = builtins.elemAt hop2.children 0;
          secondEdge = builtins.elemAt firstEdge.error.children 0;
        in
        [ firstEdge.position secondEdge.position ];
      expected = [ DArgSort DArgBody ];
    };

    # -- addChild --
    "addChild-appends-one-entry" = {
      expr =
        let
          root = mkGenericError {
            type = "PersonT";
            value = { };
            msg = "m";
          };
          childErr = mkGenericError { value = "bad"; msg = "m2"; };
        in
        builtins.length (addChild (Field "n") root childErr).children;
      expected = 1;
    };
    "addChild-preserves-existing-children" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          c1 = mkGenericError { value = "a"; msg = "m"; };
          c2 = mkGenericError { value = "b"; msg = "m"; };
          r1 = addChild (Field "n") root c1;
          r2 = addChild (Field "s") r1 c2;
        in
        map (e: e.position) r2.children;
      expected = [ (Field "n") (Field "s") ];
    };
    "addChild-preserves-root-layer" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          c = mkGenericError { value = "a"; msg = "m"; };
        in
        (addChild (Field "n") root c).layer.tag;
      expected = "Generic";
    };
    "addChild-preserves-root-msg" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "outer message"; };
          c = mkGenericError { value = "a"; msg = "inner"; };
        in
        (addChild (Field "n") root c).msg;
      expected = "outer message";
    };

    # -- setLeafHint --
    "setLeafHint-mutates-leaf-hint" = {
      expr =
        let
          h = fx.diag.hints.mkHint "universe" "try U(0)";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          tree = setLeafHint h leaf;
        in
        tree.hint;
      expected = fx.diag.hints.mkHint "universe" "try U(0)";
    };
    "setLeafHint-walks-to-deep-leaf" = {
      expr =
        let
          h = fx.diag.hints.mkHint "description" "hint text";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          chain = nestUnder DArgBody (nestUnder DArgSort leaf);
          withHint = setLeafHint h chain;
          walk = e:
            if builtins.length e.children == 0 then e
            else walk (builtins.elemAt e.children 0).error;
        in
        (walk withHint).hint;
      expected = fx.diag.hints.mkHint "description" "hint text";
    };
    "setLeafHint-preserves-path" = {
      expr =
        let
          h = fx.diag.hints.mkHint "description" "h";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          chain = nestUnder DArgBody (nestUnder DArgSort leaf);
          withHint = setLeafHint h chain;
        in
        [
          (builtins.elemAt withHint.children 0).position
          (builtins.elemAt
            (builtins.elemAt withHint.children 0).error.children 0).position
        ];
      expected = [ DArgBody DArgSort ];
    };
    "setLeafHint-preserves-leaf-detail" = {
      expr =
        let
          h = fx.diag.hints.mkHint "description" "h";
          leaf = mkKernelError {
            rule = "desc-arg";
            msg = "type mismatch";
            expected = { tag = "U"; level = 0; };
            got = { tag = "U"; level = 3; };
          };
          withHint = setLeafHint h leaf;
        in
        withHint.detail.rule;
      expected = "desc-arg";
    };
    "setLeafHint-no-op-on-branching-endpoint" = {
      expr =
        let
          h = fx.diag.hints.mkHint "inhabitation" "ignored";
          root = mkGenericError { value = { }; msg = "m"; };
          c1 = mkGenericError { value = "a"; msg = "m"; };
          c2 = mkGenericError { value = "b"; msg = "m"; };
          tree = addChild (Field "s") (addChild (Field "n") root c1) c2;
          result = setLeafHint h tree;
        in
        result.hint; # root was never a leaf; nothing changed.
      expected = null;
    };
    "setLeafHint-stack-safe-on-1000-deep-chain" = {
      expr =
        let
          h = fx.diag.hints.mkHint "universe" "deep hint";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          deep = builtins.foldl' (acc: _: nestUnder DArgSort acc) leaf
            (builtins.genList (x: x) 1000);
          withHint = setLeafHint h deep;
          walk = e:
            if builtins.length e.children == 0 then e
            else walk (builtins.elemAt e.children 0).error;
        in
        (walk withHint).hint;
      expected = fx.diag.hints.mkHint "universe" "deep hint";
    };

    # -- Sibling branching (Record-shaped case). --
    "sibling-branching-two-children" = {
      expr =
        let
          root = mkGenericError {
            type = "PersonT";
            context = "PersonT";
            value = { n = "wrong"; s = 42; };
            msg = "record validation failed";
          };
          errN = mkGenericError { value = "wrong"; msg = "string is not Nat"; };
          errS = mkGenericError { value = 42; msg = "int is not String"; };
          r1 = addChild (Field "n") root errN;
          r2 = addChild (Field "s") r1 errS;
        in
        builtins.length r2.children;
      expected = 2;
    };
    "sibling-branching-positions" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          errN = mkGenericError { value = "wrong"; msg = "m"; };
          errS = mkGenericError { value = 42; msg = "m"; };
          r1 = addChild (Field "n") root errN;
          r2 = addChild (Field "s") r1 errS;
        in
        [
          (builtins.elemAt r2.children 0).position
          (builtins.elemAt r2.children 1).position
        ];
      expected = [ (Field "n") (Field "s") ];
    };
    "sibling-branching-child-payloads" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          errN = mkGenericError { value = "wrong"; msg = "mN"; };
          errS = mkGenericError { value = 42; msg = "mS"; };
          r1 = addChild (Field "n") root errN;
          r2 = addChild (Field "s") r1 errS;
        in
        [
          (builtins.elemAt r2.children 0).error.detail.value
          (builtins.elemAt r2.children 1).error.detail.value
        ];
      expected = [ "wrong" 42 ];
    };

    # -- Kernel blame nested under a Generic root.
    "kernel-under-generic-root-layer-Generic" = {
      expr =
        let
          root = mkGenericError {
            type = "PersonT";
            value = { age = "hello"; };
            msg = "m";
          };
          kErr = mkKernelError {
            rule = "check";
            msg = "type mismatch";
            expected = { tag = "VUnit"; };
            got = { tag = "VString"; };
          };
        in
        (addChild (Field "age") root kErr).layer.tag;
      expected = "Generic";
    };
    "kernel-under-generic-child-position" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          kErr = mkKernelError { rule = "check"; msg = "m"; };
        in
        (builtins.elemAt (addChild (Field "age") root kErr).children 0).position;
      expected = Field "age";
    };
    "kernel-under-generic-child-layer-Kernel" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          kErr = mkKernelError { rule = "check"; msg = "m"; };
        in
        (builtins.elemAt (addChild (Field "age") root kErr).children 0).error.layer.tag;
      expected = "Kernel";
    };
    "kernel-under-generic-preserves-kernel-shape" = {
      expr =
        let
          root = mkGenericError { value = { }; msg = "m"; };
          kErr = mkKernelError {
            rule = "check";
            msg = "type mismatch";
            expected = "e";
            got = "g";
          };
        in
        (builtins.elemAt (addChild (Field "age") root kErr).children 0).error;
      expected = mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = "e";
        got = "g";
      };
    };

    # -- Detail shape discipline: per-layer key invariants.
    "kernel-detail-exposes-only-kernel-fields" = {
      expr = builtins.attrNames (mkKernelError { rule = "r"; msg = "m"; }).detail;
      expected = [
        "_tag"
        "ctx_depth"
        "expected"
        "frame"
        "got"
        "layer"
        "rule"
        "term"
        "trace"
      ];
    };
    "generic-detail-exposes-only-generic-fields" = {
      expr = builtins.attrNames (mkGenericError { value = 0; msg = "m"; }).detail;
      expected = [
        "_tag"
        "context"
        "desc"
        "guard"
        "index"
        "layer"
        "type"
        "value"
      ];
    };
    "contract-detail-exposes-only-contract-fields" = {
      expr = builtins.attrNames (mkContractError {
        value = 17;
        guard = { predicate = "x > 18"; };
        msg = "m";
      }).detail;
      expected = [
        "_tag"
        "context"
        "guard"
        "layer"
        "type"
        "value"
      ];
    };
    "kernel-detail-omits-generic-fields" = {
      expr =
        let d = (mkKernelError { rule = "r"; msg = "m"; }).detail;
        in [ (d ? type) (d ? desc) (d ? value) (d ? guard) (d ? index) ];
      expected = [ false false false false false ];
    };
    "kernel-error-default-term-null" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).detail.term;
      expected = null;
    };
    "kernel-error-default-frame-null" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).detail.frame;
      expected = null;
    };
    "kernel-error-default-trace-empty" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).detail.trace;
      expected = [ ];
    };
    "kernel-error-carries-term" = {
      expr = (mkKernelError {
        rule = "infer";
        msg = "no inference rule";
        term = { tag = "lam"; quoted = { tag = "lam"; }; };
      }).detail.term;
      expected = { tag = "lam"; quoted = { tag = "lam"; }; };
    };
    "kernel-error-carries-frame" = {
      expr = (mkKernelError {
        rule = "infer";
        msg = "m";
        frame = { depth = 3; env = [ "v0" "v1" "v2" ]; types = [ "T0" "T1" "T2" ]; names = [ "x" "y" "z" ]; };
      }).detail.frame.depth;
      expected = 3;
    };
    "kernel-error-carries-trace" = {
      expr = (mkKernelError {
        rule = "infer";
        msg = "m";
        trace = [{ rule = "desc-arg"; position = DArgSort; }];
      }).detail.trace;
      expected = [{ rule = "desc-arg"; position = DArgSort; }];
    };

    # -- captureFrame --
    "captureFrame-projects-depth" = {
      expr = (captureFrame {
        depth = 4;
        env = [ ];
        types = [ ];
        names = [ ];
      }).depth;
      expected = 4;
    };
    "captureFrame-projects-env" = {
      expr = (captureFrame {
        depth = 2;
        env = [ "v0" "v1" ];
        types = [ "T0" "T1" ];
        names = [ "a" "b" ];
      }).env;
      expected = [ "v0" "v1" ];
    };
    "captureFrame-projects-types" = {
      expr = (captureFrame {
        depth = 2;
        env = [ "v0" "v1" ];
        types = [ "T0" "T1" ];
        names = [ "a" "b" ];
      }).types;
      expected = [ "T0" "T1" ];
    };
    "captureFrame-projects-names" = {
      expr = (captureFrame {
        depth = 2;
        env = [ "v0" "v1" ];
        types = [ "T0" "T1" ];
        names = [ "a" "b" ];
      }).names;
      expected = [ "a" "b" ];
    };
    "captureFrame-defaults-names-to-empty" = {
      expr = (captureFrame { depth = 1; env = [ "v" ]; types = [ "T" ]; }).names;
      expected = [ ];
    };
    "captureFrame-output-has-four-fields" = {
      expr = builtins.attrNames (captureFrame {
        depth = 0;
        env = [ ];
        types = [ ];
      });
      expected = [ "depth" "env" "names" "types" ];
    };

    # -- appendTrace --
    "appendTrace-adds-entry-on-kernel" = {
      expr =
        let
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          updated = appendTrace "desc-arg" DArgSort leaf;
        in
        updated.detail.trace;
      expected = [{ rule = "desc-arg"; position = DArgSort; }];
    };
    "appendTrace-preserves-leaf-otherwise" = {
      expr =
        let
          leaf = mkKernelError { rule = "r"; msg = "m"; expected = "e"; got = "g"; };
          updated = appendTrace "desc-arg" DArgSort leaf;
        in
        [ updated.layer.tag updated.msg updated.detail.expected updated.detail.got ];
      expected = [ "Kernel" "m" "e" "g" ];
    };
    "appendTrace-passes-through-generic" = {
      expr =
        let
          leaf = mkGenericError { value = 0; msg = "m"; };
          updated = appendTrace "r" DArgSort leaf;
        in
        updated == leaf;
      expected = true;
    };
    "appendTrace-passes-through-contract" = {
      expr =
        let
          leaf = mkContractError {
            value = 0;
            guard = { predicate = "p"; };
            msg = "m";
          };
          updated = appendTrace "r" DArgSort leaf;
        in
        updated == leaf;
      expected = true;
    };
    "appendTrace-accepts-null-rule" = {
      expr =
        let
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          updated = appendTrace null DArgSort leaf;
        in
        (builtins.head updated.detail.trace).rule;
      expected = null;
    };
    "appendTrace-accumulates-in-application-order" = {
      expr =
        let
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          step1 = appendTrace "r1" DArgSort leaf;
          step2 = appendTrace "r2" DArgBody step1;
        in
        map (e: e.rule) step2.detail.trace;
      expected = [ "r1" "r2" ];
    };
    "generic-detail-omits-kernel-fields" = {
      expr =
        let d = (mkGenericError { value = 0; msg = "m"; }).detail;
        in [ (d ? rule) (d ? expected) (d ? got) (d ? ctx_depth) ];
      expected = [ false false false false ];
    };
    "contract-detail-omits-kernel-and-shape-fields" = {
      expr =
        let
          d = (mkContractError {
            value = 0;
            guard = { predicate = "p"; };
            msg = "m";
          }).detail;
        in
        [ (d ? rule) (d ? expected) (d ? got) (d ? desc) (d ? index) ];
      expected = [ false false false false false ];
    };
    "kernel-detail-self-discriminates" = {
      expr = (mkKernelError { rule = "r"; msg = "m"; }).detail.layer;
      expected = "Kernel";
    };
    "generic-detail-self-discriminates" = {
      expr = (mkGenericError { value = 0; msg = "m"; }).detail.layer;
      expected = "Generic";
    };
    "contract-detail-self-discriminates" = {
      expr = (mkContractError {
        value = 0;
        guard = { predicate = "p"; };
        msg = "m";
      }).detail.layer;
      expected = "Contract";
    };
    "detail-layer-agrees-with-error-layer-kernel" = {
      expr =
        let e = mkKernelError { rule = "r"; msg = "m"; };
        in e.layer.tag == e.detail.layer;
      expected = true;
    };
    "detail-layer-agrees-with-error-layer-generic" = {
      expr =
        let e = mkGenericError { value = 0; msg = "m"; };
        in e.layer.tag == e.detail.layer;
      expected = true;
    };
    "detail-layer-agrees-with-error-layer-contract" = {
      expr =
        let
          e = mkContractError {
            value = 0;
            guard = { predicate = "p"; };
            msg = "m";
          };
        in
        e.layer.tag == e.detail.layer;
      expected = true;
    };
    "isDetail-recognises-kernel-detail" = {
      expr = isDetail (mkKernelDetail { rule = "r"; });
      expected = true;
    };
    "isDetail-recognises-generic-detail" = {
      expr = isDetail (mkGenericDetail { value = 0; });
      expected = true;
    };
    "isDetail-recognises-contract-detail" = {
      expr = isDetail (mkContractDetail { value = 0; guard = { predicate = "p"; }; });
      expected = true;
    };
    "isDetail-rejects-plain-attrset" = {
      expr = isDetail { layer = "Kernel"; rule = "r"; };
      expected = false;
    };
    "mkKernelDetail-overlays-defaults" = {
      expr = (mkKernelDetail { rule = "x"; }).rule;
      expected = "x";
    };
    "mkKernelDetail-unprovided-fields-null" = {
      expr = (mkKernelDetail { rule = "x"; }).expected;
      expected = null;
    };
    "mkGenericDetail-overlays-defaults" = {
      expr = (mkGenericDetail { type = "PersonT"; }).type;
      expected = "PersonT";
    };
    "mkContractDetail-requires-guard-by-convention" = {
      expr = (mkContractDetail {
        value = 17;
        guard = { predicate = "x > 18"; };
      }).guard.predicate;
      expected = "x > 18";
    };

    # -- isError rejects malformed inputs.
    "isError-rejects-plain-attrset" = {
      expr = isError { layer = Kernel; msg = "m"; };
      expected = false;
    };
    "isError-rejects-non-attrset" = {
      expr = isError "not an error";
      expected = false;
    };
    "isError-rejects-missing-children" = {
      expr = isError {
        _tag = "Error";
        layer = Kernel;
        detail = emptyKernelDetail;
        msg = "m";
      };
      expected = false;
    };

    # -- Structural equality.
    "eq-equal-errors" = {
      expr = eq
        (mkKernelError { rule = "r"; msg = "m"; })
        (mkKernelError { rule = "r"; msg = "m"; });
      expected = true;
    };
    "eq-distinguishes-msg" = {
      expr = eq
        (mkKernelError { rule = "r"; msg = "a"; })
        (mkKernelError { rule = "r"; msg = "b"; });
      expected = false;
    };
    "eq-distinguishes-layer" = {
      expr = eq
        (mkKernelError { rule = "r"; msg = "m"; })
        (mkGenericError { value = 0; msg = "m"; });
      expected = false;
    };
    "eq-distinguishes-children-positions" = {
      expr =
        let leaf = mkKernelError { rule = "r"; msg = "m"; };
        in eq (nestUnder DArgSort leaf) (nestUnder DArgBody leaf);
      expected = false;
    };
    "native-eq-matches-eq" = {
      expr =
        let
          a = mkKernelError { rule = "r"; msg = "m"; };
          b = mkKernelError { rule = "r"; msg = "m"; };
        in
        a == b;
      expected = true;
    };

    # -- Position independence: Elem-keyed children work identically.
    "addChild-accepts-Elem-position" = {
      expr =
        let
          root = mkGenericError { value = [ ]; msg = "m"; };
          c = mkGenericError { value = "bad"; msg = "m"; };
        in
        (builtins.elemAt (addChild (Elem 3) root c).children 0).position;
      expected = Elem 3;
    };
  };

  value = {
    Kernel = api.leaf {
      value = Kernel;
      description = "Kernel: Layer constant tagging a kernel-layer diagnostic error; `Error.layer` is set to this for typechecker/elaborator failures.";
      doc = ''
        Emitted by `checkHoas` / `infer` / elaborator passes. Paired
        with a `KernelDetail` carrying `rule` (the failing kernel rule
        name) and typically `expected` / `got` carrying normalised
        value-domain types. Pre-allocated; never construct via
        `{ _tag = ...; }`.
      '';
    };
    Generic = api.leaf {
      value = Generic;
      description = "Generic: Layer constant tagging a value whose shape fails to inhabit a description.";
      doc = ''
        Emitted by sugar validators (`fx.types.*`) and the generic
        `descElim`-driven shape checker. Paired with a `GenericDetail`
        carrying `value` (the failing input) and usually `type` /
        `desc` identifying the violated contract. Pure shape failures
        (record-field type mismatch, wrong variant tag) live here;
        refinement-predicate failures belong in `Contract`.
      '';
    };
    Contract = api.leaf {
      value = Contract;
      description = "Contract: Layer constant tagging a value with the correct shape that violates a refinement predicate (`guard`).";
      doc = ''
        Paired with a `ContractDetail` carrying `value`, the mandatory
        `guard = { predicate = "…"; }`, and optionally the surface
        `type` and outer `context`. Renderer formats Contract failures
        as predicate violations distinct from shape mismatches.
        Pre-allocated; never construct via `{ _tag = ...; }`.
      '';
    };
    mkKernelDetail = api.leaf {
      value = mkKernelDetail;
      description = "mkKernelDetail: build a Kernel-layer `Detail` record from optional field overrides; defaults set every field to null (trace to []) and carry the layer self-discriminator.";
      signature = "mkKernelDetail : { rule?, expected?, got?, ctx_depth?, term?, frame?, trace? } -> Detail";
    };
    mkGenericDetail = api.leaf {
      value = mkGenericDetail;
      description = "mkGenericDetail: build a Generic-layer `Detail` record from optional field overrides; defaults set every field to null and carry the layer self-discriminator.";
      signature = "mkGenericDetail : { type?, desc?, value?, context?, index?, guard? } -> Detail";
    };
    mkContractDetail = api.leaf {
      value = mkContractDetail;
      description = "mkContractDetail: build a Contract-layer `Detail` record from optional field overrides; defaults set every field to null and carry the layer self-discriminator. Callers should always populate `guard`.";
      signature = "mkContractDetail : { type?, value?, context?, guard? } -> Detail";
    };
    mkKernelError = api.leaf {
      value = mkKernelError;
      description = "mkKernelError: build a kernel-layer leaf `Error` from `{ rule, msg, position?, expected?, got?, ctx_depth?, term?, frame?, trace?, hint? }`; when `position` is supplied, wraps the leaf in `nestUnder` so the rule emits its own descent coordinate.";
      signature = "mkKernelError : { rule, msg, position?, expected?, got?, ctx_depth?, term?, frame?, trace?, hint? } -> Error";
      doc = ''
        `rule` is the kernel-rule identifier — `hints.nix` keys its
        Hint table off `rule` plus blame-path-suffix, so use the
        canonical name (`"check"`, `"desc-arg"`, `"univ-poly"`, …) not
        an ad-hoc string. `expected` / `got` should be value-domain
        terms (post-`eval`), not unelaborated HOAS — the diff renderer
        expects normalised shape. Supplying `position` is equivalent
        to `nestUnder p (mkKernelError { … })`; use it when the rule
        emits a single descent hop, not when the caller will add hops
        of its own. `term` names the failing surface-term shape;
        `frame` is a Ctx snapshot via `captureFrame`; `trace` is
        usually left empty at emission and populated by `bindP` /
        `bindPR` as the error unwinds.
      '';
    };
    mkGenericError = api.leaf {
      value = mkGenericError;
      description = "mkGenericError: build a generic-layer leaf `Error` from `{ value, msg, type?, context?, desc?, index?, guard?, hint? }`; `value` is the thing whose shape failed to inhabit the description.";
      signature = "mkGenericError : { value, msg, type?, context?, desc?, index?, guard?, hint? } -> Error";
      doc = ''
        `type` is the surface name presented to the user (`"PersonT"`,
        `"NonEmptyList"`); `desc` is the underlying `Desc I` shape if
        the producer has it; `context` is an outer-scope name used in
        nested record/variant failures. The `guard` slot is retained
        for callers that have not yet migrated refinement failures to
        `mkContractError`; prefer Contract for new producers.
      '';
    };
    mkContractError = api.leaf {
      value = mkContractError;
      description = "mkContractError: build a contract-layer leaf `Error` from `{ value, guard, msg, type?, context?, hint? }`; `value` has the correct shape but `guard` rejected it.";
      signature = "mkContractError : { value, guard, msg, type?, context?, hint? } -> Error";
      doc = ''
        `guard` is mandatory — a `{ predicate = "…"; }` record naming
        the refinement that rejected `value`. Without a guard the
        failure is structural, not contractual, and belongs in
        `mkGenericError`. `type` and `context` describe the surrounding
        contract for the renderer.
      '';
    };
    nestUnder = api.leaf {
      value = nestUnder;
      description = "nestUnder: add a positional hop above `inner`, producing a new branch whose single child carries `position` as its edge label; pass-through of layer/detail/msg/hint preserves leaf rendering at any depth.";
      signature = "nestUnder : Position -> Error -> Error";
      doc = ''
        Pass-through invariant: the wrapper's `layer`, `detail`, `msg`,
        and `hint` are copied from `inner`. This is what lets the
        renderer pick its branch (Kernel vs Generic) and pick the
        leaf's payload at any depth without descending the chain —
        the entire single-child chain reports the same diagnostic,
        just with a longer blame path. Stacking is by repeated
        application: `nestUnder pOuter (nestUnder pInner leaf)` yields
        a chain whose outer edge is `pOuter`, inner edge `pInner`.
      '';
    };
    addChild = api.leaf {
      value = addChild;
      description = "addChild: append a keyed child `Error` to a branching `parent`; used by collecting handlers that gather many sibling failures under one root without flattening the blame paths.";
      signature = "addChild : Position -> Error -> Error -> Error  -- position, parent, child";
      doc = ''
        Use for sibling collection (record fields, variant cases, list
        elements all rejected against the same root contract). Order
        of insertion is preserved in the resulting children list, so
        callers control reporting order. The parent's `layer` /
        `detail` / `msg` are not overwritten — they describe the
        outer-shape failure, while each child describes one element's
        failure. For descent (one-deep hop), use `nestUnder` instead;
        `addChild` is the multi-sibling counterpart.
      '';
    };
    setLeafHint = api.leaf {
      value = setLeafHint;
      description = "setLeafHint: walk the single-child chain to its leaf and overwrite `hint` on the endpoint, returning a structurally-equivalent tree; stack-safe via `splitChainFast`/`splitChainSlow` to kernel-descent depth.";
      signature = "setLeafHint : Hint -> Error -> Error";
      doc = ''
        Only mutates the chain endpoint. If the endpoint is branching
        (children count > 1), returns the tree unchanged — sibling-
        specific hint attachment is the caller's responsibility, the
        function is intentionally a no-op there to avoid clobbering
        ambiguity. Stack-safe to arbitrary depth: switches from direct
        recursion to a `genericClosure` worklist past `fastPathLimit`
        (500) frames. Use after `hints.resolve` has produced a Hint
        for the failure, not before.
      '';
    };
    captureFrame = api.leaf {
      value = captureFrame;
      description = "captureFrame: project a typing context into a `{ depth, env, types, names }` Frame suitable for `KernelDetail.frame`; reads `ctx.names` defensively so contexts without name tracking still produce a well-formed frame.";
      signature = "captureFrame : Ctx -> Frame";
    };
    appendTrace = api.leaf {
      value = appendTrace;
      description = "appendTrace: append a `{ rule, position }` entry to a Kernel-layer error's `detail.trace`; non-Kernel errors pass through unchanged. Used by `bindP`/`bindPR` to auto-capture the descent chain as the error unwinds.";
      signature = "appendTrace : (String | null) -> Position -> Error -> Error";
    };
    isError = api.leaf {
      value = isError;
      description = "isError: predicate recognising the `Error` ADT — checks `_tag == \"Error\"` plus the required fields `layer`, `detail`, `msg`, `children`.";
      signature = "isError : Any -> Bool";
      doc = ''
        Use at module boundaries where input could be anything;
        internal code that constructs Errors via the per-layer
        constructors doesn't need to check. The predicate rejects bare
        attrsets that happen to have `_tag = "Error"` but are missing
        required fields — guards against accidental partial
        construction more than against type confusion.
      '';
    };
    isLayer = api.leaf {
      value = isLayer;
      description = "isLayer: predicate recognising the `Layer` ADT — checks `_tag == \"Layer\"` plus the presence of `tag`; accepts `Kernel`, `Generic`, and `Contract`.";
      signature = "isLayer : Any -> Bool";
      doc = ''
        Does not distinguish the variants — pair with a check on `.tag`
        for layer-specific dispatch, or use `isKernel` / `isGeneric` /
        `isContract`. Rejects plain attrsets `{ tag = "Kernel"; }` that
        lack `_tag`, so renderer branching can trust a positive result
        to mean a canonical constant.
      '';
    };
    isDetail = api.leaf {
      value = isDetail;
      description = "isDetail: predicate recognising the `Detail` ADT — checks `_tag == \"Detail\"` plus the presence of a `layer` self-discriminator.";
      signature = "isDetail : Any -> Bool";
    };
    isKernel = api.leaf {
      value = isKernel;
      description = "isKernel: `Layer` variant predicate — true iff the value is the `Kernel` constant.";
      signature = "isKernel : Any -> Bool";
    };
    isGeneric = api.leaf {
      value = isGeneric;
      description = "isGeneric: `Layer` variant predicate — true iff the value is the `Generic` constant.";
      signature = "isGeneric : Any -> Bool";
    };
    isContract = api.leaf {
      value = isContract;
      description = "isContract: `Layer` variant predicate — true iff the value is the `Contract` constant.";
      signature = "isContract : Any -> Bool";
    };
    eq = api.leaf {
      value = eq;
      description = "eq: structural equality on `Error` values — relies on Nix's attrset-by-content comparison so equal trees compare equal regardless of construction path.";
      signature = "eq : Error -> Error -> Bool";
      doc = ''
        Equality is content-based, so two distinct constructions of
        the same shape (`mkKernelError { rule = "r"; msg = "m"; }`
        twice) compare equal — useful for test assertions and for
        deduplicating siblings in a collecting handler. Position
        ADT values inside `children` participate in the comparison,
        so chains with reordered hops are not equal.
      '';
    };

  };
}
