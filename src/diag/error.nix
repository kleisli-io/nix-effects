# Error: the diagnostic ADT.
#
# An Error carries:
#   - layer    : Layer         (Kernel | Generic)
#   - detail   : Detail        (one unified record; fields optional)
#   - msg      : String        (short human-readable summary)
#   - hint     : Hint | null   (resolved later by hints.nix;
#                                Hint = { _tag = "Hint"; text;
#                                         category; severity; docLink; })
#   - children : [{ position : Position; error : Error }]
#
# A leaf is an Error with `children = []`. A non-empty children list marks
# a descent frame (one child) or a collection of sibling failures (many).
# The absolute blame path is the root-to-leaf sequence of children[].position,
# reconstructed at rendering time; the path is the tree shape, never stored
# duplicatedly.
#
# Layer ADT:
#   Kernel  — a term the type-checker rejected during check/infer.
#   Generic — a value that fails to inhabit a description.
#
# There is no `Contract` layer. Sugar validators emit `Generic` directly
# with a partial `Detail`; a `descElim`-driven implementation of the same
# API fills in the remaining Detail fields without changing the tag.
#
# `Guard` is a sub-variant populated inside a Generic Error's `Detail.guard`
# (a `{ predicate : String; }` record), not a top-level Layer. Refinement
# blame is semantically "value against description" — the same location as
# structural blame — so it shares the Generic renderer branch.
#
# This module is pure data. No effects; combinators build attrsets. The
# kernel consumes `Position` constants and pure combinators from here
# (via fx.diag); this module itself depends only on `api` and the sibling
# positions module.
{ lib, fx, ... }:
let
  inherit (fx.diag.positions) DArgSort DArgBody Field Elem;

  # Stack-safety switchover point for chain-walking combinators. Direct
  # recursion up to this depth, then a genericClosure worklist that
  # WHNF-forces the next node. Matches pretty.nix / hints.nix.
  fastPathLimit = 500;

  # -- Layer ADT constants.
  # Tagged attrsets with `_tag = "Layer"` mark these as terminal values
  # (not traversed by api.extractValue/extractTests).
  Kernel  = { _tag = "Layer"; tag = "Kernel";  };
  Generic = { _tag = "Layer"; tag = "Generic"; };

  # -- Detail: one unified record. Every field is optional and defaults to
  # null. Producers populate the subset that applies:
  #   Kernel:   rule, expected, got, ctx_depth
  #   Generic:  type, desc, index, context, value, guard
  # Extra fields added later are additive; existing producers keep working
  # because missing fields surface as null.
  emptyDetail = {
    context   = null;
    ctx_depth = null;
    desc      = null;
    expected  = null;
    got       = null;
    guard     = null;
    index     = null;
    rule      = null;
    type      = null;
    value     = null;
  };
  mkDetail = overrides: emptyDetail // overrides;

  # -- Internal: build a leaf Error. children = [].
  mkLeaf = { layer, detail, msg, hint ? null }:
    { _tag = "Error";
      inherit layer detail msg hint;
      children = [];
    };

  # -- mkKernelError: a Kernel-layer leaf. `position`, when supplied, is
  # added as an outer hop via nestUnder so the rule can declare its own
  # descent coordinate at the emission site.
  mkKernelError = {
    position ? null,
    rule,
    msg,
    expected ? null,
    got ? null,
    ctx_depth ? null,
    hint ? null,
  }:
    let
      leaf = mkLeaf {
        layer = Kernel;
        detail = mkDetail { inherit rule expected got ctx_depth; };
        inherit msg hint;
      };
    in
      if position == null then leaf
      else nestUnder position leaf;

  # -- mkGenericError: a Generic-layer leaf. `value` is the thing that
  # failed to inhabit the description (or the applicable sugar type).
  mkGenericError = {
    type ? null,
    context ? null,
    value,
    desc ? null,
    index ? null,
    guard ? null,
    msg,
    hint ? null,
  }:
    mkLeaf {
      layer = Generic;
      detail = mkDetail { inherit type context value desc index guard; };
      inherit msg hint;
    };

  # -- nestUnder: add a positional hop above an existing Error. The wrapper
  # inherits the inner's layer/detail/msg/hint (pass-through) so renderer
  # dispatch and leaf-content rendering work at any depth of the chain;
  # the blame path is encoded in the children edges.
  nestUnder = position: inner:
    { _tag = "Error";
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
      in splitChainFast (acc ++ [edge.position]) edge.error (depth + 1);

  splitChainSlow = acc0: err0:
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
      final = lib.last steps;
    in { positions = final._acc; endpoint = final._err; };

  setLeafHint = hint: err:
    let
      split = splitChainFast [] err 0;
      endpoint = split.endpoint;
      newLeaf =
        if builtins.length endpoint.children == 0
        then endpoint // { inherit hint; }
        else endpoint;
      n = builtins.length split.positions;
      reversed = builtins.genList
        (i: builtins.elemAt split.positions (n - 1 - i)) n;
    in builtins.foldl' (inner: pos: nestUnder pos inner)
         newLeaf reversed;

  # -- Predicates.
  isLayer = x:
    builtins.isAttrs x
    && (x._tag or null) == "Layer"
    && x ? tag;

  isError = x:
    builtins.isAttrs x
    && (x._tag or null) == "Error"
    && x ? layer
    && x ? detail
    && x ? msg
    && x ? children;

  # -- Structural equality. Works because Nix compares attrsets by content.
  eq = a: b: a == b;

in {
  inherit Kernel Generic mkDetail mkKernelError mkGenericError
          nestUnder addChild setLeafHint isError isLayer eq;



  __docs = {
    _self = {
      doc = ''
    Diagnostic Error ADT.

    An Error has a Layer (Kernel | Generic), a Detail record whose fields
    are all optional, a short msg, an optional hint, and a list of
    children. A leaf has `children = []`; a branch has a non-empty
    children list whose entries are `{ position, error }` pairs. Sibling
    failures produce many children; a chained descent produces one
    child; a leaf has none.

    Constructors:
      mkKernelError  { position?, rule, msg, expected?, got?, ctx_depth?, hint? }
      mkGenericError { type?, context?, value, desc?, index?, guard?, msg, hint? }

    Combinators:
      nestUnder  : Position -> Error -> Error
      addChild   : Position -> Error -> Error -> Error

    Layer constants: Kernel, Generic. Predicates: isError, isLayer.
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
      expected = [];
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
        rule = "r"; msg = "m";
        hint = fx.diag.hints.mkHint "universe" "try using u 0";
      }).hint;
      expected = fx.diag.hints.mkHint "universe" "try using u 0";
    };
    "kernel-error-is-error" = {
      expr = isError (mkKernelError { rule = "r"; msg = "m"; });
      expected = true;
    };
    "kernel-error-generic-detail-fields-null" = {
      expr = let d = (mkKernelError { rule = "r"; msg = "m"; }).detail;
             in [ d.type d.desc d.index d.context d.value d.guard ];
      expected = [ null null null null null null ];
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
      expected = [];
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
        value = {};
        msg = "m";
      }).detail.type;
      expected = "PersonT";
    };
    "generic-error-carries-context" = {
      expr = (mkGenericError {
        type = "PersonT";
        context = "PersonT";
        value = {};
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
      expected = [];
    };
    "generic-error-kernel-detail-fields-null" = {
      expr = let d = (mkGenericError { value = 0; msg = "m"; }).detail;
             in [ d.rule d.expected d.got d.ctx_depth ];
      expected = [ null null null null ];
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
        let inner = mkKernelError {
              rule = "desc-arg";
              msg = "m";
              expected = { tag = "VU"; level = 0; };
              got = { tag = "VU"; level = 1; };
            };
        in (nestUnder DArgSort inner).detail;
      expected = (mkKernelError {
        rule = "desc-arg";
        msg = "m";
        expected = { tag = "VU"; level = 0; };
        got = { tag = "VU"; level = 1; };
      }).detail;
    };
    "nestUnder-stacks-two-levels" = {
      expr =
        let inner = mkKernelError { rule = "r"; msg = "m"; };
            hop1 = nestUnder DArgBody inner;
            hop2 = nestUnder DArgSort hop1;
            firstEdge  = builtins.elemAt hop2.children 0;
            secondEdge = builtins.elemAt firstEdge.error.children 0;
        in [ firstEdge.position secondEdge.position ];
      expected = [ DArgSort DArgBody ];
    };

    # -- addChild --
    "addChild-appends-one-entry" = {
      expr =
        let root = mkGenericError {
              type = "PersonT"; value = {}; msg = "m";
            };
            childErr = mkGenericError { value = "bad"; msg = "m2"; };
        in builtins.length (addChild (Field "n") root childErr).children;
      expected = 1;
    };
    "addChild-preserves-existing-children" = {
      expr =
        let root = mkGenericError { value = {}; msg = "m"; };
            c1 = mkGenericError { value = "a"; msg = "m"; };
            c2 = mkGenericError { value = "b"; msg = "m"; };
            r1 = addChild (Field "n") root c1;
            r2 = addChild (Field "s") r1 c2;
        in map (e: e.position) r2.children;
      expected = [ (Field "n") (Field "s") ];
    };
    "addChild-preserves-root-layer" = {
      expr =
        let root = mkGenericError { value = {}; msg = "m"; };
            c = mkGenericError { value = "a"; msg = "m"; };
        in (addChild (Field "n") root c).layer.tag;
      expected = "Generic";
    };
    "addChild-preserves-root-msg" = {
      expr =
        let root = mkGenericError { value = {}; msg = "outer message"; };
            c = mkGenericError { value = "a"; msg = "inner"; };
        in (addChild (Field "n") root c).msg;
      expected = "outer message";
    };

    # -- setLeafHint --
    "setLeafHint-mutates-leaf-hint" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "universe" "try U(0)";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          tree = setLeafHint h leaf;
        in tree.hint;
      expected = fx.diag.hints.mkHint "universe" "try U(0)";
    };
    "setLeafHint-walks-to-deep-leaf" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "description" "hint text";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          chain = nestUnder DArgBody (nestUnder DArgSort leaf);
          withHint = setLeafHint h chain;
          walk = e:
            if builtins.length e.children == 0 then e
            else walk (builtins.elemAt e.children 0).error;
        in (walk withHint).hint;
      expected = fx.diag.hints.mkHint "description" "hint text";
    };
    "setLeafHint-preserves-path" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "description" "h";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          chain = nestUnder DArgBody (nestUnder DArgSort leaf);
          withHint = setLeafHint h chain;
        in [
          (builtins.elemAt withHint.children 0).position
          (builtins.elemAt
            (builtins.elemAt withHint.children 0).error.children 0).position
        ];
      expected = [ DArgBody DArgSort ];
    };
    "setLeafHint-preserves-leaf-detail" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "description" "h";
          leaf = mkKernelError {
            rule = "desc-arg"; msg = "type mismatch";
            expected = { tag = "U"; level = 0; };
            got      = { tag = "U"; level = 3; };
          };
          withHint = setLeafHint h leaf;
        in withHint.detail.rule;
      expected = "desc-arg";
    };
    "setLeafHint-no-op-on-branching-endpoint" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "inhabitation" "ignored";
          root = mkGenericError { value = {}; msg = "m"; };
          c1 = mkGenericError { value = "a"; msg = "m"; };
          c2 = mkGenericError { value = "b"; msg = "m"; };
          tree = addChild (Field "s") (addChild (Field "n") root c1) c2;
          result = setLeafHint h tree;
        in result.hint;   # root was never a leaf; nothing changed.
      expected = null;
    };
    "setLeafHint-stack-safe-on-1000-deep-chain" = {
      expr =
        let
          h    = fx.diag.hints.mkHint "universe" "deep hint";
          leaf = mkKernelError { rule = "r"; msg = "m"; };
          deep = builtins.foldl' (acc: _: nestUnder DArgSort acc) leaf
                   (builtins.genList (x: x) 1000);
          withHint = setLeafHint h deep;
          walk = e:
            if builtins.length e.children == 0 then e
            else walk (builtins.elemAt e.children 0).error;
        in (walk withHint).hint;
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
        in builtins.length r2.children;
      expected = 2;
    };
    "sibling-branching-positions" = {
      expr =
        let
          root = mkGenericError { value = {}; msg = "m"; };
          errN = mkGenericError { value = "wrong"; msg = "m"; };
          errS = mkGenericError { value = 42; msg = "m"; };
          r1 = addChild (Field "n") root errN;
          r2 = addChild (Field "s") r1 errS;
        in [
          (builtins.elemAt r2.children 0).position
          (builtins.elemAt r2.children 1).position
        ];
      expected = [ (Field "n") (Field "s") ];
    };
    "sibling-branching-child-payloads" = {
      expr =
        let
          root = mkGenericError { value = {}; msg = "m"; };
          errN = mkGenericError { value = "wrong"; msg = "mN"; };
          errS = mkGenericError { value = 42; msg = "mS"; };
          r1 = addChild (Field "n") root errN;
          r2 = addChild (Field "s") r1 errS;
        in [
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
        in (addChild (Field "age") root kErr).layer.tag;
      expected = "Generic";
    };
    "kernel-under-generic-child-position" = {
      expr =
        let
          root = mkGenericError { value = {}; msg = "m"; };
          kErr = mkKernelError { rule = "check"; msg = "m"; };
        in (builtins.elemAt (addChild (Field "age") root kErr).children 0).position;
      expected = Field "age";
    };
    "kernel-under-generic-child-layer-Kernel" = {
      expr =
        let
          root = mkGenericError { value = {}; msg = "m"; };
          kErr = mkKernelError { rule = "check"; msg = "m"; };
        in (builtins.elemAt (addChild (Field "age") root kErr).children 0).error.layer.tag;
      expected = "Kernel";
    };
    "kernel-under-generic-preserves-kernel-shape" = {
      expr =
        let
          root = mkGenericError { value = {}; msg = "m"; };
          kErr = mkKernelError {
            rule = "check";
            msg = "type mismatch";
            expected = "e";
            got = "g";
          };
        in (builtins.elemAt (addChild (Field "age") root kErr).children 0).error;
      expected = mkKernelError {
        rule = "check";
        msg = "type mismatch";
        expected = "e";
        got = "g";
      };
    };

    # -- Detail shape discipline.
    "detail-keys-same-across-layers" = {
      expr =
        let
          kKeys = builtins.attrNames (mkKernelError { rule = "r"; msg = "m"; }).detail;
          gKeys = builtins.attrNames (mkGenericError { value = 0; msg = "m"; }).detail;
        in kKeys == gKeys;
      expected = true;
    };
    "detail-exposes-all-fields" = {
      expr = builtins.attrNames emptyDetail;
      expected = [
        "context" "ctx_depth" "desc" "expected" "got"
        "guard" "index" "rule" "type" "value"
      ];
    };
    "mkDetail-overlays-on-emptyDetail" = {
      expr = (mkDetail { rule = "x"; }).rule;
      expected = "x";
    };
    "mkDetail-unprovided-fields-null" = {
      expr = (mkDetail { rule = "x"; }).value;
      expected = null;
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
        detail = emptyDetail;
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
        let a = mkKernelError { rule = "r"; msg = "m"; };
            b = mkKernelError { rule = "r"; msg = "m"; };
        in a == b;
      expected = true;
    };

    # -- Position independence: Elem-keyed children work identically.
    "addChild-accepts-Elem-position" = {
      expr =
        let root = mkGenericError { value = []; msg = "m"; };
            c = mkGenericError { value = "bad"; msg = "m"; };
        in (builtins.elemAt (addChild (Elem 3) root c).children 0).position;
      expected = Elem 3;
    };
  };
    };

    Kernel = {
      description = "Kernel: Layer constant tagging a kernel-layer diagnostic error; `Error.layer` is set to this for typechecker/elaborator failures, distinguishing them from Generic-layer surface errors.";
      doc = ''
        Emitted by `checkHoas` / `infer` / elaborator passes. Always
        paired with `Detail.rule` (the failing kernel rule name), and
        typically with `Detail.expected` and `Detail.got` carrying
        normalised value-domain types. Renderer branches on this
        constant to format type-mismatch shapes; the alternative is
        `Generic`. Pre-allocated; never construct via `{ _tag = ...; }`.
      '';
    };
    Generic = {
      description = "Generic: Layer constant tagging a surface-language diagnostic error; `Error.layer` is set to this for `fx.types`/`fx.generic` failures coming from refinement, guard, or shape predicates.";
      doc = ''
        Emitted by sugar validators (`fx.types.*`), the generic
        `descElim`-driven shape checker, and refinement predicates.
        Always paired with `Detail.value` (the failing input); usually
        with `Detail.type` / `Detail.desc` identifying which contract
        was violated; with `Detail.guard` when a refinement predicate
        rejected the value. Refinement blame uses this layer rather
        than a separate `Contract` layer.
      '';
    };
    mkDetail = {
      description = "mkDetail: build a `Detail` record by overriding fields of the canonical empty-Detail; every field is optional so producers populate the subset that applies to their layer.";
      signature = "mkDetail : { rule?, expected?, got?, ctx_depth?, type?, context?, value?, desc?, index?, guard? } -> Detail";
      doc = ''
        Use only when constructing `Error` records manually outside
        `mkKernelError` / `mkGenericError`. The two constructors call
        this for you. Guarantee: every Detail value has the same key
        set regardless of which fields the caller populated — missing
        fields are `null`, never absent. Consumers should pattern-match
        on `null` rather than `?`.
      '';
    };
    mkKernelError = {
      description = "mkKernelError: build a kernel-layer leaf `Error` from `{ rule, msg, position?, expected?, got?, ctx_depth?, hint? }`; when `position` is supplied, wraps the leaf in `nestUnder` so the rule emits its own descent coordinate.";
      signature = "mkKernelError : { rule, msg, position?, expected?, got?, ctx_depth?, hint? } -> Error";
      doc = ''
        `rule` is the kernel-rule identifier — `hints.nix` keys its
        Hint table off `rule` plus blame-path-suffix, so use the
        canonical name (`"check"`, `"desc-arg"`, `"univ-poly"`, …) not
        an ad-hoc string. `expected` / `got` should be value-domain
        terms (post-`eval`), not unelaborated HOAS — the diff renderer
        expects normalised shape. Supplying `position` is equivalent
        to `nestUnder p (mkKernelError { … })`; use it when the rule
        emits a single descent hop, not when the caller will add hops
        of its own.
      '';
    };
    mkGenericError = {
      description = "mkGenericError: build a generic-layer leaf `Error` from `{ value, msg, type?, context?, desc?, index?, guard?, hint? }`; `value` is the thing that failed to inhabit the description.";
      signature = "mkGenericError : { value, msg, type?, context?, desc?, index?, guard?, hint? } -> Error";
      doc = ''
        `type` is the surface name presented to the user (`"PersonT"`,
        `"NonEmptyList"`); `desc` is the underlying `Desc I` shape if
        the producer has it; `context` is an outer-scope name used in
        nested record/variant failures. Populate `guard = { predicate
        = "…"; }` when a refinement predicate rejected an otherwise
        well-shaped value — the renderer formats this as a
        contract-violation rather than a shape-mismatch. Producers
        only need to populate the fields they have; null elsewhere is
        fine.
      '';
    };
    nestUnder = {
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
    addChild = {
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
    setLeafHint = {
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
    isError = {
      description = "isError: predicate recognising the `Error` ADT — checks `_tag == \"Error\"` plus the required fields `layer`, `detail`, `msg`, `children`.";
      signature = "isError : Any -> Bool";
      doc = ''
        Use at module boundaries where input could be anything;
        internal code that constructs Errors via `mkKernelError` /
        `mkGenericError` doesn't need to check. The predicate rejects
        bare attrsets that happen to have `_tag = "Error"` but are
        missing required fields — guards against accidental partial
        construction more than against type confusion.
      '';
    };
    isLayer = {
      description = "isLayer: predicate recognising the `Layer` ADT — checks `_tag == \"Layer\"` plus the presence of `tag`; accepts both `Kernel` and `Generic` constants.";
      signature = "isLayer : Any -> Bool";
      doc = ''
        Does not distinguish `Kernel` from `Generic` — pair with a
        check on `.tag` for layer-specific dispatch. Rejects plain
        attrsets `{ tag = "Kernel"; }` that lack `_tag`, so renderer
        branching can trust a positive result to mean the canonical
        constant.
      '';
    };
    eq = {
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
