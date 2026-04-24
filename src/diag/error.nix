# Error: the diagnostic ADT.
#
# An Error carries:
#   - layer    : Layer         (Kernel | Generic)
#   - detail   : Detail        (one unified record; fields optional)
#   - msg      : String        (short human-readable summary)
#   - hint     : String | null (resolved later by hints.nix)
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
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.diag.positions) DArgSort DArgBody Field Elem;

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

in mk {
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
  value = {
    inherit
      Kernel Generic
      mkDetail
      mkKernelError mkGenericError
      nestUnder addChild
      isError isLayer eq;
  };
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
        expected = { tag = "VNat"; };
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
        rule = "r"; msg = "m"; hint = "try using u 0";
      }).hint;
      expected = "try using u 0";
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
            expected = { tag = "VNat"; };
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
}
