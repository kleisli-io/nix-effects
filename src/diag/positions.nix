# Position: shared diagnostic alphabet.
#
# A Position names a sub-location in a structural descent through a
# description (Desc) or through raw MLTT structure. It is pure data:
# no source locations, no behaviour.
#
# Positions are description-centric. `DArgSort` names the sort
# sub-position of `arg`; `DPlusL` names the left summand of `plus`;
# `PiDom` names the domain of `Π`. The same coordinate is meaningful
# to any walker of the same structure — a kernel rule checking an
# `arg`-shaped term, a fold visiting an `arg`-constructor of a Desc
# value, or a contract validator descending into a record field.
#
# Per-Position metadata:
#   - `tag`     : variant discriminator (used by resolvers / hint keys);
#   - `segment` : short rendered path label;
#   - `intent`  : semantic role description, rendered by the pretty
#                  printer as a one-line "what was expected at this
#                  position" gloss alongside the segment;
#   - `rule`    : optional descent-rule annotation populated by `bindPR`
#                  at the emission site; null on every constant.
#
# `intent` and `rule` are opaque to the hint resolver: keys are built
# from `tag` only, so decorating Positions does not affect lookup.
#
# No dependency on the type-checker or the types layer.
{ api, ... }:
let
  # Tagged-attrset constructor. `_tag = "Position"` is a nominal
  # marker used by `isPosition`; `tag` is the variant discriminator;
  # `segment` is the rendered path label. Keeping the segment on the
  # Position itself collapses `renderSegment` to an O(1) field read
  # and removes the ordering-sensitive `if/else-if` cascade, whose
  # per-hop cost used to scale with the branch position of the
  # matching tag. `intent` is the role description used by the
  # pretty printer's per-position gloss; `rule` is the optional
  # descent-rule annotation, null on every constant and overridden
  # at the emission site through `withRule` / `bindPR`.
  mkPos = tag: segment: intent: extra:
    { _tag = "Position"; rule = null; inherit tag segment intent; } // extra;

  # Decorate a Position with a descent-rule annotation. Returns a
  # structurally distinct Position; the original is left intact so
  # canonical constants stay shared. Intended use is `bindPR`: a
  # kernel-rule call site supplies its own identifier so the wrapping
  # hop on the blame chain records which rule emitted the descent.
  withRule = rule: pos: pos // { inherit rule; };

  # Positions naming sub-locations inside the five Desc constructors.
  DArgLevel = mkPos "DArgLevel" "arg.k" "the universe level at which `arg`'s sort lives" { };
  DArgSort = mkPos "DArgSort" "arg.S" "the sort inhabited by `arg`'s argument" { };
  DArgEq = mkPos "DArgEq" "arg.eq" "the equality witness paired with `arg`'s sort" { };
  DArgBody = mkPos "DArgBody" "arg.T" "the description body produced by `arg`'s family" { };
  DPiLevel = mkPos "DPiLevel" "pi.k" "the universe level at which `pi`'s domain lives" { };
  DPiSort = mkPos "DPiSort" "pi.S" "the sort inhabited by `pi`'s domain" { };
  DPiEq = mkPos "DPiEq" "pi.eq" "the equality witness paired with `pi`'s sort" { };
  DPiFn = mkPos "DPiFn" "pi.f" "the index selector function of `pi`" { };
  DPiBody = mkPos "DPiBody" "pi.T" "the description body produced by `pi`'s family" { };
  DElimLevel = mkPos "DElimLevel" "elim.k" "the universe level at which the eliminator's motive lives" { };
  DRetIndex = mkPos "DRetIndex" "ret.j" "the index value supplied to `ret`" { };
  DRecIndex = mkPos "DRecIndex" "rec.j" "the index value supplied to `rec`" { };
  DRecTail = mkPos "DRecTail" "rec.D" "the description tail spliced onto `rec`" { };
  DPlusL = mkPos "DPlusL" "plus.L" "the left summand of `plus`" { };
  DPlusR = mkPos "DPlusR" "plus.R" "the right summand of `plus`" { };

  # Positions naming sub-locations in raw MLTT structure (outside Desc).
  PiDom = mkPos "PiDom" "Π.dom" "the domain type of Π" { };
  PiCod = mkPos "PiCod" "Π.cod" "the codomain family of Π" { };
  SigmaFst = mkPos "SigmaFst" "Σ.fst" "the first component type of Σ" { };
  SigmaSnd = mkPos "SigmaSnd" "Σ.snd" "the second component type of Σ" { };
  AnnTerm = mkPos "AnnTerm" "ann.term" "the term being annotated" { };
  AnnType = mkPos "AnnType" "ann.type" "the type annotation supplied" { };
  MuUnroll = mkPos "MuUnroll" "μ" "an unrolling step of μ" { };
  AppHead = mkPos "AppHead" "app.head" "the function applied" { };
  AppArg = mkPos "AppArg" "app.arg" "the argument supplied to the application" { };

  # Term-side positions for binding-form bodies and the universal
  # CHECK→INFER sub-rule fallthrough. `LamBody` and `LetBody` name
  # the body slots of `lam` and `let` at the term level — distinct
  # from `PiCod` (the type-level codomain position) so blame chains
  # can carry both term-shape and type-shape information without
  # collapse. `Sub` names the catch-all subsumption bridge where
  # CHECK falls through to INFER + structural conv.
  LamBody = mkPos "LamBody" "lam.body" "the body of the lambda under its bound variable" { };
  LetBody = mkPos "LetBody" "let.body" "the body of the let-binding" { };
  Sub = mkPos "Sub" "sub" "the subsumption bridge from CHECK to INFER" { };

  # Positions naming sub-locations inside eliminator rules — shared
  # across generated datatype eliminators, sum-elim, desc-elim, desc-ind, j.
  Scrut = mkPos "Scrut" "scrut" "the scrutinee of the eliminator" { };
  Motive = mkPos "Motive" "motive" "the motive of the eliminator" { };

  # Positions naming sub-locations inside the Mu-layer operations
  # (desc-con, desc-ind).
  MuDesc = mkPos "MuDesc" "con.D" "the description argument of `con`" { };
  MuIndex = mkPos "MuIndex" "con.i" "the index value supplied to `con`" { };
  MuPayload = mkPos "MuPayload" "con.d" "the payload of `con` at its index" { };

  # Positions naming sub-locations inside the `j` eliminator.
  JType = mkPos "JType" "J.A" "the type carrying `J`'s two endpoints" { };
  JLhs = mkPos "JLhs" "J.a" "the left endpoint of `J`" { };
  JRhs = mkPos "JRhs" "J.b" "the right endpoint of `J`" { };
  JEq = mkPos "JEq" "J.eq" "the equality witness consumed by `J`" { };

  # Opaque-lam's type annotation sub-position.
  OpaqueType = mkPos "OpaqueType" "opaque.type" "the Π-type annotation of the opaque lambda" { };

  # Positions naming sub-locations inside Level expressions.
  LevelSucPred = mkPos "LevelSucPred" "suc.pred" "the predecessor of `suc`" { };
  LevelMaxLhs = mkPos "LevelMaxLhs" "max.L" "the left operand of `max`" { };
  LevelMaxRhs = mkPos "LevelMaxRhs" "max.R" "the right operand of `max`" { };

  # Position naming the level argument of `U(k)`.
  ULevel = mkPos "ULevel" "U.k" "the level argument of `U`" { };

  # Parameterised positions for value-side descent through records,
  # lists, and tagged unions. Segment is computed from the parameter
  # at construction time; positions are long-lived per descent frame,
  # so the cost is amortised.
  Field = name: mkPos "Field" ("." + name)
    ("the value at field `" + name + "`")
    { inherit name; };
  Elem = idx: mkPos "Elem" ("[" + toString idx + "]")
    ("the element at index " + toString idx)
    { inherit idx; };
  Tag = name: mkPos "Tag" ("#" + name)
    ("the payload of variant `" + name + "`")
    { inherit name; };
  # Tuple component (statically-indexed product). Renders identically to
  # Elem ("[i]") but stays distinct at the position level so consumers can
  # tell n-ary tuple descent from list-element descent.
  Tuple = idx: mkPos "Tuple" ("[" + toString idx + "]")
    ("the tuple component at position " + toString idx)
    { inherit idx; };

  # Layer coordinate for the homogeneous `desc-con` trampoline. Names
  # the k-th step in a peeled linear-recursive desc-con chain
  # (k = 0 outermost, k = n base). One segment compresses the
  # otherwise O(k × nFields) structural path
  # `(MuPayload → DPlusL|R → SigmaSnd^{nFields})^k`; the homogeneity
  # of the trampoline (same D, same plus-side, same nFields per layer)
  # makes layer depth the only varying coordinate. Mirrors `Elem`'s
  # shape (ℕ → Position) because the underlying object is the same:
  # a Nat-indexed coordinate into a sequence-like structure.
  DConLayer = layer: mkPos "DConLayer" ("con[" + toString layer + "]")
    ("the " + toString layer + "-th `con` unrolling step")
    { inherit layer; };

  # Parameterised position naming a case-handler inside an eliminator:
  # generated constructor names, "inl"/"inr" (sum-elim), "base" (j),
  # "onRet"/"onArg"/"onRec"/"onPi"/"onPlus" (desc-elim), "step"
  # (desc-ind).
  Case = name: mkPos "Case" ("@" + name)
    ("the body of the `" + name + "` case")
    { inherit name; };

  # Structural equality works because Nix compares attrsets by
  # contents. `eq` is exposed for readers who prefer an explicit
  # function over `==`.
  eq = a: b: a == b;

  isPosition = x:
    builtins.isAttrs x
    && (x._tag or null) == "Position"
    && x ? tag;

  # Render a single position as a short human-readable segment.
  # Names are description-centric: "arg.S", "plus.L", ".age". The
  # segment is carried as a field on the Position itself so rendering
  # is a single attribute read, independent of the alphabet's size.
  renderSegment = pos: pos.segment;

in
api.namespace {
  description = "fx.diag.positions: shared diagnostic alphabet of structural sub-locations (DArgSort, DPlusL, PiDom, …) carrying tag, segment, intent, and rule annotation.";
  doc = ''
    Shared diagnostic alphabet. Pure data.

    A Position names the blame location in a structural descent through
    a Desc or through raw MLTT structure (Π / Σ / Ann / μ / App). The
    alphabet is description-centric: names such as `DArgSort`, `DPlusL`,
    and `PiDom` identify sub-positions by their meaning in the structure,
    not by the code path that happens to visit them.

    Each Position carries four fields:

      - `tag`     : variant discriminator (used by hint-key lookup);
      - `segment` : short rendered path label (e.g. `"arg.S"`, `"Π.dom"`);
      - `intent`  : semantic role description, rendered by the pretty
                     printer as a "what was expected at this position"
                     gloss alongside the segment;
      - `rule`    : optional descent-rule annotation; null on every
                     constant. `withRule` produces a decorated variant
                     and `bindPR` populates it at the emission site.

    `intent` and `rule` are opaque to the hint resolver: keys are built
    from `tag` only, so decorating Positions does not affect lookup.

    Two kinds of consumer:

      - A kernel enrichment layer that wraps rule delegations, emitting
        a child error tagged with the `Position` of the sub-call that
        failed.
      - A value-level validator (record / list / variant field walkers)
        that emits `Field` / `Elem` / `Tag` positions from its per-
        component blame traversal.

    Both consumers produce `Error` trees whose children are keyed by
    `Position`, allowing errors from either source to compose into one
    tree.
  '';
  tests = {
    "DArgSort-is-position" = {
      expr = isPosition DArgSort;
      expected = true;
    };
    "DArgSort-has-tag" = {
      expr = DArgSort.tag;
      expected = "DArgSort";
    };
    "plain-attrset-is-not-position" = {
      expr = isPosition { tag = "DArgSort"; };
      expected = false;
    };
    "Field-has-name" = {
      expr = (Field "age").name;
      expected = "age";
    };
    "Field-has-tag" = {
      expr = (Field "age").tag;
      expected = "Field";
    };
    "Elem-has-idx" = {
      expr = (Elem 3).idx;
      expected = 3;
    };
    "Tag-has-name" = {
      expr = (Tag "Some").name;
      expected = "Some";
    };

    "eq-reflexive-nullary" = {
      expr = eq DArgSort DArgSort;
      expected = true;
    };
    "eq-distinguishes-nullary" = {
      expr = eq DArgSort DArgBody;
      expected = false;
    };
    "native-eq-nullary" = {
      expr = DArgSort == DArgSort;
      expected = true;
    };
    "native-eq-Field-same" = {
      expr = Field "age" == Field "age";
      expected = true;
    };
    "native-eq-Field-different" = {
      expr = Field "age" == Field "name";
      expected = false;
    };
    "native-eq-Elem-same" = {
      expr = Elem 3 == Elem 3;
      expected = true;
    };
    "native-eq-Elem-different" = {
      expr = Elem 3 == Elem 4;
      expected = false;
    };
    "nullary-neq-parameterised" = {
      expr = DArgSort == { _tag = "Position"; tag = "DArgSort"; extra = null; };
      expected = false;
    };

    "render-DArgSort" = {
      expr = renderSegment DArgSort;
      expected = "arg.S";
    };
    "render-DArgLevel" = {
      expr = renderSegment DArgLevel;
      expected = "arg.k";
    };
    "render-DArgBody" = {
      expr = renderSegment DArgBody;
      expected = "arg.T";
    };
    "render-DArgEq" = {
      expr = renderSegment DArgEq;
      expected = "arg.eq";
    };
    "render-DPiEq" = {
      expr = renderSegment DPiEq;
      expected = "pi.eq";
    };
    "render-DPiFn" = {
      expr = renderSegment DPiFn;
      expected = "pi.f";
    };
    "render-DPiLevel" = {
      expr = renderSegment DPiLevel;
      expected = "pi.k";
    };
    "render-DPlusL" = {
      expr = renderSegment DPlusL;
      expected = "plus.L";
    };
    "render-DPlusR" = {
      expr = renderSegment DPlusR;
      expected = "plus.R";
    };
    "render-PiDom" = {
      expr = renderSegment PiDom;
      expected = "Π.dom";
    };
    "render-MuUnroll" = {
      expr = renderSegment MuUnroll;
      expected = "μ";
    };
    "render-Field" = {
      expr = renderSegment (Field "age");
      expected = ".age";
    };
    "render-Elem" = {
      expr = renderSegment (Elem 3);
      expected = "[3]";
    };
    "render-Tag" = {
      expr = renderSegment (Tag "Some");
      expected = "#Some";
    };
    "render-Scrut" = {
      expr = renderSegment Scrut;
      expected = "scrut";
    };
    "render-Motive" = {
      expr = renderSegment Motive;
      expected = "motive";
    };
    "render-MuDesc" = {
      expr = renderSegment MuDesc;
      expected = "con.D";
    };
    "render-MuPayload" = {
      expr = renderSegment MuPayload;
      expected = "con.d";
    };
    "render-JLhs" = {
      expr = renderSegment JLhs;
      expected = "J.a";
    };
    "render-OpaqueType" = {
      expr = renderSegment OpaqueType;
      expected = "opaque.type";
    };
    "render-LevelSucPred" = {
      expr = renderSegment LevelSucPred;
      expected = "suc.pred";
    };
    "render-LevelMaxLhs" = {
      expr = renderSegment LevelMaxLhs;
      expected = "max.L";
    };
    "render-LevelMaxRhs" = {
      expr = renderSegment LevelMaxRhs;
      expected = "max.R";
    };
    "render-ULevel" = {
      expr = renderSegment ULevel;
      expected = "U.k";
    };
    "render-LamBody" = {
      expr = renderSegment LamBody;
      expected = "lam.body";
    };
    "render-LetBody" = {
      expr = renderSegment LetBody;
      expected = "let.body";
    };
    "render-Sub" = {
      expr = renderSegment Sub;
      expected = "sub";
    };
    "LamBody-is-position" = {
      expr = isPosition LamBody;
      expected = true;
    };
    "LetBody-distinct-from-LamBody" = {
      expr = LetBody == LamBody;
      expected = false;
    };
    "Sub-is-singleton" = {
      expr = Sub == Sub;
      expected = true;
    };
    "render-DConLayer-zero" = {
      expr = renderSegment (DConLayer 0);
      expected = "con[0]";
    };
    "render-DConLayer-deep" = {
      expr = renderSegment (DConLayer 4000);
      expected = "con[4000]";
    };
    "DConLayer-is-position" = {
      expr = isPosition (DConLayer 4000);
      expected = true;
    };
    "DConLayer-has-layer" = {
      expr = (DConLayer 4000).layer;
      expected = 4000;
    };
    "DConLayer-eq-same" = {
      expr = DConLayer 17 == DConLayer 17;
      expected = true;
    };
    "DConLayer-distinct-by-layer" = {
      expr = DConLayer 0 == DConLayer 1;
      expected = false;
    };
    "DConLayer-distinct-from-Elem" = {
      # Same numeric coordinate; the quotient position must stay distinct
      # from list-element descent even when the underlying index agrees.
      expr = DConLayer 3 == Elem 3;
      expected = false;
    };
    "render-Case" = {
      expr = renderSegment (Case "zero");
      expected = "@zero";
    };
    "Tuple-has-idx" = {
      expr = (Tuple 2).idx;
      expected = 2;
    };
    "Tuple-has-tag" = {
      expr = (Tuple 2).tag;
      expected = "Tuple";
    };
    "render-Tuple" = {
      expr = renderSegment (Tuple 0);
      expected = "[0]";
    };
    "Tuple-distinct-from-Elem" = {
      expr = Tuple 3 == Elem 3;
      expected = false;
    };
    "native-eq-Tuple-same" = {
      expr = Tuple 1 == Tuple 1;
      expected = true;
    };
    "Case-parameterised" = {
      expr = (Case "onRet").name;
      expected = "onRet";
    };
    "Case-eq" = {
      expr = Case "zero" == Case "zero";
      expected = true;
    };
    "Case-neq-different-name" = {
      expr = Case "zero" == Case "succ";
      expected = false;
    };

    # -- intent: every Position constant carries a non-empty intent.
    "DArgSort-has-intent" = {
      expr = DArgSort.intent;
      expected = "the sort inhabited by `arg`'s argument";
    };
    "DArgBody-has-intent" = {
      expr = DArgBody.intent;
      expected = "the description body produced by `arg`'s family";
    };
    "PiDom-has-intent" = {
      expr = PiDom.intent;
      expected = "the domain type of Π";
    };
    "PiCod-has-intent" = {
      expr = PiCod.intent;
      expected = "the codomain family of Π";
    };
    "Motive-has-intent" = {
      expr = Motive.intent;
      expected = "the motive of the eliminator";
    };
    "AppHead-has-intent" = {
      expr = AppHead.intent;
      expected = "the function applied";
    };
    "AppArg-has-intent" = {
      expr = AppArg.intent;
      expected = "the argument supplied to the application";
    };
    "LamBody-has-intent" = {
      expr = LamBody.intent;
      expected = "the body of the lambda under its bound variable";
    };
    "Sub-has-intent" = {
      expr = Sub.intent;
      expected = "the subsumption bridge from CHECK to INFER";
    };
    "MuDesc-has-intent" = {
      expr = MuDesc.intent;
      expected = "the description argument of `con`";
    };
    "Field-intent-quotes-name" = {
      expr = (Field "age").intent;
      expected = "the value at field `age`";
    };
    "Elem-intent-uses-idx" = {
      expr = (Elem 3).intent;
      expected = "the element at index 3";
    };
    "Tag-intent-quotes-name" = {
      expr = (Tag "Some").intent;
      expected = "the payload of variant `Some`";
    };
    "Tuple-intent-uses-idx" = {
      expr = (Tuple 0).intent;
      expected = "the tuple component at position 0";
    };
    "Case-intent-quotes-name" = {
      expr = (Case "zero").intent;
      expected = "the body of the `zero` case";
    };
    "DConLayer-intent-uses-layer" = {
      expr = (DConLayer 4).intent;
      expected = "the 4-th `con` unrolling step";
    };
    "every-nullary-constant-has-non-empty-intent" = {
      expr =
        let
          nullaries = [
            DArgLevel
            DArgSort
            DArgEq
            DArgBody
            DPiLevel
            DPiSort
            DPiEq
            DPiFn
            DPiBody
            DElimLevel
            DRetIndex
            DRecIndex
            DRecTail
            DPlusL
            DPlusR
            PiDom
            PiCod
            SigmaFst
            SigmaSnd
            AnnTerm
            AnnType
            MuUnroll
            AppHead
            AppArg
            LamBody
            LetBody
            Sub
            Scrut
            Motive
            MuDesc
            MuIndex
            MuPayload
            JType
            JLhs
            JRhs
            JEq
            OpaqueType
            LevelSucPred
            LevelMaxLhs
            LevelMaxRhs
            ULevel
          ];
        in
        builtins.all
          (p: builtins.isString p.intent && p.intent != "")
          nullaries;
      expected = true;
    };

    # -- rule: defaults to null on every constant; withRule decorates.
    "DArgSort-rule-defaults-null" = {
      expr = DArgSort.rule;
      expected = null;
    };
    "Field-rule-defaults-null" = {
      expr = (Field "age").rule;
      expected = null;
    };
    "withRule-stores-rule-on-position" = {
      expr = (withRule "desc-arg" DArgSort).rule;
      expected = "desc-arg";
    };
    "withRule-preserves-tag" = {
      expr = (withRule "r" DArgSort).tag;
      expected = "DArgSort";
    };
    "withRule-preserves-segment" = {
      expr = (withRule "r" DArgSort).segment;
      expected = "arg.S";
    };
    "withRule-preserves-intent" = {
      expr = (withRule "r" DArgSort).intent;
      expected = "the sort inhabited by `arg`'s argument";
    };
    "withRule-preserves-isPosition" = {
      expr = isPosition (withRule "r" DArgSort);
      expected = true;
    };
    "withRule-distinguishes-by-rule" = {
      expr = withRule "a" DArgSort == withRule "b" DArgSort;
      expected = false;
    };
    "withRule-same-rule-eq" = {
      expr = withRule "r" DArgSort == withRule "r" DArgSort;
      expected = true;
    };
    "withRule-on-parameterised-preserves-name" = {
      expr = (withRule "r" (Field "age")).name;
      expected = "age";
    };
    "withRule-replaces-prior-rule" = {
      expr = (withRule "b" (withRule "a" DArgSort)).rule;
      expected = "b";
    };
    "renderSegment-ignores-rule" = {
      expr = renderSegment (withRule "r" DArgSort);
      expected = "arg.S";
    };

    # -- Hint slug discipline: tag (and therefore hint-key membership)
    # is unaffected by rule decoration. Confirms the resolver's
    # opaqueness invariant at the Position level.
    "withRule-preserves-tag-for-hint-keys" = {
      expr =
        let decorated = withRule "r" DArgSort;
        in decorated.tag == DArgSort.tag;
      expected = true;
    };
  };

  value =
    let
      constantPositions = {
        inherit
          DArgLevel DArgSort DArgEq DArgBody
          DPiLevel DPiSort DPiEq DPiFn DPiBody
          DElimLevel
          DRetIndex
          DRecIndex DRecTail
          DPlusL DPlusR
          PiDom PiCod
          SigmaFst SigmaSnd
          AnnTerm AnnType
          MuUnroll
          AppHead AppArg
          LamBody LetBody Sub
          Scrut Motive
          MuDesc MuIndex MuPayload
          JType JLhs JRhs JEq
          OpaqueType
          LevelSucPred LevelMaxLhs LevelMaxRhs ULevel;
      };
      positionLeaf = name: value: api.leaf {
        inherit value;
        description = "${name}: canonical Position constant for ${value.intent or value.segment}.";
        signature = "Position";
        doc = "Canonical diagnostic Position constant. Segment: `${value.segment}`.";
      };
    in
    builtins.mapAttrs positionLeaf constantPositions // {
      Field = api.leaf {
        value = Field;
        description = "Field: parameterised position naming a record field by `name`; renders as `.<name>` in blame paths and carries `name` for downstream lookup by field-key.";
        signature = "Field : String -> Position";
      };
      Elem = api.leaf {
        value = Elem;
        description = "Elem: parameterised position naming a list element by `idx`; renders as `[<idx>]` in blame paths and carries `idx` for downstream lookup by integer index.";
        signature = "Elem : Int -> Position";
      };
      Tag = api.leaf {
        value = Tag;
        description = "Tag: parameterised position naming a tagged-union arm by `name`; renders as `#<name>` in blame paths and carries `name` for downstream lookup by variant tag.";
        signature = "Tag : String -> Position";
      };
      Tuple = api.leaf {
        value = Tuple;
        description = "Tuple: parameterised position naming a tuple component by static `idx`; renders identically to `Elem` (`[<idx>]`) but stays distinct so consumers tell n-ary tuple from list descent.";
        signature = "Tuple : Int -> Position";
      };
      DConLayer = api.leaf {
        value = DConLayer;
        description = "DConLayer: parameterised position naming the `layer`-th step in a peeled linear-recursive `desc-con` trampoline chain (0 = outermost, n = base); renders as `con[<layer>]`; quotient representative of homogeneous μ-unfolding paths so per-blame chain depth stays constant regardless of trampoline depth.";
        signature = "DConLayer : Int -> Position";
      };
      Case = api.leaf {
        value = Case;
        description = "Case: parameterised position naming an eliminator's case handler by `name` — generated constructor names, `\"inl\"`/`\"inr\"`, `\"base\"`, `\"onRet\"`/`\"onArg\"`/`\"onRec\"`/`\"onPi\"`/`\"onPlus\"`, `\"step\"`.";
        signature = "Case : String -> Position";
      };
      eq = api.leaf {
        value = eq;
        description = "eq: structural equality on `Position` values; relies on Nix's attrset-by-content comparison so equal positions compare equal regardless of construction path.";
        signature = "eq : Position -> Position -> Bool";
      };
      renderSegment = api.leaf {
        value = renderSegment;
        description = "renderSegment: render a `Position` as its short human-readable segment (`\"arg.S\"`, `\"plus.L\"`, `\".age\"`); single field read since the segment is carried on the Position itself.";
        signature = "renderSegment : Position -> String";
      };
      isPosition = api.leaf {
        value = isPosition;
        description = "isPosition: predicate recognising the `Position` ADT — checks `_tag == \"Position\"`; complements the `Layer`/`Error` predicates from `fx.diag.error`.";
        signature = "isPosition : Any -> Bool";
      };
      withRule = api.leaf {
        value = withRule;
        description = "withRule: decorate a `Position` with a descent-rule annotation, returning a structurally distinct Position whose `rule` field is set to the supplied string; leaves the original canonical constant intact for sharing.";
        signature = "withRule : String -> Position -> Position";
        doc = ''
          Use at the kernel-rule call site to record which rule emitted
          the descent — paired with `bindPR` to wrap the inner
          computation under a Position that carries both the structural
          coordinate (`tag`/`segment`/`intent`) and the rule identity.
          The hint resolver ignores `rule` (keys come from `tag` only),
          so decorating Positions never changes lookup.
        '';
      };
    };
}
