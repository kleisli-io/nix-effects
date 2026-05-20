# Position: shared diagnostic alphabet.
#
# A Position names a sub-location in a structural descent through a
# description (Desc) or through raw MLTT structure. It is pure data:
# no source locations, no human strings beyond the rendering helper,
# no behaviour.
#
# Positions are description-centric. `DArgSort` names the sort
# sub-position of `arg`; `DPlusL` names the left summand of `plus`;
# `PiDom` names the domain of `Π`. The same coordinate is meaningful
# to any walker of the same structure — a kernel rule checking an
# `arg`-shaped term, a fold visiting an `arg`-constructor of a Desc
# value, or a contract validator descending into a record field.
#
# No dependency on the type-checker or the types layer.
{ ... }:
let
  # Tagged-attrset constructor. `_tag = "Position"` is a nominal
  # marker used by `isPosition`; `tag` is the variant discriminator;
  # `segment` is the rendered path label. Keeping the segment on the
  # Position itself collapses `renderSegment` to an O(1) field read
  # and removes the ordering-sensitive `if/else-if` cascade, whose
  # per-hop cost used to scale with the branch position of the
  # matching tag.
  mkPos = tag: segment: extra:
    { _tag = "Position"; inherit tag segment; } // extra;

  # Positions naming sub-locations inside the five Desc constructors.
  DArgLevel = mkPos "DArgLevel" "arg.k" {};
  DArgSort  = mkPos "DArgSort"  "arg.S" {};
  DArgEq    = mkPos "DArgEq"    "arg.eq" {};
  DArgBody  = mkPos "DArgBody"  "arg.T" {};
  DPiLevel  = mkPos "DPiLevel"  "pi.k"  {};
  DPiSort   = mkPos "DPiSort"   "pi.S"  {};
  DPiEq     = mkPos "DPiEq"     "pi.eq" {};
  DPiFn     = mkPos "DPiFn"     "pi.f"  {};
  DPiBody   = mkPos "DPiBody"   "pi.T"  {};
  DElimLevel = mkPos "DElimLevel" "elim.k" {};
  DRetIndex = mkPos "DRetIndex" "ret.j" {};
  DRecIndex = mkPos "DRecIndex" "rec.j" {};
  DRecTail  = mkPos "DRecTail"  "rec.D" {};
  DPlusL    = mkPos "DPlusL"    "plus.L" {};
  DPlusR    = mkPos "DPlusR"    "plus.R" {};

  # Positions naming sub-locations in raw MLTT structure (outside Desc).
  PiDom    = mkPos "PiDom"    "Π.dom"   {};
  PiCod    = mkPos "PiCod"    "Π.cod"   {};
  SigmaFst = mkPos "SigmaFst" "Σ.fst"   {};
  SigmaSnd = mkPos "SigmaSnd" "Σ.snd"   {};
  AnnTerm  = mkPos "AnnTerm"  "ann.term" {};
  AnnType  = mkPos "AnnType"  "ann.type" {};
  MuUnroll = mkPos "MuUnroll" "μ"       {};
  AppHead  = mkPos "AppHead"  "app.head" {};
  AppArg   = mkPos "AppArg"   "app.arg"  {};

  # Term-side positions for binding-form bodies and the universal
  # CHECK→INFER sub-rule fallthrough. `LamBody` and `LetBody` name
  # the body slots of `lam` and `let` at the term level — distinct
  # from `PiCod` (the type-level codomain position) so blame chains
  # can carry both term-shape and type-shape information without
  # collapse. `Sub` names the catch-all subsumption bridge where
  # CHECK falls through to INFER + structural conv.
  LamBody = mkPos "LamBody" "lam.body" {};
  LetBody = mkPos "LetBody" "let.body" {};
  Sub     = mkPos "Sub"     "sub"      {};

  # Positions naming sub-locations inside eliminator rules — shared
  # across generated datatype eliminators, sum-elim, desc-elim, desc-ind, j.
  Scrut  = mkPos "Scrut"  "scrut"  {};
  Motive = mkPos "Motive" "motive" {};

  # Positions naming sub-locations inside the Mu-layer operations
  # (desc-con, desc-ind).
  MuDesc    = mkPos "MuDesc"    "con.D" {};
  MuIndex   = mkPos "MuIndex"   "con.i" {};
  MuPayload = mkPos "MuPayload" "con.d" {};

  # Positions naming sub-locations inside the `j` eliminator.
  JType = mkPos "JType" "J.A"  {};
  JLhs  = mkPos "JLhs"  "J.a"  {};
  JRhs  = mkPos "JRhs"  "J.b"  {};
  JEq   = mkPos "JEq"   "J.eq" {};

  # Opaque-lam's type annotation sub-position.
  OpaqueType = mkPos "OpaqueType" "opaque.type" {};

  # Positions naming sub-locations inside Level expressions.
  LevelSucPred = mkPos "LevelSucPred" "suc.pred" {};
  LevelMaxLhs  = mkPos "LevelMaxLhs"  "max.L"    {};
  LevelMaxRhs  = mkPos "LevelMaxRhs"  "max.R"    {};

  # Position naming the level argument of `U(k)`.
  ULevel = mkPos "ULevel" "U.k" {};

  # Parameterised positions for value-side descent through records,
  # lists, and tagged unions. Segment is computed from the parameter
  # at construction time; positions are long-lived per descent frame,
  # so the cost is amortised.
  Field = name: mkPos "Field" ("." + name)               { inherit name; };
  Elem  = idx:  mkPos "Elem"  ("[" + toString idx + "]") { inherit idx; };
  Tag   = name: mkPos "Tag"   ("#" + name)               { inherit name; };
  # Tuple component (statically-indexed product). Renders identically to
  # Elem ("[i]") but stays distinct at the position level so consumers can
  # tell n-ary tuple descent from list-element descent.
  Tuple = idx:  mkPos "Tuple" ("[" + toString idx + "]") { inherit idx; };

  # Layer coordinate for the homogeneous `desc-con` trampoline. Names
  # the k-th step in a peeled linear-recursive desc-con chain
  # (k = 0 outermost, k = n base). One segment compresses the
  # otherwise O(k × nFields) structural path
  # `(MuPayload → DPlusL|R → SigmaSnd^{nFields})^k`; the homogeneity
  # of the trampoline (same D, same plus-side, same nFields per layer)
  # makes layer depth the only varying coordinate. Mirrors `Elem`'s
  # shape (ℕ → Position) because the underlying object is the same:
  # a Nat-indexed coordinate into a sequence-like structure.
  DConLayer = layer: mkPos "DConLayer" ("con[" + toString layer + "]") { inherit layer; };

  # Parameterised position naming a case-handler inside an eliminator:
  # generated constructor names, "inl"/"inr" (sum-elim), "base" (j),
  # "onRet"/"onArg"/"onRec"/"onPi"/"onPlus" (desc-elim), "step"
  # (desc-ind).
  Case = name: mkPos "Case" ("@" + name) { inherit name; };

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

in {
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

  inherit Field Elem Tag Tuple DConLayer Case eq renderSegment isPosition;



  __docs = {
    _self = {
      doc = ''
    Shared diagnostic alphabet. Pure data.

    A Position names the blame location in a structural descent through
    a Desc or through raw MLTT structure (Π / Σ / Ann / μ / App). The
    alphabet is description-centric: names such as `DArgSort`, `DPlusL`,
    and `PiDom` identify sub-positions by their meaning in the structure,
    not by the code path that happens to visit them.

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
  };
    };

    Field = {
      description = "Field: parameterised position naming a record field by `name`; renders as `.<name>` in blame paths and carries `name` for downstream lookup by field-key.";
      signature = "Field : String -> Position";
    };
    Elem = {
      description = "Elem: parameterised position naming a list element by `idx`; renders as `[<idx>]` in blame paths and carries `idx` for downstream lookup by integer index.";
      signature = "Elem : Int -> Position";
    };
    Tag = {
      description = "Tag: parameterised position naming a tagged-union arm by `name`; renders as `#<name>` in blame paths and carries `name` for downstream lookup by variant tag.";
      signature = "Tag : String -> Position";
    };
    Tuple = {
      description = "Tuple: parameterised position naming a tuple component by static `idx`; renders identically to `Elem` (`[<idx>]`) but stays distinct so consumers tell n-ary tuple from list descent.";
      signature = "Tuple : Int -> Position";
    };
    DConLayer = {
      description = "DConLayer: parameterised position naming the `layer`-th step in a peeled linear-recursive `desc-con` trampoline chain (0 = outermost, n = base); renders as `con[<layer>]`; quotient representative of homogeneous μ-unfolding paths so per-blame chain depth stays constant regardless of trampoline depth.";
      signature = "DConLayer : Int -> Position";
    };
    Case = {
      description = "Case: parameterised position naming an eliminator's case handler by `name` — generated constructor names, `\"inl\"`/`\"inr\"`, `\"base\"`, `\"onRet\"`/`\"onArg\"`/`\"onRec\"`/`\"onPi\"`/`\"onPlus\"`, `\"step\"`.";
      signature = "Case : String -> Position";
    };
    eq = {
      description = "eq: structural equality on `Position` values; relies on Nix's attrset-by-content comparison so equal positions compare equal regardless of construction path.";
      signature = "eq : Position -> Position -> Bool";
    };
    renderSegment = {
      description = "renderSegment: render a `Position` as its short human-readable segment (`\"arg.S\"`, `\"plus.L\"`, `\".age\"`); single field read since the segment is carried on the Position itself.";
      signature = "renderSegment : Position -> String";
    };
    isPosition = {
      description = "isPosition: predicate recognising the `Position` ADT — checks `_tag == \"Position\"`; complements the `Layer`/`Error` predicates from `fx.diag.error`.";
      signature = "isPosition : Any -> Bool";
    };

  };
}
