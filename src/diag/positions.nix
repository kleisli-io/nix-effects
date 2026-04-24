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
{ api, ... }:

let
  inherit (api) mk;

  # Tagged-attrset constructor. `_tag = "Position"` is a nominal
  # marker used by `isPosition`; `tag` is the variant discriminator.
  mkPos = tag: extra: { _tag = "Position"; inherit tag; } // extra;

  # Positions naming sub-locations inside the five Desc constructors.
  DArgSort = mkPos "DArgSort" {};
  DArgBody = mkPos "DArgBody" {};
  DPiSort = mkPos "DPiSort" {};
  DPiFn   = mkPos "DPiFn" {};
  DPiBody = mkPos "DPiBody" {};
  DRetIndex = mkPos "DRetIndex" {};
  DRecIndex = mkPos "DRecIndex" {};
  DRecTail = mkPos "DRecTail" {};
  DPlusL = mkPos "DPlusL" {};
  DPlusR = mkPos "DPlusR" {};

  # Positions naming sub-locations in raw MLTT structure (outside Desc).
  PiDom = mkPos "PiDom" {};
  PiCod = mkPos "PiCod" {};
  SigmaFst = mkPos "SigmaFst" {};
  SigmaSnd = mkPos "SigmaSnd" {};
  AnnTerm = mkPos "AnnTerm" {};
  AnnType = mkPos "AnnType" {};
  MuUnroll = mkPos "MuUnroll" {};
  AppHead = mkPos "AppHead" {};
  AppArg = mkPos "AppArg" {};

  # Positions naming sub-locations inside eliminator rules — shared
  # across nat-elim, list-elim, sum-elim, desc-elim, desc-ind, j.
  Scrut = mkPos "Scrut" {};
  Motive = mkPos "Motive" {};

  # Positions naming sub-locations inside the Mu-layer operations
  # (desc-con, desc-ind).
  MuDesc = mkPos "MuDesc" {};
  MuIndex = mkPos "MuIndex" {};
  MuPayload = mkPos "MuPayload" {};

  # Positions naming sub-locations inside the `j` eliminator.
  JType = mkPos "JType" {};
  JLhs = mkPos "JLhs" {};
  JRhs = mkPos "JRhs" {};
  JEq = mkPos "JEq" {};

  # Opaque-lam's type annotation sub-position.
  OpaqueType = mkPos "OpaqueType" {};

  # Parameterised positions for value-side descent through records,
  # lists, and tagged unions.
  Field = name: mkPos "Field" { inherit name; };
  Elem = idx: mkPos "Elem" { inherit idx; };
  Tag = name: mkPos "Tag" { inherit name; };

  # Parameterised position naming a case-handler inside an eliminator:
  # "zero"/"succ" (nat-elim), "nil"/"cons" (list-elim), "inl"/"inr"
  # (sum-elim), "base" (j), "onRet"/"onArg"/"onRec"/"onPi"/"onPlus"
  # (desc-elim), "step" (desc-ind).
  Case = name: mkPos "Case" { inherit name; };

  # Structural equality works because Nix compares attrsets by
  # contents. `eq` is exposed for readers who prefer an explicit
  # function over `==`.
  eq = a: b: a == b;

  isPosition = x:
    builtins.isAttrs x
    && (x._tag or null) == "Position"
    && x ? tag;

  # Render a single position as a short human-readable segment.
  # Names are description-centric: "arg.S", "plus.L", ".age".
  renderSegment = pos:
    if pos.tag == "DArgSort" then "arg.S"
    else if pos.tag == "DArgBody" then "arg.T"
    else if pos.tag == "DPiSort" then "pi.S"
    else if pos.tag == "DPiFn" then "pi.f"
    else if pos.tag == "DPiBody" then "pi.T"
    else if pos.tag == "DRetIndex" then "ret.j"
    else if pos.tag == "DRecIndex" then "rec.j"
    else if pos.tag == "DRecTail" then "rec.D"
    else if pos.tag == "DPlusL" then "plus.L"
    else if pos.tag == "DPlusR" then "plus.R"
    else if pos.tag == "PiDom" then "Π.dom"
    else if pos.tag == "PiCod" then "Π.cod"
    else if pos.tag == "SigmaFst" then "Σ.fst"
    else if pos.tag == "SigmaSnd" then "Σ.snd"
    else if pos.tag == "AnnTerm" then "ann.term"
    else if pos.tag == "AnnType" then "ann.type"
    else if pos.tag == "MuUnroll" then "μ"
    else if pos.tag == "AppHead" then "app.head"
    else if pos.tag == "AppArg" then "app.arg"
    else if pos.tag == "Scrut" then "scrut"
    else if pos.tag == "Motive" then "motive"
    else if pos.tag == "MuDesc" then "con.D"
    else if pos.tag == "MuIndex" then "con.i"
    else if pos.tag == "MuPayload" then "con.d"
    else if pos.tag == "JType" then "J.A"
    else if pos.tag == "JLhs" then "J.a"
    else if pos.tag == "JRhs" then "J.b"
    else if pos.tag == "JEq" then "J.eq"
    else if pos.tag == "OpaqueType" then "opaque.type"
    else if pos.tag == "Field" then "." + pos.name
    else if pos.tag == "Elem" then "[" + toString pos.idx + "]"
    else if pos.tag == "Tag" then "#" + pos.name
    else if pos.tag == "Case" then "@" + pos.name
    else throw "diag.positions: unknown tag ${pos.tag}";

in mk {
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
  value = {
    inherit
      DArgSort DArgBody
      DPiSort DPiFn DPiBody
      DRetIndex
      DRecIndex DRecTail
      DPlusL DPlusR
      PiDom PiCod
      SigmaFst SigmaSnd
      AnnTerm AnnType
      MuUnroll
      AppHead AppArg
      Scrut Motive
      MuDesc MuIndex MuPayload
      JType JLhs JRhs JEq
      OpaqueType
      Field Elem Tag Case
      eq renderSegment isPosition;
  };
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
    "render-DArgBody" = {
      expr = renderSegment DArgBody;
      expected = "arg.T";
    };
    "render-DPiFn" = {
      expr = renderSegment DPiFn;
      expected = "pi.f";
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
    "render-Case" = {
      expr = renderSegment (Case "zero");
      expected = "@zero";
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
}
