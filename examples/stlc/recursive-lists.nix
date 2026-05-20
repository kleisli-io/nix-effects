# STLC recursive lists surface example.
#
# The kernel already has description-backed recursive datatypes. Lists are
# represented there as a generated `ListDT` whose carrier is a `mu` over a
# description. This example gives that machinery ordinary STLC syntax:
#
#   Type syntax:  List A
#   Terms:        nil
#                 cons h t
#   Eliminator:   listFold A R nilCase consCase xs
#
# There is no new recursive-type checker here. The surface forms elaborate to
# the existing HOAS `listOf`, `nil`, `cons`, and `listElim` combinators. In
# that sense, `nil` and `cons` are the fold/roll side of the iso-recursive
# story, and `listFold` is the unfold/elimination side.
#
# The interesting user-facing feature is omitted element types:
#
#   implicitNil
#   implicitCons zero (nil Nat)
#
# Both are ambiguous alone. When checked against `List Nat`, they solve their
# missing element type as `Nat` through the surface implicit-metavariable path.
{ fx, core, ... }:

let
  H = fx.types.hoas;
  S = fx.surface;
  C = fx.tc.check;
  E = fx.tc.eval;
  M = fx.tc.elaborate.meta;
  V = fx.tc.value;
  Core = core.stlc;

  # This example accepts both its own surface-level `List A` node and the
  # underlying HOAS `H.listOf A` spine as expected types.
  listElement = expectedType:
    if builtins.isAttrs expectedType && (expectedType._htag or null) == "stlc.list"
    then expectedType.elem
    else S.prelude.listElement expectedType;

  expectedListError = context: {
    error = {
      msg = "expected a List type";
      kind = "stlc.expected-list";
      position = context.position or null;
      expectedType = context.expectedType or null;
      term = context.term or null;
    };
    msg = "expected a List type";
    kind = "stlc.expected-list";
    position = context.position or null;
  };

  # Allocate and solve the implicit element type from an expected `List A`.
  #
  # The helper is separate from the handlers so the tests can inspect the
  # metavariable context directly: first a `Hole`, then a `Solved` entry whose
  # solution is the evaluated element type.
  implicitElementFromExpected = { context, label, hoas ? H }:
    let
      implicit = context.implicitMeta {
        type = { ctx = C.emptyCtx; ty = V.vU V.vLevelZero; };
        inherit label;
      };
      expectedType = context.expectedType or null;
      elem = if expectedType == null then null else listElement expectedType;
    in
    if expectedType == null
    then
      S.unsolvedImplicitError
        {
          metas = [{
            id = implicit.id;
            type = implicit.value.type;
            position = context.position or null;
          }];
          surface = context.surface or "STLC-RecursiveLists";
          term = context.term or null;
          position = context.position or null;
        }
    else if elem == null
    then expectedListError context
    else
      let
        elemVal = E.eval [ ] (hoas.elab elem);
        solvedState = M.solveMeta implicit.id elemVal implicit.state;
      in
      {
        inherit elem elemVal implicit solvedState;
      };

  surface = S.defineSurface {
    name = "STLC-RecursiveLists";
    description = "STLC surface extension for recursive lists.";
    constructors = {
      # `List A`.
      #
      # This is the user-level recursive type. It elaborates to the generated
      # HOAS list carrier, which is backed by the kernel's description `mu`.
      list = {
        tag = "stlc.list";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.listOf h.elem);
      };

      # Explicit empty list: `nil Nat`.
      nil = {
        tag = "stlc.nil";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.nilAtExplicit h.elem);
      };

      # Expected-type-driven empty list: `implicitNil`.
      implicitNil = {
        tag = "stlc.implicit-nil";
        handler = { context, depth, elaborate, hoas, ... }:
          let
            r = implicitElementFromExpected {
              inherit context hoas;
              label = "stlc.list-nil-element";
            };
          in
          if r ? error then r else elaborate depth (hoas.nilAtExplicit r.elem);
      };

      # Explicit cons: `cons Nat h t`.
      cons = {
        tag = "stlc.cons";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (hoas.consAtExplicit h.elem h.head h.tail);
      };

      # Expected-type-driven cons: `implicitCons h t`.
      #
      # The element type is omitted from the source term. Checking against
      # `List A` supplies it. The tail is still an ordinary term; callers can
      # use an explicit `nil A` or another typed list expression there.
      implicitCons = {
        tag = "stlc.implicit-cons";
        handler = { context, depth, h, elaborate, hoas, ... }:
          let
            r = implicitElementFromExpected {
              inherit context hoas;
              label = "stlc.list-cons-element";
            };
          in
          if r ? error then r else elaborate depth (hoas.consAtExplicit r.elem h.head h.tail);
      };

      # Non-dependent list fold.
      #
      # `listFold A R nilCase consCase xs` eliminates `xs : List A` into `R`.
      # `consCase` is a Nix function receiving:
      #
      #   head : A
      #   tail : List A
      #   ih   : R
      #
      # and returning the folded result for `cons head tail`.
      listFold = {
        tag = "stlc.list-fold";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth
            (hoas.listElim 0 h.elem
              (hoas.lam "_" (hoas.listOf h.elem) (_: h.result))
              h.onNil
              (hoas.lam "head" h.elem (head:
                hoas.lam "tail" (hoas.listOf h.elem) (tail:
                  hoas.lam "ih" h.result (ih:
                    h.onCons head tail ih))))
              h.scrut);
      };
    };
  };

  # Smart constructors for the recursive-list fragment.
  list = elem: surface.mk "list" { inherit elem; };
  nil = elem: surface.mk "nil" { inherit elem; };
  implicitNil = surface.mk "implicitNil" { };
  cons = elem: head: tail: surface.mk "cons" { inherit elem head tail; };
  implicitCons = head: tail: surface.mk "implicitCons" { inherit head tail; };
  listFold = elem: result: onNil: onCons: scrut:
    surface.mk "listFold" { inherit elem result onNil onCons scrut; };

  check = term: expectedType: position:
    S.elaborate {
      inherit surface term expectedType position;
    };

  # Addition over Nat, written directly in HOAS because arithmetic is not part
  # of the STLC surface being introduced here.
  add = lhs: rhs:
    H.ind 0 (H.lam "_" H.nat (_: H.nat)) rhs
      (H.lam "k" H.nat (_:
        H.lam "ih" H.nat (ih: H.succ ih)))
      lhs;

  one = H.natLit 1;
  three = H.natLit 3;
  listNat = list H.nat;

  explicitNilNat = nil H.nat;
  oneTwoList =
    cons H.nat one
      (cons H.nat (H.natLit 2) explicitNilNat);
  ones =
    cons H.nat one
      (cons H.nat one
        (cons H.nat one explicitNilNat));

  sumList = xs:
    listFold H.nat H.nat H.zero
      (head: _tail: ih: add head ih)
      xs;

  implicitContext = term: expectedType: position: {
    inherit expectedType position term;
    surface = "STLC-RecursiveLists";
    implicitMeta = metaArgs:
      S.implicitMeta (metaArgs // {
        position = metaArgs.position or position;
        surface = metaArgs.surface or "STLC-RecursiveLists";
      });
  };
in
rec {
  __example = {
    title = "STLC Recursive Lists";
    description = "List syntax and folds over description-backed recursive data.";
    introduction = ''
      Lists are already available in the HOAS layer as a generated recursive
      datatype. This surface gives them ordinary STLC syntax and shows how
      omitted element types can be solved from an expected `List A`.
    '';
    sections = [
      {
        title = "List constructors";
        prose = ''
          `List A`, `nil A`, and `cons A h t` translate to the generated HOAS
          list carrier and constructors.
        '';
        code = ''
          list = elem: surface.mk "list" { inherit elem; };
          nil = elem: surface.mk "nil" { inherit elem; };
          cons = elem: head: tail: surface.mk "cons" { inherit elem head tail; };

          explicitNilNat = nil H.nat;
          oneTwoList =
            cons H.nat one
              (cons H.nat (H.natLit 2) explicitNilNat);
        '';
        tests = [
          "stlcListNilChecks"
          "stlcListConsChecks"
        ];
      }
      {
        title = "Folding lists";
        prose = ''
          The fold form elaborates to `listElim` with a constant result type.
          The checked example computes the sum of `[1, 1, 1]` and proves the
          result is `3`.
        '';
        code = ''
          listFold = elem: result: onNil: onCons: scrut:
            surface.mk "listFold" { inherit elem result onNil onCons scrut; };

          sumList = xs:
            listFold H.nat H.nat H.zero
              (head: _tail: ih: add head ih)
              xs;

          stlcListFoldSumChecks =
            (H.checkHoas (H.eq H.nat (sumList ones) three) H.refl).tag == "desc-con";
        '';
        tests = [
          "stlcListFoldSumChecks"
          "stlcBadListFoldHasSurfaceBlame"
        ];
      }
      {
        title = "Element-type holes";
        prose = ''
          `implicitNil` and `implicitCons` allocate a surface metavariable for
          the missing element type. Checking against `List Nat` solves that
          metavariable as `Nat`.
        '';
        code = ''
          implicitElementFromExpected = { context, label, hoas ? H }:
            let
              implicit = context.implicitMeta {
                type = { ctx = C.emptyCtx; ty = V.vU V.vLevelZero; };
                inherit label;
              };
              expectedType = context.expectedType or null;
              elem = if expectedType == null then null else listElement expectedType;
            in
            if expectedType == null
            then S.unsolvedImplicitError { metas = [{ id = implicit.id; }]; }
            else if elem == null
            then expectedListError context
            else {
              inherit elem implicit;
              solvedState = M.solveMeta implicit.id (E.eval [ ] (hoas.elab elem)) implicit.state;
            };
        '';
        tests = [
          "stlcListImplicitNilSolvesElement"
          "stlcListImplicitConsSolvesElement"
        ];
      }
    ];
  };

  # Public extension API. It includes the core STLC vocabulary plus the list
  # forms introduced here.
  stlc = Core // {
    inherit surface list nil implicitNil cons implicitCons listFold;
  };

  # `nil Nat` checks against `List Nat`.
  stlcListNilChecks =
    let r = check explicitNilNat listNat { path = [ "list" "nil" ]; };
    in !(r ? error)
      && r.tag == "desc-con"
      && r.d.tag == "boot-inl";

  # `cons Nat 1 (cons Nat 2 (nil Nat))` checks against `List Nat`.
  stlcListConsChecks =
    let r = check oneTwoList listNat { path = [ "list" "cons" ]; };
    in !(r ? error)
      && r.tag == "desc-con"
      && r.d.tag == "boot-inr";

  # Folding `[1, 1, 1]` with addition computes `3`. This checks the
  # eliminator path, not just constructor typing.
  stlcListFoldSumChecks =
    (H.checkHoas (H.eq H.nat (sumList ones) three) H.refl).tag == "desc-con";

  # `implicitNil` solves its missing element type from `List Nat`.
  stlcListImplicitNilSolvesElement =
    let
      term = implicitNil;
      position = { path = [ "list" "implicit-nil" ]; };
      solved = implicitElementFromExpected {
        context = implicitContext term listNat position;
        label = "stlc.list-nil-element";
      };
      checked = check term listNat position;
    in
    !(checked ? error)
    && checked.tag == "desc-con"
    && solved.implicit.state.delta."0".tag == "Hole"
    && solved.solvedState.delta."0".tag == "Solved"
    && solved.solvedState.delta."0".tm.tag == "VMu";

  # `implicitCons 1 (nil Nat)` solves its missing element type from `List Nat`.
  stlcListImplicitConsSolvesElement =
    let
      term = implicitCons one explicitNilNat;
      position = { path = [ "list" "implicit-cons" ]; };
      solved = implicitElementFromExpected {
        context = implicitContext term listNat position;
        label = "stlc.list-cons-element";
      };
      checked = check term listNat position;
    in
    !(checked ? error)
    && checked.tag == "desc-con"
    && solved.implicit.state.delta."0".tag == "Hole"
    && solved.solvedState.delta."0".tag == "Solved"
    && solved.solvedState.delta."0".tm.tag == "VMu";

  # Folding over a Nat is invalid. The surface position survives the kernel
  # error, so diagnostics point at the source-level fold expression.
  stlcBadListFoldHasSurfaceBlame =
    let
      term = listFold H.nat H.nat H.zero
        (head: _tail: ih: add head ih)
        (Core.ann H.zero H.nat);
      r = check term H.nat { path = [ "bad" "list-fold" ]; };
    in
    (r ? error)
    && (r.position or null) == { path = [ "bad" "list-fold" ]; };
}
