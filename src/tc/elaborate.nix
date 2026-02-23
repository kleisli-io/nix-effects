# Type-checking kernel: Elaboration bridge
#
# Bridges fx.types (runtime predicates) to kernel types (de Bruijn Tm)
# via the HOAS surface combinator layer.
#
# Three layers:
#   elaborateType  : FxType → HoasTree    (type level)
#   elaborateValue : HoasTree → NixVal → HoasTree  (value level)
#   decide         : HoasTree → NixVal → Bool       (decision procedure)
#
# Annotated constructors (carry _kernel for auto-elaboration):
#   Bool, Nat, Unit, ListOf, Either, Arrow, Product, typeAt
#
# Adequacy invariant:
#   For each annotated type T and value v:
#     decide(elaborateType T, v) == T.check(v)
#
# Non-dependent Pi/Sigma are auto-detected via sentinel test.
# Dependent Pi/Sigma require explicit _kernel annotation or Phase 4 API.
#
# Spec reference: kernel-mvp-research.md §3
{ fx, api, ... }:

let
  inherit (api) mk;
  H = fx.tc.hoas;

  # -- Detection predicates for fx.types structural dispatch --

  # Pi types carry domain, codomain, checkAt from dependent.nix
  isPi = type:
    builtins.isAttrs type
    && type ? domain && type ? codomain && type ? checkAt;

  # Sigma types carry fstType, sndFamily, proj1 from dependent.nix
  isSigma = type:
    builtins.isAttrs type
    && type ? fstType && type ? sndFamily && type ? proj1;

  # Non-dependence test: call the family with two sentinels.
  # If result type names match, the family is constant.
  # LIMITATION (E3): builtins.tryEval only catches `throw` and `assert false`.
  # A type family that triggers boolean coercion errors, cross-type comparison
  # errors, or missing attribute access on sentinels will crash Nix rather than
  # returning false from isConstantFamily. This is an inherent limitation of
  # Nix's error model — there is no general-purpose exception catching.
  _s1 = { _tag = "Type"; name = "__elab_sentinel_1__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  _s2 = { _tag = "Type"; name = "__elab_sentinel_2__"; check = _: false; universe = 0; description = "sentinel"; validate = _: fx.kernel.pure null; };
  isConstantFamily = fn:
    let
      r1 = builtins.tryEval (fn _s1);
      r2 = builtins.tryEval (fn _s2);
    in r1.success && r2.success && r1.value.name == r2.value.name;

  # -- Type elaboration --
  #
  # Dispatches on:
  #   1. _kernel annotation (annotated types from this module)
  #   2. Structural fields (Pi: domain/codomain, Sigma: fstType/sndFamily)
  #   3. Name convention (Bool, Nat, Unit, Null)
  elaborateType = type:
    if !(builtins.isAttrs type) then
      throw "elaborateType: expected a type attrset"
    else if type ? _kernel then type._kernel
    else if isPi type then
      if isConstantFamily type.codomain
      then H.forall "x" (elaborateType type.domain) (_: elaborateType (type.codomain _s1))
      else throw "elaborateType: dependent Pi requires _kernel annotation"
    else if isSigma type then
      if isConstantFamily type.sndFamily
      then H.sigma "x" (elaborateType type.fstType) (_: elaborateType (type.sndFamily _s1))
      else throw "elaborateType: dependent Sigma requires _kernel annotation"
    else if type.name == "Bool" then H.bool
    else if type.name == "Nat" then H.nat
    else if type.name == "Unit" || type.name == "Null" then H.unit
    else throw "elaborateType: cannot elaborate '${type.name}' (add _kernel annotation)";

  # -- Value elaboration --
  #
  # Dispatches on HOAS type tag (_htag) to produce HOAS value tree.
  # Guards ensure clean throws (catchable by tryEval) for invalid values.
  elaborateValue = hoasTy: value:
    let t = hoasTy._htag or (throw "elaborateValue: not an HOAS type node"); in

    if t == "bool" then
      if !(builtins.isBool value)
      then throw "elaborateValue: Bool requires boolean, got ${builtins.typeOf value}"
      else if value then H.true_ else H.false_

    else if t == "nat" then
      if !(builtins.isInt value) || value < 0
      then throw "elaborateValue: Nat requires non-negative integer"
      else H.natLit value

    else if t == "unit" then
      if value != null
      then throw "elaborateValue: Unit requires null"
      else H.tt

    else if t == "list" then
      if !(builtins.isList value)
      then throw "elaborateValue: List requires a list"
      else
        let
          elemTy = hoasTy.elem;
          buildList = vs:
            if vs == [] then H.nil elemTy
            else H.cons elemTy
              (elaborateValue elemTy (builtins.head vs))
              (buildList (builtins.tail vs));
        in buildList value

    else if t == "sum" then
      if !(builtins.isAttrs value && value ? _tag && value ? value)
      then throw "elaborateValue: Sum requires { _tag = \"Left\"|\"Right\"; value = ...; }"
      else if value._tag == "Left"
      then H.inl hoasTy.left hoasTy.right (elaborateValue hoasTy.left value.value)
      else if value._tag == "Right"
      then H.inr hoasTy.left hoasTy.right (elaborateValue hoasTy.right value.value)
      else throw "elaborateValue: Sum _tag must be \"Left\" or \"Right\""

    else if t == "sigma" then
      if !(builtins.isAttrs value && value ? fst && value ? snd)
      then throw "elaborateValue: Sigma requires { fst; snd; }"
      else
        let
          # Guard: dependent sigma (body uses its argument) cannot be elaborated
          # from a plain Nix value — the second type depends on the first value's
          # HOAS representation, which we can't reconstruct here. Use explicit
          # _kernel annotation on the type for dependent sigma elaboration.
          _hs1 = { _htag = "nat"; _sentinel = 1; };
          _hs2 = { _htag = "nat"; _sentinel = 2; };
          r1 = builtins.tryEval (hoasTy.body _hs1);
          r2 = builtins.tryEval (hoasTy.body _hs2);
          sndTy =
            if r1.success && r2.success && r1.value == r2.value
            then r1.value
            else throw "elaborateValue: dependent Sigma requires explicit _kernel annotation";
        in H.pair
          (elaborateValue hoasTy.fst value.fst)
          (elaborateValue sndTy value.snd)
          hoasTy

    else throw "elaborateValue: unsupported type tag '${t}'";

  # -- Decision procedure --
  #
  # decide : HoasTree → NixValue → Bool
  # Returns true iff both elaboration and kernel type-checking succeed.
  # Uses tryEval to catch elaboration throws and checks for kernel errors.
  decide = hoasTy: value:
    let
      result = builtins.tryEval (
        let
          hoasVal = elaborateValue hoasTy value;
          checked = H.checkHoas hoasTy hoasVal;
        in !(checked ? error)
      );
    in result.success && result.value;

  # -- Convenience: elaborate type then decide --
  decideType = type: value:
    decide (elaborateType type) value;

  # -- Annotated type constructors --
  # Wrap fx.types with _kernel annotation for auto-elaboration.

  FP = fx.types.primitives;
  FC = fx.types.constructors;
  FD = fx.types.dependent;
  FU = fx.types.universe;
  FR = fx.types.refinement;

  Bool = FP.Bool // { _kernel = H.bool; };

  # Nat: refined Int (non-negative). Maps to kernel Peano Nat.
  Nat = (FR.refined "Nat" FP.Int (x: x >= 0)) // { _kernel = H.nat; };

  Unit = FP.Unit // { _kernel = H.unit; };

  # ListOf: wraps fx.types.constructors.ListOf with kernel annotation.
  ListOf = elemType:
    (FC.ListOf elemType) // { _kernel = H.listOf (elaborateType elemType); };

  # Either: wraps fx.types.constructors.Either with kernel annotation.
  Either = leftType: rightType:
    (FC.Either leftType rightType) // {
      _kernel = H.sum (elaborateType leftType) (elaborateType rightType);
    };

  # typeAt: wraps fx.types.universe.typeAt with kernel annotation.
  typeAtK = n: (FU.typeAt n) // { _kernel = H.u n; };

  # Arrow: non-dependent Pi (A → B) with kernel annotation.
  Arrow = domType: codType:
    (FD.Pi {
      domain = domType; codomain = _: codType;
      universe = if domType.universe >= codType.universe then domType.universe else codType.universe;
    }) // {
      _kernel = H.forall "x" (elaborateType domType) (_: elaborateType codType);
    };

  # Product: non-dependent Sigma (A × B) with kernel annotation.
  Product = fstType: sndType:
    (FD.Sigma {
      fst = fstType; snd = _: sndType;
      universe = if fstType.universe >= sndType.universe then fstType.universe else sndType.universe;
    }) // {
      _kernel = H.sigma "x" (elaborateType fstType) (_: elaborateType sndType);
    };

in mk {
  doc = ''
    Elaboration bridge: fx.types → kernel types.
    elaborateType converts fx.types to HOAS trees.
    elaborateValue converts Nix values to HOAS term trees.
    decide checks a value against a type via the kernel.
    Annotated constructors (Bool, Nat, etc.) carry _kernel annotation.
  '';
  value = {
    inherit elaborateType elaborateValue decide decideType;
    inherit Bool Nat Unit ListOf Either Arrow Product;
    typeAt = typeAtK;
  };
  tests = let
    # Shorthand for fx.types (unannotated, for auto-detection tests)
    IntT = FP.Int;
    BoolT = FP.Bool;
  in {
    # ===== Type elaboration: annotated constructors =====

    "elab-type-bool" = {
      expr = (elaborateType Bool)._htag;
      expected = "bool";
    };
    "elab-type-nat" = {
      expr = (elaborateType Nat)._htag;
      expected = "nat";
    };
    "elab-type-unit" = {
      expr = (elaborateType Unit)._htag;
      expected = "unit";
    };
    "elab-type-list-nat" = {
      expr = (elaborateType (ListOf Nat))._htag;
      expected = "list";
    };
    "elab-type-list-elem" = {
      expr = (elaborateType (ListOf Bool))._htag;
      expected = "list";
    };
    "elab-type-either" = {
      expr = (elaborateType (Either Nat Bool))._htag;
      expected = "sum";
    };
    "elab-type-arrow" = {
      expr = (elaborateType (Arrow Nat Bool))._htag;
      expected = "pi";
    };
    "elab-type-product" = {
      expr = (elaborateType (Product Nat Bool))._htag;
      expected = "sigma";
    };
    "elab-type-u0" = {
      expr = (elaborateType (typeAtK 0))._htag;
      expected = "U";
    };

    # ===== Type elaboration: auto-detection =====

    # Name-based: unannotated Bool detected by name
    "elab-type-auto-bool" = {
      expr = (elaborateType BoolT)._htag;
      expected = "bool";
    };

    # Structural: non-dependent Pi auto-detected
    "elab-type-auto-pi" = {
      expr = let
        piT = FD.Pi { domain = BoolT; codomain = _: IntT; universe = 0; };
      in (elaborateType piT)._htag;
      expected = "pi";
    };

    # Structural: non-dependent Sigma auto-detected
    "elab-type-auto-sigma" = {
      expr = let
        sigT = FD.Sigma { fst = BoolT; snd = _: IntT; universe = 0; };
      in (elaborateType sigT)._htag;
      expected = "sigma";
    };

    # ===== Value elaboration =====

    "elab-val-true" = {
      expr = (H.elab (elaborateValue H.bool true)).tag;
      expected = "true";
    };
    "elab-val-false" = {
      expr = (H.elab (elaborateValue H.bool false)).tag;
      expected = "false";
    };
    "elab-val-zero" = {
      expr = (H.elab (elaborateValue H.nat 0)).tag;
      expected = "zero";
    };
    "elab-val-nat-3" = {
      expr = (H.elab (elaborateValue H.nat 3)).tag;
      expected = "succ";
    };
    "elab-val-unit" = {
      expr = (H.elab (elaborateValue H.unit null)).tag;
      expected = "tt";
    };
    "elab-val-nil" = {
      expr = (H.elab (elaborateValue (H.listOf H.nat) [])).tag;
      expected = "nil";
    };
    "elab-val-cons" = {
      expr = (H.elab (elaborateValue (H.listOf H.nat) [0 1])).tag;
      expected = "cons";
    };
    "elab-val-inl" = {
      expr = (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Left"; value = 0; })).tag;
      expected = "inl";
    };
    "elab-val-inr" = {
      expr = (H.elab (elaborateValue (H.sum H.nat H.bool) { _tag = "Right"; value = true; })).tag;
      expected = "inr";
    };
    "elab-val-pair" = {
      expr = (H.elab (elaborateValue (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; })).tag;
      expected = "pair";
    };

    # ===== Decision procedure: positive =====

    "decide-bool-true" = {
      expr = decide H.bool true;
      expected = true;
    };
    "decide-bool-false" = {
      expr = decide H.bool false;
      expected = true;
    };
    "decide-nat-0" = {
      expr = decide H.nat 0;
      expected = true;
    };
    "decide-nat-5" = {
      expr = decide H.nat 5;
      expected = true;
    };
    "decide-unit" = {
      expr = decide H.unit null;
      expected = true;
    };
    "decide-list-empty" = {
      expr = decide (H.listOf H.nat) [];
      expected = true;
    };
    "decide-list-nat" = {
      expr = decide (H.listOf H.nat) [0 1 2];
      expected = true;
    };
    "decide-sum-left" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = 0; };
      expected = true;
    };
    "decide-sum-right" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Right"; value = true; };
      expected = true;
    };
    "decide-product" = {
      expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = 0; snd = true; };
      expected = true;
    };

    # ===== Decision procedure: negative =====

    "decide-bool-rejects-int" = {
      expr = decide H.bool 42;
      expected = false;
    };
    "decide-nat-rejects-neg" = {
      expr = decide H.nat (-1);
      expected = false;
    };
    "decide-nat-rejects-string" = {
      expr = decide H.nat "hello";
      expected = false;
    };
    "decide-list-rejects-wrong-elem" = {
      expr = decide (H.listOf H.nat) [true];
      expected = false;
    };
    "decide-sum-rejects-wrong-val" = {
      expr = decide (H.sum H.nat H.bool) { _tag = "Left"; value = true; };
      expected = false;
    };
    "decide-product-rejects-wrong-fst" = {
      expr = decide (H.sigma "x" H.nat (_: H.bool)) { fst = true; snd = true; };
      expected = false;
    };

    # Dependent sigma cleanly rejected (tryEval catches the throw)
    "decide-dep-sigma-rejected" = {
      expr = decide (H.sigma "x" H.nat (x: H.eq H.nat x H.zero)) { fst = 0; snd = null; };
      expected = false;
    };

    # ===== Adequacy: decide(T,v) == T.check(v) =====

    "adeq-bool-true" = {
      expr = (decideType Bool true) == (Bool.check true);
      expected = true;
    };
    "adeq-bool-rejects-int" = {
      expr = (decideType Bool 42) == (Bool.check 42);
      expected = true;
    };
    "adeq-nat-5" = {
      expr = (decideType Nat 5) == (Nat.check 5);
      expected = true;
    };
    "adeq-nat-rejects-neg" = {
      expr = (decideType Nat (-1)) == (Nat.check (-1));
      expected = true;
    };
    "adeq-unit-null" = {
      expr = (decideType Unit null) == (Unit.check null);
      expected = true;
    };
    "adeq-unit-rejects-42" = {
      expr = (decideType Unit 42) == (Unit.check 42);
      expected = true;
    };
    "adeq-list-nat-valid" = {
      expr = let lt = ListOf Nat; in (decideType lt [0 1 2]) == (lt.check [0 1 2]);
      expected = true;
    };
    "adeq-list-nat-empty" = {
      expr = let lt = ListOf Nat; in (decideType lt []) == (lt.check []);
      expected = true;
    };
    "adeq-list-nat-rejects-bad" = {
      expr = let lt = ListOf Nat; in (decideType lt [true]) == (lt.check [true]);
      expected = true;
    };
    "adeq-either-left-valid" = {
      expr = let et = Either Nat Bool; v = { _tag = "Left"; value = 0; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "adeq-either-right-bad" = {
      expr = let et = Either Nat Bool; v = { _tag = "Right"; value = 42; };
      in (decideType et v) == (et.check v);
      expected = true;
    };
    "adeq-product-valid" = {
      expr = let pt = Product Nat Bool; v = { fst = 0; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };
    "adeq-product-bad-fst" = {
      expr = let pt = Product Nat Bool; v = { fst = true; snd = true; };
      in (decideType pt v) == (pt.check v);
      expected = true;
    };
  };
}
