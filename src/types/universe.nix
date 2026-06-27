# Non-cumulative Tarski universe tower: Type_n holds types of universe exactly
# n, lifted across levels by `lift`/`liftTo`. See the `doc` entries below.
{ fx, api, ... }:
let
  inherit (fx.types.foundation) mkType check;

  # A type-as-value must expose the full Type interface, not merely the tag:
  # check/validate/name. NOT prove/kernelCheck — approximate Pi/Sigma legitimately
  # lack those (the kernel is suppressed when lossy), and universe membership does
  # not require a kernel-precise type.
  isType = v:
    builtins.isAttrs v && v ? _tag && v._tag == "Type"
    && v ? check && builtins.isFunction v.check
    && v ? validate && builtins.isFunction v.validate
    && v ? name && builtins.isString v.name;

  H = fx.tc.hoas;
  HII = fx.tc.hoas._internal._indexed;

  # A closed HOAS Level term `suc^n zero` for a Nix Int `n`.
  mkHoasLevel = n:
    builtins.foldl' (acc: _: H.levelSuc acc) H.levelZero (builtins.genList (x: x) n);

  typeAt = n:
    # `Type_n` has a precise kernel type (U(n)), but a type-as-value is not
    # decided by the kernel alone: `decide(U(n), v)` reads `v._kernel` and
    # verifies it is a type at level n, yet cannot see whether `v` is a real
    # nix-effects type at universe exactly n. So `check` is the conjunction
    # `decide(U(n), v) ∧ guard(v)` — the kernel verifies the level, the guard
    # verifies type-ness and the exact universe label. `_kernel`/`prove` are
    # kept (the kernel type IS U(n)); `kernelCheck` is removed, since a
    # kernel-only decision would mislead for type-as-value membership.
    removeAttrs
      (mkType {
        name = "Type_${toString n}";
        kernelType = H.u n;
        # Guard: complements the kernel decide, it does not replace it. The
        # kernel checks `v._kernel` sits at level n; the guard checks `v` is a
        # real type whose universe is exactly n (`== n` — the tower is
        # non-cumulative). The `v ? universe` check is a crash boundary:
        # without it, reading `v.universe` on a fake `_tag="Type"` attrset with
        # no universe field would crash Nix.
        guard = v: isType v && v ? universe && v.universe == n;
        universe = n + 1;
        description = "Universe level ${toString n}";
      }) [ "kernelCheck" ];

  # Explicit cross-level coercion: `liftTo m t` reindexes `t` to universe `m`
  # (require `m >= t.universe`), exposing the kernel `LiftAt` of its kernel
  # type. Values are unchanged — `check` is preserved — only the level moves.
  # Idempotent at `m == t.universe`. `lift` raises by one.
  liftTo = m: t:
    if m < t.universe
    then throw "cannot lift type '${t.name}' at universe ${toString t.universe} down to ${toString m}"
    else if m == t.universe then t
    else
      let
        lLvl = mkHoasLevel t.universe;
        mLvl = mkHoasLevel m;
        liftedKernel = HII.LiftAt lLvl mLvl t._kernel;
      in
      t // {
        universe = m;
        _kernel = liftedKernel;
      }
      # `prove` follows the kernel: a proof of the base carrier is lifted via
      # `liftAt` and checked against the lifted kernel, keeping `.prove` in sync
      # with `._kernel` (the inherited base `prove` would check the un-lifted
      # carrier). Only precise types carry `prove`; an approximate base has none
      # and the lift adds none.
      // (if t ? prove then {
        prove = a:
          let
            r = builtins.tryEval
              (!((H.checkHoas liftedKernel (HII.liftAt lLvl mLvl t._kernel a)) ? error));
          in
          r.success && r.value;
      } else { });

  lift = t: liftTo (t.universe + 1) t;

  Type_0 = typeAt 0;
  Type_1 = typeAt 1;
  Type_2 = typeAt 2;
  Type_3 = typeAt 3;
  Type_4 = typeAt 4;

  level = type: type.universe;

in
api.namespace {
  description = "Universe hierarchy: `typeAt n` produces `Type_n` in a non-cumulative Tarski tower; `lift`/`liftTo` coerce across levels; `Type_0`–`Type_4` are predefined; `level` reads a type's universe.";
  doc = "Universe hierarchy: Type_0 : Type_1 : Type_2 : ... Lazy infinite non-cumulative tower.";
  value = {
    typeAt = api.leaf {
      value = typeAt;
      description = "typeAt: factory producing the non-cumulative universe type `Type_n`; values of `Type_n` are types of universe exactly n; `Type_n` itself has universe `n+1`.";
      signature = "typeAt : Int -> Type";
      doc = ''
        Create universe type at level n (non-cumulative). `Type_n` contains
        exactly the types with universe `n` — a lower-level type is not subsumed,
        use `lift`/`liftTo` for the explicit coercion. `Type_n` itself has
        universe `n + 1`, enforcing `Type_n : Type_(n+1)` for all n and avoiding
        Russell's paradox.
      '';
      tests = {
        "type0-accepts-level0-type" = {
          expr =
            let IntType = mkType { name = "Int"; kernelType = H.int_; };
            in check (typeAt 0) IntType;
          expected = true;
        };
        "type0-rejects-itself" = {
          expr = check (typeAt 0) (typeAt 0);
          expected = false;
        };
        "type1-accepts-type0" = {
          # Type_0 has universe exactly 1, so it is a member of Type_1 — an
          # honest tower step, not cumulative subsumption.
          expr = check (typeAt 1) (typeAt 0);
          expected = true;
        };
        # Non-cumulative: a lower-level type is not subsumed into a higher
        # universe without an explicit lift.
        "type2-rejects-type0-noncumulative" = {
          expr = check (typeAt 2) (typeAt 0);
          expected = false;
        };
        "type1-rejects-level0-type-noncumulative" = {
          expr =
            let IntType = mkType { name = "Int"; kernelType = H.int_; };
            in check (typeAt 1) IntType;
          expected = false;
        };
        "no-self-membership" = {
          expr = check (typeAt 3) (typeAt 3);
          expected = false;
        };
        "has-kernel" = {
          expr = (typeAt 0) ? _kernel;
          expected = true;
        };
        "has-prove" = {
          expr = (typeAt 0) ? prove;
          expected = true;
        };
        "prove-accepts-nat-in-U0" = {
          expr = (typeAt 0).prove H.nat;
          expected = true;
        };
        "prove-accepts-bool-in-U0" = {
          expr = (typeAt 0).prove H.bool;
          expected = true;
        };
        "no-kernelCheck" = {
          # Types-as-values can't be elaborated
          expr = (typeAt 0) ? kernelCheck;
          expected = false;
        };
        "type0-rejects-type-without-validate" = {
          # A bare {_tag="Type"; …} carrying a valid kernel but missing the Type
          # interface (no `validate`) is not a real type — the tightened guard
          # rejects it even though its `_kernel` would pass the universe check.
          expr = check (typeAt 0) { _tag = "Type"; name = "fake"; check = _: true; universe = 0; _kernel = H.nat; };
          expected = false;
        };
      };
    };
    level = api.leaf {
      value = level;
      description = "level: read a type's universe level as an `Int`; level 0 covers atomic types, level 1 contains `Type_0`, and so on up the stratified tower. Throws (via `.universe`) when the type's level is term-dependent or level-polymorphic.";
      signature = "level : Type -> Int";
      doc = ''
        Get the universe level of a type. Equivalent to `.universe` field
        access; provided for explicit calls. Like `.universe`, it throws
        rather than fabricating a level when the type's universe is
        term-dependent or level-polymorphic (no ground `suc^n zero`).
      '';
      tests = {
        "level0-for-primitive" = {
          expr = level (mkType { name = "Int"; kernelType = H.int_; });
          expected = 0;
        };
        "level1-for-type0" = {
          expr = level Type_0;
          expected = 1;
        };
        "level2-for-type1" = {
          expr = level Type_1;
          expected = 2;
        };
      };
    };

    liftTo = api.leaf {
      value = liftTo;
      description = "liftTo: explicit cross-level coercion — `liftTo m t` reindexes type `t` to universe `m` (require `m >= t.universe`), preserving its values; idempotent at `m == t.universe`, throws when `m` is below `t`'s level.";
      signature = "liftTo : Int -> Type -> Type";
      doc = ''
        Reindex a type to a higher universe. `liftTo m t` has universe `m` and
        accepts exactly the values `t` accepts (`check` is preserved); its
        `_kernel` is the kernel `LiftAt` of `t`'s kernel type. Requires
        `m >= t.universe`; idempotent at `m == t.universe`. The non-cumulative
        tower has no implicit subsumption, so this is how a lower-level type
        becomes a member of a higher universe.
      '';
      tests = {
        "liftTo-raises-universe" = {
          expr = (liftTo 2 (mkType { name = "Int"; kernelType = H.int_; })).universe;
          expected = 2;
        };
        "liftTo-preserves-check" = {
          expr =
            let lifted = liftTo 2 (mkType { name = "Int"; kernelType = H.int_; });
            in lifted.check 5 && !(lifted.check "x");
          expected = true;
        };
        "liftTo-member-at-target" = {
          expr = check (typeAt 2) (liftTo 2 (mkType { name = "Int"; kernelType = H.int_; }));
          expected = true;
        };
        "liftTo-idempotent-at-equal-level" = {
          expr =
            let
              t = mkType { name = "Int"; kernelType = H.int_; };
              l = liftTo 0 t;
            in
            l.universe == 0 && l.check 5;
          expected = true;
        };
        "liftTo-rejects-lower-target" = {
          expr = (builtins.tryEval (liftTo 0 Type_1).universe).success;
          expected = false;
        };
        "liftTo-prove-checks-lifted-kernel" = {
          # `.prove` lifts the base proof and checks it against the lifted kernel,
          # staying in sync with `._kernel`.
          expr = (liftTo 2 (mkType { name = "Int"; kernelType = H.int_; })).prove (H.intLit 7);
          expected = true;
        };
        "liftTo-prove-rejects-non-member" = {
          expr = (liftTo 2 (mkType { name = "Int"; kernelType = H.int_; })).prove H.true_;
          expected = false;
        };
      };
    };
    lift = api.leaf {
      value = lift;
      description = "lift: raise a type by one universe — `lift t = liftTo (t.universe + 1) t`, preserving its values.";
      signature = "lift : Type -> Type";
      doc = "Raise a type by one universe level. `lift t = liftTo (t.universe + 1) t`. See `liftTo`.";
      tests = {
        "lift-raises-by-one" = {
          expr = (lift (mkType { name = "Int"; kernelType = H.int_; })).universe;
          expected = 1;
        };
        "lift-member-of-next-universe" = {
          expr = check (typeAt 1) (lift (mkType { name = "Int"; kernelType = H.int_; }));
          expected = true;
        };
      };
    };

    Type_0 = api.leaf { value = Type_0; description = "Type_0: first universe in the non-cumulative tower."; doc = "Predefined `Type_0` universe."; };
    Type_1 = api.leaf { value = Type_1; description = "Type_1: second universe in the non-cumulative tower."; doc = "Predefined `Type_1` universe."; };
    Type_2 = api.leaf { value = Type_2; description = "Type_2: third universe in the non-cumulative tower."; doc = "Predefined `Type_2` universe."; };
    Type_3 = api.leaf { value = Type_3; description = "Type_3: fourth universe in the non-cumulative tower."; doc = "Predefined `Type_3` universe."; };
    Type_4 = api.leaf { value = Type_4; description = "Type_4: fifth universe in the non-cumulative tower."; doc = "Predefined `Type_4` universe."; };

  };
}
