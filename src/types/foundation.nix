# nix-effects type system foundation
#
# Core type constructor (mkType) and operations. Every type is defined by
# its kernel representation (kernelType). All type operations are derived:
#
#   _tag = "Type"
#   name : String             — human-readable name
#   _kernel : HoasType        — kernel representation (the type IS this)
#   check : Value → Bool      — derived from decide(kernelType, value)
#   kernelCheck : Value → Bool — same as check (for legacy callers)
#   prove : HoasTerm → Bool   — kernel proof checking
#   validate : Value → Comp   — effectful check (sends typeCheck effect)
#   universe : Int             — derived from checkTypeLevel(kernelType)
#   description : String      — documentation
#
# The kernel type IS the type. check is its decision procedure, derived
# mechanically from the kernel via decide. No hand-written predicates.
# Universe levels are computed, not declared. This is the "one system"
# architecture — there is no separate contract system, no adequacy bridge,
# no possibility of disagreement between check and kernel.
#
# For refinement types, an optional `guard` adds a runtime predicate
# on top of the kernel check: check = decide(kernelType, v) && guard(v).
# The guard is NOT part of the kernel — it's a contract-level constraint
# that the kernel can't express (e.g., x >= 0 for natural numbers).
#
# Known constraint: builtins.tryEval only evaluates to WHNF.
# When catching handler throws, force .value on the result to trigger
# trampoline execution: builtins.tryEval ((fx.handle {...} comp).value).
# The outer {value; state;} attrset is constructed without forcing thunks.
#
# Grounded in Martin-Löf (1984) for universe-stratified structure,
# Freeman & Pfenning (1991) and Rondon et al. (2008) for refinement types,
# and Findler & Felleisen (2002) for higher-order contract checking.
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;
  inherit (api) mk;

  mkType = mk {
    doc = ''
      Create a type from its kernel representation.

      A nix-effects type is defined by its `kernelType` — an HOAS type tree
      representing the type in the MLTT kernel. All fields are derived:

      - `.check` = `decide(kernelType, v)` — the decision procedure
      - `.universe` = `checkTypeLevel(kernelType)` — computed universe level
      - `.kernelCheck` = same as `.check`
      - `.prove` = kernel proof checking for HOAS terms

      Arguments:

      - `name` — Human-readable type name
      - `kernelType` — HOAS type tree (required — this IS the type)
      - `guard` — Optional runtime predicate for refinement types.
        When provided, `.check = decide(kernelType, v) && guard(v)`.
        The guard is NOT part of the kernel — it handles constraints
        the kernel can't express (e.g., x >= 0 for Nat).
      - `verify` — Optional custom verifier (`self → value → Computation`).
        When null (default), `validate` is auto-derived by wrapping
        `check` in a `typeCheck` effect. Supply a custom `verify` for
        types that decompose checking (e.g. Sigma sends separate effects
        for `fst` and `snd` for blame tracking).
      - `description` — Documentation string (default = `name`)
      - `universe` — Optional universe level override. When null (default),
        computed from `checkTypeLevel(kernelType)`. Use when the kernelType
        is a fallback (e.g., `H.function_` for Pi) that doesn't capture the
        real universe level.
      - `approximate` — When true, the kernelType is a sound but lossy
        approximation (e.g., `H.function_` for Pi, `H.any` for Sigma).
        Suppresses `_kernel`, `kernelCheck`, and `prove` on the result,
        since the kernel representation doesn't precisely capture this type.
        The kernelType is still used internally for universe computation.
    '';
    value = { name, kernelType ? null, guard ? null, verify ? null, description ? name, universe ? null, approximate ? false }:
      let
        # Effective kernel type: when omitted, fall back to the weakest type.
        # Types without an explicit kernelType are always approximate.
        effectiveKernelType = if kernelType != null then kernelType else fx.tc.hoas.any;
        isApproximate = approximate || kernelType == null;

        # The kernel's decision procedure
        kernelDecide = v: fx.tc.elaborate.decide effectiveKernelType v;

        # .check: guard overrides decide when provided (for types where
        # the nix-effects value representation can't be elaborated to kernel
        # values — e.g., Record, Maybe, Variant, Universe). When null,
        # check is purely derived from the kernel via decide.
        # When kernelType is omitted (no kernel representation at all),
        # guard is required — otherwise check would use decide(H.any, v)
        # which accepts everything.
        effectiveCheck =
          if guard != null then guard
          else kernelDecide;

        # .universe: override if provided, otherwise computed from checkTypeLevel
        effectiveUniverse =
          if universe != null then universe
          else
            let
              tm = fx.tc.hoas.elab effectiveKernelType;
              result = fx.tc.check.runCheck
                (fx.tc.check.checkTypeLevel fx.tc.check.emptyCtx tm);
            in if result ? error then 0 else result.level;

        # Kernel fields: only present when kernelType is precise (not approximate).
        # When approximate (e.g., H.function_ for Pi, H.any for Sigma without
        # explicit kernelType), these are suppressed so that:
        #   - elaborateType can fall through to structural detection
        #   - callers know kernel checking is not available
        kernelFields =
          if isApproximate then {}
          else {
            _kernel = effectiveKernelType;
            kernelCheck = kernelDecide;
            prove = term:
              let result = builtins.tryEval (
                !((fx.tc.hoas.checkHoas effectiveKernelType term) ? error));
              in result.success && result.value;
          };

        self = {
          _tag = "Type";
          inherit name description;
          check = effectiveCheck;
          universe = effectiveUniverse;
          validate =
            if verify != null then verify self
            else v: send "typeCheck" { type = self; context = name; value = v; };
        } // kernelFields;
      in self;
    tests = let
      H = fx.tc.hoas;
    in {
      # -- Core construction --
      "creates-type" = {
        expr = (mkType.value { name = "Test"; kernelType = H.any; })._tag;
        expected = "Type";
      };
      "has-kernel" = {
        expr = (mkType.value { name = "T"; kernelType = H.bool; }) ? _kernel;
        expected = true;
      };
      "has-kernelCheck" = {
        expr = (mkType.value { name = "T"; kernelType = H.bool; }) ? kernelCheck;
        expected = true;
      };
      "has-prove" = {
        expr = (mkType.value { name = "T"; kernelType = H.bool; }) ? prove;
        expected = true;
      };
      "has-validate" = {
        expr = (mkType.value { name = "T"; kernelType = H.any; }) ? validate;
        expected = true;
      };
      # -- Derived check --
      "check-accepts-valid-bool" = {
        expr = (mkType.value { name = "Bool"; kernelType = H.bool; }).check true;
        expected = true;
      };
      "check-rejects-invalid-bool" = {
        expr = (mkType.value { name = "Bool"; kernelType = H.bool; }).check 42;
        expected = false;
      };
      "check-accepts-valid-string" = {
        expr = (mkType.value { name = "String"; kernelType = H.string; }).check "hello";
        expected = true;
      };
      "check-rejects-invalid-string" = {
        expr = (mkType.value { name = "String"; kernelType = H.string; }).check 42;
        expected = false;
      };
      "check-accepts-valid-nat" = {
        expr = (mkType.value { name = "Nat"; kernelType = H.nat; }).check 5;
        expected = true;
      };
      "check-rejects-negative-nat" = {
        expr = (mkType.value { name = "Nat"; kernelType = H.nat; }).check (-1);
        expected = false;
      };
      "check-any-accepts-all" = {
        expr =
          let t = mkType.value { name = "Any"; kernelType = H.any; };
          in t.check 42 && t.check "s" && t.check true && t.check null;
        expected = true;
      };
      # -- Derived universe --
      "universe-level-0" = {
        expr = (mkType.value { name = "Bool"; kernelType = H.bool; }).universe;
        expected = 0;
      };
      "universe-pi-level" = {
        expr = (mkType.value { name = "Arrow"; kernelType = H.forall "x" H.nat (_: H.bool); }).universe;
        expected = 0;
      };
      "universe-U0" = {
        expr = (mkType.value { name = "U0"; kernelType = H.u 0; }).universe;
        expected = 1;
      };
      # -- Guard (complete check override) --
      "guard-overrides-decide" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType.value {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in t.check 5;
        expected = true;
      };
      "guard-rejects" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType.value {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in t.check (-1);
        expected = false;
      };
      "guard-rejects-wrong-base-type" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType.value {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in t.check "not-an-int";
        expected = false;
      };
      "kernelCheck-ignores-guard" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType.value {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in t.kernelCheck (-1);  # kernel accepts (it's an int), guard would reject
        expected = true;
      };
      # -- Prove --
      "prove-accepts-valid" = {
        expr = (mkType.value { name = "Bool"; kernelType = H.bool; }).prove H.true_;
        expected = true;
      };
      "prove-rejects-wrong-type" = {
        expr = (mkType.value { name = "Bool"; kernelType = H.bool; }).prove H.zero;
        expected = false;
      };
      # -- Validate --
      "auto-validate-returns-impure" = {
        expr = ((mkType.value { name = "T"; kernelType = H.any; }).validate 42)._tag;
        expected = "Impure";
      };
      "auto-validate-effect-name" = {
        expr = ((mkType.value { name = "T"; kernelType = H.any; }).validate 42).effect.name;
        expected = "typeCheck";
      };
      "auto-validate-passes-type" = {
        expr =
          let t = mkType.value { name = "MyT"; kernelType = H.any; };
          in (t.validate 1).effect.param.type.name;
        expected = "MyT";
      };
      "verify-overrides-default" = {
        expr =
          let t = mkType.value {
            name = "Custom";
            kernelType = H.any;
            verify = _self: v: pure v;
          };
          in (t.validate 42)._tag;
        expected = "Pure";
      };
    };
  };

  check = mk {
    doc = "Check whether a value inhabits a type. Returns bool.";
    value = type: value: type.check value;
    tests = let H = fx.tc.hoas; in {
      "check-passes" = {
        expr = check.value (mkType.value { name = "Any"; kernelType = H.any; }) 42;
        expected = true;
      };
      "check-fails" = {
        expr = check.value (mkType.value { name = "Void"; kernelType = H.void; }) 42;
        expected = false;
      };
    };
  };

  make = mk {
    doc = "Validate a value and return it, or throw on failure.";
    value = type: v:
      if type.check v
      then v
      else builtins.throw "nix-effects type error: expected ${type.name}, got ${builtins.typeOf v}";
    tests = let H = fx.tc.hoas; in {
      "make-passes" = {
        expr = make.value (mkType.value { name = "Any"; kernelType = H.any; }) 42;
        expected = 42;
      };
    };
  };

  refine = mk {
    doc = ''
      Narrow a type with an additional predicate. Creates a refinement type
      whose check = decide(kernelType, v) AND predicate(v).
      The base type's kernelType provides the kernel backing; the predicate
      is a runtime-only guard the kernel cannot express.
      Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
    '';
    value = base: predicate: mkType.value {
      name = "${base.name}[refined]";
      kernelType = base._kernel;
      guard = v: base.check v && predicate v;
      description = "${base.description} (refined)";
    };
    tests = let H = fx.tc.hoas; in {
      "refine-narrows" = {
        expr =
          let
            int = mkType.value { name = "Int"; kernelType = H.int_; };
            nat = refine.value int (x: x >= 0);
          in check.value nat 5;
        expected = true;
      };
      "refine-rejects" = {
        expr =
          let
            int = mkType.value { name = "Int"; kernelType = H.int_; };
            nat = refine.value int (x: x >= 0);
          in check.value nat (-1);
        expected = false;
      };
    };
  };

  # -- Standalone effectful validation with explicit context --
  #
  # This is a convenience function for ad-hoc validation with a custom
  # context string. For typical use, call type.validate directly — mkType
  # auto-derives it. This 3-arg form is useful when you need to specify
  # a context string different from the type's name (e.g. for nested
  # validation in user code).

  validate = mk {
    doc = ''
      Standalone effectful validation with explicit context string.

      Sends a `typeCheck` effect with the given type, value, and context.
      The handler receives `{ type, context, value }` and determines the
      response: throw, collect error, log, or offer restarts.

      For typical use, prefer `type.validate` (auto-derived by `mkType`,
      uses the type's name as context). This 3-arg form is for cases
      where a custom context string is needed.

      ```
      validate : Type → Value → String → Computation Bool
      ```
    '';
    value = type: v: context:
      send "typeCheck" { inherit type context; value = v; };
    tests = let H = fx.tc.hoas; in {
      "validate-returns-impure" = {
        expr =
          let
            t = mkType.value { name = "Int"; kernelType = H.int_; };
          in (validate.value t 42 "test")._tag;
        expected = "Impure";
      };
      "validate-effect-name" = {
        expr =
          let
            t = mkType.value { name = "Int"; kernelType = H.int_; };
          in (validate.value t 42 "test").effect.name;
        expected = "typeCheck";
      };
      "validate-effect-has-type-and-context" = {
        expr =
          let
            t = mkType.value { name = "Int"; kernelType = H.int_; };
            comp = validate.value t 42 "test-ctx";
          in comp.effect.param.context;
        expected = "test-ctx";
      };
    };
  };

in mk {
  doc = "Type system foundation: Type constructor, check, validate, make, refine.";
  value = {
    inherit mkType check validate make refine;
    # Re-export kernel primitives for dependent contract modules
    inherit pure bind send;
  };
}
