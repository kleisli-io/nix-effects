# nix-effects type system foundation
#
# Core type constructor (mkType) and operations. Every type is a
# (Specification, Guard, Verifier) triple:
#
#   _tag = "Type"
#   name : String             — specification (human-readable)
#   check : Value → Bool      — guard (pure, compositional)
#   validate : Value → Comp   — verifier (effectful, observable)
#   universe : Int            — universe level (0 for value types)
#   description : String      — documentation
#
# The guard (check) is the foundation — composite types compose by calling
# sub-type guards, which must be pure Bool returns. The verifier (validate)
# is auto-derived by mkType: it wraps check in a typeCheck effect for
# blame tracking. Types with decomposed checking (e.g. Sigma) supply a
# custom verifier via the `verify` parameter.
#
# Adequacy invariant: T.check v ⟺ all typeCheck effects in T.validate v pass
# Totality: validate is total where check is total. Structurally malformed
# inputs fail through the effect system, never crash Nix. Composite verifiers
# (Sigma, Pi, Certified) short-circuit on sub-check failure: dependent
# expressions (snd type family, function application, predicate evaluation)
# are never evaluated on wrong-typed inputs. This mirrors check's &&
# short-circuit behavior and prevents crashes in dependent type families.
#
# Per Pedrot & Tabareau "Fire Triangle" (POPL 2020):
#   Level 1: types as pure values (this attrset)
#   Level 2: type checking as effectful computation (validate)
#   Level 3: error policy as handler (strict/collecting/logging)
#
# Handler semantics (Level 3):
#   strict     — throws on first failure (abort semantics)
#   collecting — accumulates all errors in state (continues with false resume)
#   logging    — records all checks (pass and fail) for observability
#   all-pass   — boolean state tracking whether ALL checks passed;
#                canonical handler for testing the adequacy invariant
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
      Create a type as a (Specification, Guard, Verifier) triple.

      A nix-effects type is a tuple `(S, G, V)` where:

      ```
      S = Specification — the type-theoretic content (name, universe)
      G = Guard — a decidable pure predicate: check : Value → Bool
      V = Verifier — an effectful procedure: validate : Value → Computation Value
      ```

      Arguments:

      - `name` — Human-readable type name
      - `check` — Guard predicate (pure, compositional, used inside composite types)
      - `verify` — Optional custom verifier (`self → value → Computation`).
        Receives the type object (`self`) for structural failure
        reporting. When null (default), `validate` is auto-derived
        by wrapping `check` in a `typeCheck` effect. Supply a custom
        `verify` for types that decompose checking (e.g. Sigma sends
        separate effects for `fst` and `snd` for blame tracking).
      - `universe` — Universe level (default 0)
      - `description` — Documentation string (default = `name`)

      The auto-derived `validate` satisfies the adequacy invariant:

      ```
      T.check v ⟺ all typeCheck effects in T.validate v pass
      ```

      Tested via the all-pass handler:
      `state = state ∧ (param.type.check param.value)`

      The guard (`check`) is the foundation — pure, compositional, defines type
      membership. Composite types like Sigma compose by calling sub-type guards
      (`fst.check`, `snd.check`) which MUST be pure Bool returns. The verifier
      (`validate`) is built on top for observability — it sends `typeCheck` effects
      through the freer monad so handlers can implement blame tracking, error
      collection, or logging.

      Per Pedrot & Tabareau "Fire Triangle" (POPL 2020):

      ```
      Level 1: types as pure values (this attrset)
      Level 2: type checking as effectful computation (validate)
      Level 3: error policy as handler (strict/collecting/logging)
      ```
    '';
    value = { name, check, verify ? null, universe ? 0, description ? name, kernelType ? null }:
      let
        kernelFields =
          if kernelType != null then {
            _kernel = kernelType;
            kernelCheck = v: fx.tc.elaborate.decide kernelType v;
            prove = term:
              let result = builtins.tryEval (
                !((fx.tc.hoas.checkHoas kernelType term) ? error));
              in result.success && result.value;
          } else {};
        self = {
          _tag = "Type";
          inherit name check universe description;
          validate =
            if verify != null then verify self
            else v: send "typeCheck" { type = self; context = name; value = v; };
        } // kernelFields;
      in self;
    tests = {
      "creates-type" = {
        expr = (mkType.value { name = "Test"; check = _: true; })._tag;
        expected = "Type";
      };
      "default-universe-is-zero" = {
        expr = (mkType.value { name = "Test"; check = _: true; }).universe;
        expected = 0;
      };
      "has-validate" = {
        expr = (mkType.value { name = "T"; check = _: true; }) ? validate;
        expected = true;
      };
      "auto-validate-returns-impure" = {
        expr = ((mkType.value { name = "T"; check = _: true; }).validate 42)._tag;
        expected = "Impure";
      };
      "auto-validate-effect-name" = {
        expr = ((mkType.value { name = "T"; check = _: true; }).validate 42).effect.name;
        expected = "typeCheck";
      };
      "auto-validate-passes-type" = {
        expr =
          let t = mkType.value { name = "MyT"; check = _: true; };
          in (t.validate 1).effect.param.type.name;
        expected = "MyT";
      };
      "verify-overrides-default" = {
        expr =
          let t = mkType.value {
            name = "Custom";
            check = _: true;
            verify = _self: v: pure v;
          };
          in (t.validate 42)._tag;
        expected = "Pure";
      };
      "kernelType-absent-by-default" = {
        expr = (mkType.value { name = "T"; check = _: true; }) ? kernelCheck;
        expected = false;
      };
      "kernelType-adds-fields" = {
        expr = let
          H = fx.tc.hoas;
          t = mkType.value { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
        in t ? kernelCheck && t ? prove && t ? _kernel;
        expected = true;
      };
      "kernelCheck-accepts-valid" = {
        expr = let
          H = fx.tc.hoas;
          t = mkType.value { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
        in t.kernelCheck true;
        expected = true;
      };
      "kernelCheck-rejects-invalid" = {
        expr = let
          H = fx.tc.hoas;
          t = mkType.value { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
        in t.kernelCheck 42;
        expected = false;
      };
      "prove-accepts-valid" = {
        expr = let
          H = fx.tc.hoas;
          t = mkType.value { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
        in t.prove H.true_;
        expected = true;
      };
      "prove-rejects-wrong-type" = {
        expr = let
          H = fx.tc.hoas;
          t = mkType.value { name = "Bool"; check = builtins.isBool; kernelType = H.bool; };
        in t.prove H.zero;
        expected = false;
      };
    };
  };

  check = mk {
    doc = "Check whether a value inhabits a type. Returns bool.";
    value = type: value: type.check value;
    tests = {
      "check-passes" = {
        expr = check.value (mkType.value { name = "Any"; check = _: true; }) 42;
        expected = true;
      };
      "check-fails" = {
        expr = check.value (mkType.value { name = "Never"; check = _: false; }) 42;
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
    tests = {
      "make-passes" = {
        expr = make.value (mkType.value { name = "Any"; check = _: true; }) 42;
        expected = 42;
      };
    };
  };

  refine = mk {
    doc = ''
      Narrow a type with an additional predicate. Creates a refinement type
      whose check = base.check AND predicate.
      Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
    '';
    value = base: predicate: mkType.value {
      name = "${base.name}[refined]";
      check = v: base.check v && predicate v;
      inherit (base) universe;
      description = "${base.description} (refined)";
    };
    tests = {
      "refine-narrows" = {
        expr =
          let
            nat = refine.value
              (mkType.value { name = "Int"; check = builtins.isInt; })
              (x: x >= 0);
          in check.value nat 5;
        expected = true;
      };
      "refine-rejects" = {
        expr =
          let
            nat = refine.value
              (mkType.value { name = "Int"; check = builtins.isInt; })
              (x: x >= 0);
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
    tests = {
      "validate-returns-impure" = {
        expr =
          let
            t = mkType.value { name = "Int"; check = builtins.isInt; };
          in (validate.value t 42 "test")._tag;
        expected = "Impure";
      };
      "validate-effect-name" = {
        expr =
          let
            t = mkType.value { name = "Int"; check = builtins.isInt; };
          in (validate.value t 42 "test").effect.name;
        expected = "typeCheck";
      };
      "validate-effect-has-type-and-context" = {
        expr =
          let
            t = mkType.value { name = "Int"; check = builtins.isInt; };
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
