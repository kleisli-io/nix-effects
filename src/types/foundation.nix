# nix-effects type system foundation
#
# Core type constructor (mkType) and operations. Every type is defined by
# its kernel representation (kernelType). All type operations are derived:
#
#   _tag = "Type"
#   name : String              — human-readable name
#   _kernel : HoasType         — kernel representation (when not approximate)
#   _kernelPrecise : Bool      — true when kernel faithfully represents the type
#   _kernelSufficient : Bool   — true when kernel alone is sufficient for checking
#   check : Value → Bool       — derived from kernel and/or guard (see below)
#   kernelCheck : Value → Bool — kernel-only decision (when not approximate)
#   prove : HoasTerm → Bool    — kernel proof checking (when not approximate)
#   validate : Value → Comp    — effectful check (sends typeCheck effect)
#   universe : Int              — derived from checkTypeLevel(kernelType)
#   description : String       — documentation
#
# The relationship between the kernel type system (MLTT) and the contract
# layer (guards) is a Galois connection. The kernel provides a sound
# over-approximation: γ(α(T)) ⊇ T. The guard provides the residual
# constraints the kernel cannot express. Check is their intersection.
#
# Universal conjunction derivation based on `guard`:
#   - No guard: check = kernelDecide (kernel is sufficient)
#   - Guard: check = kernelDecide(v) ∧ guard(v) (conjunction —
#     kernel catches structural errors, guard handles residual constraints)
# Total elaboration (opaque lambda for Pi, HOAS substitution for Sigma)
# ensures kernelDecide never spuriously fails, eliminating the need for
# replacement mode.
#
# _kernelPrecise = !isApproximate. True when the kernel faithfully represents
# the type's structure. Parent constructors use this to build precise kernels.
# _kernelSufficient = !isApproximate && guard == null. True when the kernel
# alone decides membership — no guard residual needed.
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
        When present, `.check = kernelDecide(v) && guard(v)` (conjunction —
        kernel catches structural errors, guard handles residual constraints).
        The guard handles constraints the kernel can't express (e.g., x >= 0).
      - `verify` — Optional custom verifier (`self → path → value → Computation`).
        `path` is a list of string segments describing the structural
        descent from the validation root (e.g. `["a" "b" "c"]` for a
        nested field, `["[0]" "mtu"]` for a list element's field).
        When null (default), `validate` is auto-derived by wrapping
        `check` in a `typeCheck` effect. Supply a custom `verify` for
        types that decompose checking (e.g. Record sends separate
        effects per field for blame tracking).
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

        # .check: universal conjunction.
        # No guard: check = kernelDecide (kernel is sufficient).
        # Guard: check = kernelDecide(v) ∧ guard(v) — kernel catches
        #   structural errors, guard handles residual constraints.
        # Total elaboration (opaque lambda for Pi, HOAS substitution for
        # Sigma) ensures kernelDecide never spuriously fails.
        effectiveCheck =
          if guard == null then kernelDecide
          else v: kernelDecide v && guard v;

        # .universe: override if provided, otherwise computed from checkTypeLevel
        effectiveUniverse =
          if universe != null then universe
          else
            let
              tm = fx.tc.hoas.elab effectiveKernelType;
              result = fx.tc.check.runCheck
                (fx.tc.check.checkTypeLevel fx.tc.check.emptyCtx tm);
            in if result ? error then 0 else result.level;

        # _kernel is always exposed as the best kernel approximation, even for
        # approximate types. This lets constructors always build precise composed
        # kernels from children. kernelCheck and prove are only available when
        # the kernel is precise (not approximate) — they promise accuracy.
        kernelFields = {
          _kernel = effectiveKernelType;
        } // (if isApproximate then {} else {
          kernelCheck = kernelDecide;
          prove = term:
            let result = builtins.tryEval (
              !((fx.tc.hoas.checkHoas effectiveKernelType term) ? error));
            in result.success && result.value;
        });

        self = {
          _tag = "Type";
          _kernelPrecise = !isApproximate;
          _kernelSufficient = !isApproximate && guard == null;
          inherit name description;
          check = effectiveCheck;
          universe = effectiveUniverse;
          # validateAt path v — effectful check with accumulated path for
          # deep blame. validate v is the 1-arg convenience that starts
          # from an empty path. Constructors (Record, ListOf, Variant)
          # thread path through their recursive validateAt calls.
          # validateAt path positions v — effectful check with accumulated
          # path (string list for display) and positions (Position list for
          # structural descent). Constructors (Record, ListOf, Variant,
          # Sigma) thread both in lockstep; `positions` supplies the
          # `Field`/`Elem`/`Tag`/`SigmaFst`/`SigmaSnd` tags that pipe into
          # the emitted `diagError`. Primitives carry empty-chain positions
          # unless a constructor wraps them.
          validateAt =
            if verify != null then verify self
            else path: positions: v:
              let
                leafErr = fx.diag.error.mkGenericError {
                  type = name; context = name; value = v;
                  msg = "type check failed";
                };
                n = builtins.length positions;
                # Fold positions outer→inner around the leaf: for
                # positions = [p0, p1, ..., pk-1],
                #   diagError = nestUnder p0 (nestUnder p1 (... leaf))
                # so chainPositions (walking children[0]) reproduces
                # positions in the original descent order.
                diagError = builtins.foldl'
                  (err: i:
                    fx.diag.error.nestUnder
                      (builtins.elemAt positions (n - 1 - i)) err)
                  leafErr
                  (builtins.genList (x: x) n);
              in send "typeCheck" {
                type = self; context = name; value = v;
                inherit path positions diagError;
              };
          validate = v: self.validateAt [] [] v;
          diagnose = v: {
            kernel = kernelDecide v;
            guard = if guard != null then guard v else null;
            agreement = guard == null || (kernelDecide v) == (guard v);
          };
        } // kernelFields;
      in self;
    tests = let
      H = fx.tc.hoas;
    in {
      # -- Core construction --
      "creates-type" = {
        expr = (mkType { name = "Test"; kernelType = H.any; })._tag;
        expected = "Type";
      };
      "has-kernel" = {
        expr = (mkType { name = "T"; kernelType = H.bool; }) ? _kernel;
        expected = true;
      };
      "has-kernelCheck" = {
        expr = (mkType { name = "T"; kernelType = H.bool; }) ? kernelCheck;
        expected = true;
      };
      "has-prove" = {
        expr = (mkType { name = "T"; kernelType = H.bool; }) ? prove;
        expected = true;
      };
      "has-validate" = {
        expr = (mkType { name = "T"; kernelType = H.any; }) ? validate;
        expected = true;
      };
      # -- Derived check --
      "check-accepts-valid-bool" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).check true;
        expected = true;
      };
      "check-rejects-invalid-bool" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).check 42;
        expected = false;
      };
      "check-accepts-valid-string" = {
        expr = (mkType { name = "String"; kernelType = H.string; }).check "hello";
        expected = true;
      };
      "check-rejects-invalid-string" = {
        expr = (mkType { name = "String"; kernelType = H.string; }).check 42;
        expected = false;
      };
      "check-accepts-valid-nat" = {
        expr = (mkType { name = "Nat"; kernelType = H.nat; }).check 5;
        expected = true;
      };
      "check-rejects-negative-nat" = {
        expr = (mkType { name = "Nat"; kernelType = H.nat; }).check (-1);
        expected = false;
      };
      "check-any-accepts-all" = {
        expr =
          let t = mkType { name = "Any"; kernelType = H.any; };
          in t.check 42 && t.check "s" && t.check true && t.check null;
        expected = true;
      };
      # -- Derived universe --
      "universe-level-0" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).universe;
        expected = 0;
      };
      "universe-pi-level" = {
        expr = (mkType { name = "Arrow"; kernelType = H.forall "x" H.nat (_: H.bool); }).universe;
        expected = 0;
      };
      "universe-U0" = {
        expr = (mkType { name = "U0"; kernelType = H.u 0; }).universe;
        expected = 1;
      };
      # -- Guard (complete check override) --
      "guard-overrides-decide" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType {
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
            t = mkType {
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
            t = mkType {
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
            t = mkType {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in t.kernelCheck (-1);  # kernel accepts (it's an int), check would reject
        expected = true;
      };
      # -- _kernelPrecise / _kernelSufficient --
      "kernel-precise-when-not-approximate" = {
        expr = (mkType { name = "T"; kernelType = H.bool; })._kernelPrecise;
        expected = true;
      };
      "kernel-sufficient-when-no-guard" = {
        expr = (mkType { name = "T"; kernelType = H.bool; })._kernelSufficient;
        expected = true;
      };
      "kernel-precise-with-guard" = {
        expr = (mkType { name = "Pos"; kernelType = H.int_;
          guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
        })._kernelPrecise;
        expected = true;
      };
      "not-kernel-sufficient-with-guard" = {
        expr = (mkType { name = "Pos"; kernelType = H.int_;
          guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
        })._kernelSufficient;
        expected = false;
      };
      "not-kernel-precise-when-approximate" = {
        expr = (mkType { name = "T"; kernelType = null; })._kernelPrecise;
        expected = false;
      };
      "not-kernel-sufficient-when-approximate" = {
        expr = (mkType { name = "T"; kernelType = null; })._kernelSufficient;
        expected = false;
      };
      # -- Diagnose --
      "diagnose-agreement" = {
        expr =
          let t = mkType { name = "Pos"; kernelType = H.int_;
            guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
          };
          in (t.diagnose 5).agreement;
        expected = true;
      };
      "diagnose-kernel-accepts-guard-rejects" = {
        expr =
          let t = mkType { name = "Pos"; kernelType = H.int_;
            guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
          };
          d = t.diagnose (-1);
          in d.kernel == true && d.guard == false && d.agreement == false;
        expected = true;
      };
      "diagnose-no-guard" = {
        expr =
          let t = mkType { name = "T"; kernelType = H.bool; };
          d = t.diagnose true;
          in d.guard == null && d.agreement == true;
        expected = true;
      };
      "diagnose-both-reject" = {
        expr =
          let t = mkType { name = "Pos"; kernelType = H.int_;
            guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
          };
          d = t.diagnose "not-an-int";
          in d.kernel == false && d.guard == false && d.agreement == true;
        expected = true;
      };
      # -- Prove --
      "prove-accepts-valid" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).prove H.true_;
        expected = true;
      };
      "prove-rejects-wrong-type" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).prove H.zero;
        expected = false;
      };
      # -- Validate --
      "auto-validate-returns-impure" = {
        expr = fx.comp.isPure ((mkType { name = "T"; kernelType = H.any; }).validate 42);
        expected = false;
      };
      "auto-validate-effect-name" = {
        expr = ((mkType { name = "T"; kernelType = H.any; }).validate 42).effect.name;
        expected = "typeCheck";
      };
      "auto-validate-passes-type" = {
        expr =
          let t = mkType { name = "MyT"; kernelType = H.any; };
          in (t.validate 1).effect.param.type.name;
        expected = "MyT";
      };
      "verify-overrides-default" = {
        expr =
          let t = mkType {
            name = "Custom";
            kernelType = H.any;
            verify = _self: _path: _positions: v: pure v;
          };
          in fx.comp.isPure (t.validate 42);
        expected = true;
      };
      "auto-validate-carries-empty-path" = {
        expr = ((mkType { name = "T"; kernelType = H.any; }).validate 42).effect.param.path;
        expected = [];
      };
      "auto-validate-carries-empty-positions" = {
        expr = ((mkType { name = "T"; kernelType = H.any; }).validate 42).effect.param.positions;
        expected = [];
      };
      "validate-at-threads-path" = {
        expr =
          let t = mkType { name = "T"; kernelType = H.any; };
          in (t.validateAt [ "a" "b" ] [] 42).effect.param.path;
        expected = [ "a" "b" ];
      };
      "validate-at-threads-positions" = {
        expr =
          let
            t = mkType { name = "T"; kernelType = H.any; };
            Ps = [ (fx.diag.positions.Field "a") (fx.diag.positions.Elem 2) ];
          in (t.validateAt [ "a" "[2]" ] Ps 42).effect.param.positions;
        expected = [
          (fx.diag.positions.Field "a")
          (fx.diag.positions.Elem 2)
        ];
      };
      "default-emit-has-leaf-diagError" = {
        expr =
          let t = mkType { name = "T"; kernelType = H.any; };
          in (t.validate 42).effect.param.diagError.layer.tag;
        expected = "Generic";
      };
      "default-emit-diagError-chains-positions" = {
        expr =
          let
            t = mkType { name = "T"; kernelType = H.any; };
            P = fx.diag.positions;
            Ps = [ P.PiDom P.DArgSort ];
            err = (t.validateAt [ "dom" "arg.S" ] Ps 42).effect.param.diagError;
            # Walk children[0] from the outer wrapper to verify chain order.
            outerTag = (builtins.elemAt err.children 0).position.tag;
            innerTag = (builtins.elemAt
              ((builtins.elemAt err.children 0).error.children) 0).position.tag;
          in { outer = outerTag; inner = innerTag; };
        expected = { outer = "PiDom"; inner = "DArgSort"; };
      };
    };
  };

  check = mk {
    doc = "Check whether a value inhabits a type. Returns bool.";
    value = type: value:
      if type ? check then type.check value
      else if type ? value then check type.value value
      else type value;
    tests = let H = fx.tc.hoas; in {
      "check-passes" = {
        expr = check (mkType { name = "Any"; kernelType = H.any; }) 42;
        expected = true;
      };
      "check-fails" = {
        expr = check (mkType { name = "Void"; kernelType = H.void; }) 42;
        expected = false;
      };
    };
  };

  make = mk {
    doc = "Validate a value and return it, or throw on failure.";
    value = type: v:
      if type.check v
      then v
      else throw "nix-effects type error: expected ${type.name}, got ${builtins.typeOf v}";
    tests = let H = fx.tc.hoas; in {
      "make-passes" = {
        expr = make (mkType { name = "Any"; kernelType = H.any; }) 42;
        expected = 42;
      };
    };
  };

  refine = mk {
    doc = ''
      Narrow a type with an additional predicate. Creates a refinement type
      whose check = kernelDecide(v) ∧ guard(v) (conjunction).
      The base type's kernel provides structural checking; the guard handles
      the refinement predicate the kernel cannot express.
      Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
    '';
    value = base: predicate: mkType {
      name = "${base.name}[refined]";
      kernelType = base._kernel;
      guard = v: base.check v && predicate v;
      description = "${base.description} (refined)";
    };
    tests = let H = fx.tc.hoas; in {
      "refine-narrows" = {
        expr =
          let
            int = mkType { name = "Int"; kernelType = H.int_; };
            nat = refine int (x: x >= 0);
          in check nat 5;
        expected = true;
      };
      "refine-rejects" = {
        expr =
          let
            int = mkType { name = "Int"; kernelType = H.int_; };
            nat = refine int (x: x >= 0);
          in check nat (-1);
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
      send "typeCheck" { inherit type context; value = v; path = []; };
    tests = let H = fx.tc.hoas; in {
      "validate-returns-impure" = {
        expr =
          let
            t = mkType { name = "Int"; kernelType = H.int_; };
          in fx.comp.isPure (validate t 42 "test");
        expected = false;
      };
      "validate-effect-name" = {
        expr =
          let
            t = mkType { name = "Int"; kernelType = H.int_; };
          in (validate t 42 "test").effect.name;
        expected = "typeCheck";
      };
      "validate-effect-has-type-and-context" = {
        expr =
          let
            t = mkType { name = "Int"; kernelType = H.int_; };
            comp = validate t 42 "test-ctx";
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
