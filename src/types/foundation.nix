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
  R = fx.tc.kernel.reflect;
  mkType = { name, kernelType ? null, guard ? null, verify ? null, description ? name, universe ? null, approximate ? false }:
    let
      # Effective kernel type: when omitted, fall back to the weakest type.
      # Types without an explicit kernelType are always approximate.
      effectiveKernelType = if kernelType != null then kernelType else fx.tc.hoas.any;
      isApproximate = approximate || kernelType == null;

      kernelDecide = v: fx.tc.elaborate.decide effectiveKernelType v;

      # A KernelPred guard derives its decision from the kernel predicate
      # stack; a raw guard is used directly. Hoisted so the dispatch runs once,
      # not once per checked value.
      effectiveGuard =
        if guard == null then null
        else if R.isKernelPred guard then R.deriveGuard guard
        else guard;

      # A KernelPred guard carries no source text; render it as a labelled
      # predicate so contract diagnostics stay clean.
      diagGuard =
        if guard == null then null
        else if R.isKernelPred guard then { predicate = "${name} (kernel-internalized)"; }
        else guard;

      # Total elaboration ensures kernelDecide never spuriously fails — no
      # replacement mode needed.
      effectiveCheck =
        if effectiveGuard == null then kernelDecide
        else v: kernelDecide v && effectiveGuard v;

      effectiveUniverse =
        if universe != null then universe
        else
          let
            tm = fx.tc.hoas.elab effectiveKernelType;
            result = fx.tc.check.runCheck
              (fx.tc.check.checkTypeLevel fx.tc.check.emptyCtx tm);
          in
          if result ? error then 0
          else
          # The level returned by checkTypeLevel can be a
          # `vLevelMax …` that only reduces to a concrete
          # `VLevelSuc^n VLevelZero` after the Level normaliser
          # runs (e.g. `Π Nat Nat` has level `max 0 0`).
          # Normalise first, then peel.
            let
              spine = fx.tc.conv.normLevel result.level;
            in
            if spine == [ ] then 0
            else if builtins.length spine == 1
              && (builtins.head spine).base.kind == "zero"
            then (builtins.head spine).shift
            else 0;

      # _kernel is always exposed as the best kernel approximation, even for
      # approximate types. This lets constructors always build precise composed
      # kernels from children. kernelCheck and prove are only available when
      # the kernel is precise (not approximate) — they promise accuracy.
      kernelFields = {
        _kernel = effectiveKernelType;
        # Authoritative kernel code for the internalizable fragment: a bare
        # carrier reflection when the kernel alone decides, the refined code
        # when the guard is a kernel-expressible witness, else null. Wrapped so
        # a stuck check degrades to null rather than poisoning construction.
        ktype =
          let
            r = builtins.tryEval (
              if isApproximate then null
              else if guard == null then R.reflect effectiveKernelType
              else if R.kernelExpressible guard then R.ktypeOf guard
              else null);
          in
          if r.success then r.value else null;
      } // (if isApproximate then { } else {
        kernelCheck = kernelDecide;
        prove = term:
          let
            result = builtins.tryEval (
              !((fx.tc.hoas.checkHoas effectiveKernelType term) ? error)
            );
          in
          result.success && result.value;
      });

      # Native-recursion budget per trampoline segment. validateAtF
      # descends natively while fuel remains, then defers the sub-walk
      # via a deriveBounce effect so deep contracts stay stack-safe.
      nativeWalkBudget = 512;

      self = {
        _tag = "Type";
        _kernelPrecise = !isApproximate;
        _kernelSufficient = !isApproximate && guard == null;
        # The kernel-expressible witness this type refines by, when any —
        # consumed by `refine`/`refined` to compose nested refinements.
        _kernelPred = if guard != null && R.isKernelPred guard then guard else null;
        inherit name description;
        check = effectiveCheck;
        universe = effectiveUniverse;
        # validateAt path v — effectful check with accumulated Position-
        # list path for deep blame. Constructors (Record, ListOf,
        # Variant, Sigma) thread `path` through their recursive
        # validateAt calls, appending the segment naming the descent
        # step (`Field name`, `Elem i`, `Tag name`, `SigmaFst`,
        # `SigmaSnd`). Primitives carry the inherited path unchanged.
        # `validate v` is the no-prefix convenience.
        # Auto-derived path emits `typeCheck` only on failure
        # (`!effectiveCheck v`). On pass, returns `pure v`. This matches
        # the canonical walker's emit-on-failure contract — consumers
        # treat `typeCheck` events as a failure-diagnostic stream, not
        # a blame log. Reason distinguishes kernel-rejection
        # (`shape-mismatch`) from guard-rejection (`predicate-failed`).
        validateAtF = fuel: path: v:
          if verify != null then verify self fuel path v
          else
            if effectiveCheck v then pure v
            else
              let
                reason =
                  if !(kernelDecide v) then "shape-mismatch"
                  else "predicate-failed";
                leafErr =
                  if reason == "predicate-failed"
                  then
                    fx.diag.error.mkContractError
                      {
                        type = name;
                        context = name;
                        value = v;
                        guard = diagGuard;
                        msg = "refinement check failed";
                      }
                  else
                    fx.diag.error.mkGenericError {
                      type = name;
                      context = name;
                      value = v;
                      msg = "type check failed";
                    };
                n = builtins.length path;
                # Fold positions outer→inner around the leaf: for
                # path = [p0, p1, ..., pk-1],
                #   diagError = nestUnder p0 (nestUnder p1 (... leaf))
                # so chainPositions (walking children[0]) reproduces
                # the descent in original order.
                diagError = builtins.foldl'
                  (err: i:
                    fx.diag.error.nestUnder
                      (builtins.elemAt path (n - 1 - i))
                      err)
                  leafErr
                  (builtins.genList (x: x) n);
              in
              send "typeCheck" {
                type = self;
                context = name;
                value = v;
                inherit reason path diagError;
              };
        # Public 2-arg entry: seed the native-recursion budget. Callers
        # and the verify alphabet are unchanged; fuel is threaded only
        # internally via validateAtF so recursive verifiers can bounce.
        validateAt = path: v: self.validateAtF nativeWalkBudget path v;
        validate = v: self.validateAt [ ] v;
        diagnose = v: {
          kernel = kernelDecide v;
          guard = if effectiveGuard != null then effectiveGuard v else null;
          agreement = effectiveGuard == null || (kernelDecide v) == (effectiveGuard v);
        };
      } // kernelFields;
    in
    self;

  mkTypeTests =
    let
      H = fx.tc.hoas;
      R = fx.tc.kernel.reflect;
      posInt = mkType { name = "PosInt"; kernelType = H.int_; guard = R.intPositive; };
    in
    {
      # Core construction
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
      # Derived check
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
      # Derived universe
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
      # Guard (complete check override)
      "guard-overrides-decide" = {
        expr =
          let
            decide = v: fx.tc.elaborate.decide H.int_ v;
            t = mkType {
              name = "Pos";
              kernelType = H.int_;
              guard = v: decide v && v > 0;
            };
          in
          t.check 5;
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
          in
          t.check (-1);
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
          in
          t.check "not-an-int";
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
          in
          t.kernelCheck (-1); # kernel accepts (it's an int), check would reject
        expected = true;
      };
      # _kernelPrecise / _kernelSufficient
      "kernel-precise-when-not-approximate" = {
        expr = (mkType { name = "T"; kernelType = H.bool; })._kernelPrecise;
        expected = true;
      };
      "kernel-sufficient-when-no-guard" = {
        expr = (mkType { name = "T"; kernelType = H.bool; })._kernelSufficient;
        expected = true;
      };
      "kernel-precise-with-guard" = {
        expr = (mkType {
          name = "Pos";
          kernelType = H.int_;
          guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
        })._kernelPrecise;
        expected = true;
      };
      "not-kernel-sufficient-with-guard" = {
        expr = (mkType {
          name = "Pos";
          kernelType = H.int_;
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
      # Diagnose
      "diagnose-agreement" = {
        expr =
          let
            t = mkType {
              name = "Pos";
              kernelType = H.int_;
              guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
            };
          in
          (t.diagnose 5).agreement;
        expected = true;
      };
      "diagnose-kernel-accepts-guard-rejects" = {
        expr =
          let
            t = mkType {
              name = "Pos";
              kernelType = H.int_;
              guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
            };
            d = t.diagnose (-1);
          in
          d.kernel == true && d.guard == false && d.agreement == false;
        expected = true;
      };
      "diagnose-no-guard" = {
        expr =
          let
            t = mkType { name = "T"; kernelType = H.bool; };
            d = t.diagnose true;
          in
          d.guard == null && d.agreement == true;
        expected = true;
      };
      "diagnose-both-reject" = {
        expr =
          let
            t = mkType {
              name = "Pos";
              kernelType = H.int_;
              guard = v: (fx.tc.elaborate.decide H.int_ v) && v > 0;
            };
            d = t.diagnose "not-an-int";
          in
          d.kernel == false && d.guard == false && d.agreement == true;
        expected = true;
      };
      # Prove
      "prove-accepts-valid" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).prove H.true_;
        expected = true;
      };
      "prove-rejects-wrong-type" = {
        expr = (mkType { name = "Bool"; kernelType = H.bool; }).prove H.zero;
        expected = false;
      };
      # Validate (fail-only emission)
      # Auto-derived validateAt emits `typeCheck` only when
      # `!effectiveCheck v` (kernel rejects or guard fails). On pass,
      # returns `pure v`. The test pairs below use `kernelType = H.bool`
      # with value `42` to drive the failure path; passing cases assert
      # the dual purity below.
      "auto-validate-passing-is-pure" = {
        expr = fx.comp.isPure ((mkType { name = "T"; kernelType = H.any; }).validate 42);
        expected = true;
      };
      "auto-validate-failing-is-impure" = {
        expr = fx.comp.isPure ((mkType { name = "T"; kernelType = H.bool; }).validate 42);
        expected = false;
      };
      "auto-validate-effect-name" = {
        expr = ((mkType { name = "T"; kernelType = H.bool; }).validate 42).effect.name;
        expected = "typeCheck";
      };
      "auto-validate-passes-type" = {
        expr =
          let t = mkType { name = "MyT"; kernelType = H.bool; };
          in (t.validate 42).effect.param.type.name;
        expected = "MyT";
      };
      "auto-validate-kernel-reject-shape-mismatch" = {
        expr = ((mkType { name = "T"; kernelType = H.bool; }).validate 42).effect.param.reason;
        expected = "shape-mismatch";
      };
      "auto-validate-guard-reject-predicate-failed" = {
        expr =
          let
            t = mkType {
              name = "PosInt";
              kernelType = H.int_;
              guard = v: builtins.isInt v && v > 0;
            };
          in
          (t.validate (-1)).effect.param.reason;
        expected = "predicate-failed";
      };
      "verify-overrides-default" = {
        expr =
          let
            t = mkType {
              name = "Custom";
              kernelType = H.any;
              verify = _self: _fuel: _path: v: pure v;
            };
          in
          fx.comp.isPure (t.validate 42);
        expected = true;
      };
      "auto-validate-carries-empty-path" = {
        expr = ((mkType { name = "T"; kernelType = H.bool; }).validate 42).effect.param.path;
        expected = [ ];
      };
      "validate-at-threads-path" = {
        expr =
          let
            t = mkType { name = "T"; kernelType = H.bool; };
            P = fx.diag.positions;
            p = [ (P.Field "a") (P.Elem 2) ];
          in
          (t.validateAt p 42).effect.param.path;
        expected = [
          (fx.diag.positions.Field "a")
          (fx.diag.positions.Elem 2)
        ];
      };
      "default-emit-has-leaf-diagError" = {
        expr =
          let t = mkType { name = "T"; kernelType = H.bool; };
          in (t.validate 42).effect.param.diagError.layer.tag;
        expected = "Generic";
      };
      "default-emit-diagError-chains-positions" = {
        expr =
          let
            t = mkType { name = "T"; kernelType = H.bool; };
            P = fx.diag.positions;
            err = (t.validateAt [ P.PiDom P.DArgSort ] 42).effect.param.diagError;
            # Walk children[0] from the outer wrapper to verify chain order.
            outerTag = (builtins.elemAt err.children 0).position.tag;
            innerTag = (builtins.elemAt
              ((builtins.elemAt err.children 0).error.children) 0).position.tag;
          in
          { outer = outerTag; inner = innerTag; };
        expected = { outer = "PiDom"; inner = "DArgSort"; };
      };
      # Predicate-failed values have the shape but violate the refinement
      # guard, so they belong on the Contract layer and must carry the
      # rejecting predicate.
      "predicate-failed-emits-contract-layer" = {
        expr =
          let
            t = mkType {
              name = "PosInt";
              kernelType = H.int_;
              guard = v: builtins.isInt v && v > 0;
            };
          in
          (t.validate (-1)).effect.param.diagError.layer.tag;
        expected = "Contract";
      };
      "predicate-failed-carries-guard" = {
        expr =
          let
            t = mkType {
              name = "PosInt";
              kernelType = H.int_;
              guard = v: builtins.isInt v && v > 0;
            };
            d = (t.validate (-1)).effect.param.diagError.detail;
          in
          d.guard != null;
        expected = true;
      };
      "shape-mismatch-stays-generic" = {
        expr =
          let
            t = mkType {
              name = "PosInt";
              kernelType = H.int_;
              guard = v: builtins.isInt v && v > 0;
            };
            # "abc" is not an int, so kernel rejects before the guard runs.
          in
          (t.validate "abc").effect.param.diagError.layer.tag;
        expected = "Generic";
      };
      # KernelPred guard: check derives from the kernel predicate term
      "kernelpred-accepts" = { expr = posInt.check 5; expected = true; };
      "kernelpred-rejects-zero" = { expr = posInt.check 0; expected = false; };
      "kernelpred-rejects-negative" = { expr = posInt.check (-3); expected = false; };
      "kernelpred-rejects-noncarrier" = { expr = posInt.check "x"; expected = false; };
      "kernelpred-diagnose-no-throw" = {
        expr = let d = posInt.diagnose (-1); in d.kernel == true && d.guard == false && d.agreement == false;
        expected = true;
      };
      # ktype gate arms
      "ktype-approximate-null" = { expr = (mkType { name = "A"; kernelType = null; }).ktype == null; expected = true; };
      "ktype-sufficient-nonnull" = { expr = (mkType { name = "B"; kernelType = H.bool; }).ktype != null; expected = true; };
      "ktype-rawlambda-null" = {
        expr = (mkType { name = "P"; kernelType = H.int_; guard = v: builtins.isInt v && v > 0; }).ktype == null;
        expected = true;
      };
      "ktype-kernelpred-nonnull" = { expr = posInt.ktype != null; expected = true; };
      # _kernelPred exposure
      "kernelpred-exposed" = { expr = R.isKernelPred posInt._kernelPred; expected = true; };
      "kernelpred-null-for-rawlambda" = {
        expr = (mkType { name = "P"; kernelType = H.int_; guard = v: v > 0; })._kernelPred == null;
        expected = true;
      };
      # Contract diagnostics stay clean under a KernelPred guard
      "kernelpred-predicate-failed-contract-layer" = {
        expr = (posInt.validate (-1)).effect.param.diagError.layer.tag;
        expected = "Contract";
      };
      "kernelpred-predicate-failed-renders" = {
        expr = (posInt.validate (-1)).effect.param.diagError.detail.guard ? predicate;
        expected = true;
      };
    };

  defEq = A: B:
    fx.tc.conv.conv 0
      (fx.tc.eval.eval [ ] (fx.tc.hoas.elab A._kernel))
      (fx.tc.eval.eval [ ] (fx.tc.hoas.elab B._kernel));

  defEqTests = let H = fx.tc.hoas; in {
    "defEq-refl" = {
      expr =
        let t = mkType { name = "T"; kernelType = H.int_; };
        in defEq t t;
      expected = true;
    };
    "defEq-rejects-distinct-kernels" = {
      expr =
        let
          a = mkType { name = "A"; kernelType = H.int_; };
          b = mkType { name = "B"; kernelType = H.bool; };
        in
        defEq a b;
      expected = false;
    };
    "defEq-ignores-meta-name" = {
      expr =
        let
          a = mkType { name = "Foo"; kernelType = H.int_; };
          b = mkType { name = "Bar"; kernelType = H.int_; };
        in
        defEq a b;
      expected = true;
    };
  };

  check = type: value:
    if type ? check then type.check value
    else if type ? value then check type.value value
    else type value;

  checkTests = let H = fx.tc.hoas; in {
    "check-passes" = {
      expr = check (mkType { name = "Any"; kernelType = H.any; }) 42;
      expected = true;
    };
    "check-fails" = {
      expr = check (mkType { name = "Void"; kernelType = H.void; }) 42;
      expected = false;
    };
  };

  make = type: v:
    if type.check v
    then v
    else throw "nix-effects type error: expected ${type.name}, got ${builtins.typeOf v}";

  makeTests = let H = fx.tc.hoas; in {
    "make-passes" = {
      expr = make (mkType { name = "Any"; kernelType = H.any; }) 42;
      expected = 42;
    };
  };

  # Compose a refinement guard. A kernel-expressible witness is threaded into
  # the guard slot (its check derived from the kernel term), composed with the
  # base's own witness when present; a raw predicate stays an opaque lambda.
  refineGuard = base: predicate:
    if R.isKernelPred predicate then
      (if (base._kernelPred or null) != null
      then R.andKP base._kernelPred predicate
      else predicate)
    else v: base.check v && predicate v;

  refine = base: predicate: mkType {
    name = "${base.name}[refined]";
    kernelType = base._kernel;
    guard = refineGuard base predicate;
    description = "${base.description} (refined)";
  };

  refineTests = let H = fx.tc.hoas; R = fx.tc.kernel.reflect; in {
    "refine-narrows" = {
      expr =
        let
          int = mkType { name = "Int"; kernelType = H.int_; };
          nat = refine int (x: x >= 0);
        in
        check nat 5;
      expected = true;
    };
    "refine-rejects" = {
      expr =
        let
          int = mkType { name = "Int"; kernelType = H.int_; };
          nat = refine int (x: x >= 0);
        in
        check nat (-1);
      expected = false;
    };
    # A KernelPred predicate threads into the guard slot; check derives from
    # the kernel term and ktype is non-null.
    "refine-kernelpred-narrows" = {
      expr =
        let int = mkType { name = "Int"; kernelType = H.int_; };
        in check (refine int R.intPositive) 5;
      expected = true;
    };
    "refine-kernelpred-rejects" = {
      expr =
        let int = mkType { name = "Int"; kernelType = H.int_; };
        in check (refine int R.intPositive) 0;
      expected = false;
    };
    "refine-kernelpred-ktype" = {
      expr =
        let int = mkType { name = "Int"; kernelType = H.int_; };
        in (refine int R.intPositive).ktype != null;
      expected = true;
    };
    # Nested KernelPred refinements compose via andKP: the composite conjoins
    # both predicates and keeps a non-null ktype.
    "refine-kernelpred-composition" = {
      expr =
        let
          int = mkType { name = "Int"; kernelType = H.int_; };
          t = refine (refine int R.intNonNegative) (R.intInRange 0 10);
        in
        [ (check t 5) (check t (-1)) (check t 20) ];
      expected = [ true false false ];
    };
    "refine-kernelpred-composition-ktype" = {
      expr =
        let
          int = mkType { name = "Int"; kernelType = H.int_; };
          t = refine (refine int R.intNonNegative) (R.intInRange 0 10);
        in
        t.ktype != null;
      expected = true;
    };
  };

  # Convenience: ad-hoc typeCheck emission with explicit context; prefer
  # type.validate for normal use.
  validate = type: v: context:
    send "typeCheck" {
      inherit type context; value = v;
      path = [ ];
      reason = "shape-mismatch";
    };

  validateTests = let H = fx.tc.hoas; in {
    "validate-returns-impure" = {
      expr =
        let
          t = mkType { name = "Int"; kernelType = H.int_; };
        in
        fx.comp.isPure (validate t 42 "test");
      expected = false;
    };
    "validate-effect-name" = {
      expr =
        let
          t = mkType { name = "Int"; kernelType = H.int_; };
        in
        (validate t 42 "test").effect.name;
      expected = "typeCheck";
    };
    "validate-effect-has-type-and-context" = {
      expr =
        let
          t = mkType { name = "Int"; kernelType = H.int_; };
          comp = validate t 42 "test-ctx";
        in
        comp.effect.param.context;
      expected = "test-ctx";
    };
  };

in
api.namespace {
  description = "Type system foundation: `mkType`/`check`/`validate`/`make`/`refine` build types from kernel HOAS representations and the guard/effect machinery underneath.";
  doc = "Type system foundation: Type constructor, check, validate, make, refine.";
  value = {
    mkType = api.leaf {
      value = mkType;
      description = "mkType: foundation type constructor; builds a `nix-effects` type from a kernel HOAS representation plus optional guard/verify/universe/approximate flags.";
      signature = "mkType : { name, kernelType ? null, guard ? null, verify ? null, description ? name, universe ? null, approximate ? false } -> Type";
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
        - `verify` — Optional custom verifier
          (`self → fuel → path → value → Computation`).
          `fuel` is the native-recursion budget: recursive verifiers
          descend natively while it is positive and defer the sub-walk
          via a `deriveBounce` effect when it runs out, keeping deep
          structures stack-safe. Non-recursive verifiers ignore it.
          `path` is a list of `fx.diag.positions` Position records
          describing the structural descent from the validation root
          (e.g. `[(P.Field "a") (P.Field "b")]` for a nested field,
          `[(P.Elem 0) (P.Field "mtu")]` for a list element's field).
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
      tests = mkTypeTests;
    };
    defEq = api.leaf {
      value = defEq;
      description = "defEq: definitional equality on types; true iff the kernel-conversion judgment `Γ ⊢ A._kernel ≡ B._kernel` holds under β/η/ι/μ reduction.";
      signature = "defEq : Type -> Type -> Bool";
      doc = ''
        Definitional equality on types. This is the type-theoretic
        equality that decides when two type expressions denote the same
        type:

            conv 0 (eval [] (elab A._kernel)) (eval [] (elab B._kernel))

        Strictly stronger than meta-language `==` on `_kernel`: Nix `==`
        only coincides with conv when the encoding contains no closures.
        After the description-backed migration of Record/Variant/Certified,
        `(H.datatype …).T` carries Pi-binder closures and per-call fresh
        thunks; `==` on those kernels is no longer a sound proxy for
        type equality. `defEq` is the correct predicate.

        Grounded in Martin-Löf (1984), section 6, and standard NbE conversion
        (Abel et al. 2007).
      '';
      tests = defEqTests;
    };
    check = api.leaf {
      value = check;
      description = "check: predicate that asks whether `value` inhabits `type`; returns the type's guarded kernel decision as a Bool, never throws.";
      signature = "check : Type -> Value -> Bool";
      doc = "Check whether a value inhabits a type. Pure — returns a Bool. The dual of `make`, which throws on failure.";
      tests = checkTests;
    };
    make = api.leaf {
      value = make;
      description = "make: assert-and-return; runs `type.check` on the value, returning it on success or throwing a `nix-effects type error` on failure.";
      signature = "make : Type -> Value -> Value";
      doc = "Validate a value and return it, or throw on failure. The throwing dual of `check`.";
      tests = makeTests;
    };
    refine = api.leaf {
      value = refine;
      description = "refine: narrow a base type with an extra predicate; returns a refined `Type` whose `check` conjoins kernel decision with the supplied guard.";
      signature = "refine : Type -> (Value -> Bool) -> Type";
      doc = ''
        Narrow a type with an additional predicate. Creates a refinement type
        whose check = kernelDecide(v) ∧ guard(v) (conjunction).
        The base type's kernel provides structural checking; the guard handles
        the refinement predicate the kernel cannot express.
        Grounded in Freeman & Pfenning (1991) "Refinement Types for ML" and Rondon et al. (2008) "Liquid Types".
      '';
      tests = refineTests;
    };
    refineGuard = api.leaf {
      value = refineGuard;
      description = "refineGuard: build a refinement type's guard slot from a base type and a predicate; a KernelPred witness yields a kernel-derived (authoritative) guard composed with the base's witness, a raw predicate stays an opaque lambda conjoined with `base.check`.";
      signature = "refineGuard : Type -> (Value -> Bool | KernelPred) -> (Value -> Bool | KernelPred)";
      doc = "Shared by `refine` and `refinement.refined` so both compose guards identically. A `KernelPred` predicate is threaded through (and `andKP`-composed with `base._kernelPred`); a raw predicate becomes `v: base.check v && predicate v`.";
    };
    validate = api.leaf {
      value = validate;
      description = "validate: emit a standalone `typeCheck` effect with an explicit `context` string for ad-hoc validation; prefer `type.validate` unless overriding context.";
      signature = "validate : Type -> Value -> String -> Computation Bool";
      doc = ''
        Standalone effectful validation with explicit context string.

        Sends a `typeCheck` effect with the given type, value, and context.
        The handler receives `{ type, context, value }` and determines the
        response: throw, collect error, log, or offer restarts.

        For typical use, prefer `type.validate` (auto-derived by `mkType`,
        uses the type's name as context). This 3-arg form is for cases
        where a custom context string is needed.
      '';
      tests = validateTests;
    };

    pure = api.leaf { value = pure; description = "pure: re-export of `fx.kernel.pure` for dependent contract modules."; doc = "Re-export of `fx.kernel.pure`."; };
    bind = api.leaf { value = bind; description = "bind: re-export of `fx.kernel.bind` for dependent contract modules."; doc = "Re-export of `fx.kernel.bind`."; };
    send = api.leaf { value = send; description = "send: re-export of `fx.kernel.send` for dependent contract modules."; doc = "Re-export of `fx.kernel.send`."; };
  };
}
