# nix-effects dependent types: Pi, Sigma, Certified, Vector, DepRecord.
{ fx, api, ... }:
let
  inherit (fx.types.foundation) mkType check;
  inherit (fx.kernel) pure bind send;
  H = fx.tc.hoas;
  P = fx.diag.positions;
  R = fx.tc.kernel.reflect;
  KT = fx.tc.kernel.ktype;
  E = fx.tc.eval;

  # checkHoas wrapped so a stuck/ill-formed term degrades to `false`, never poisons.
  proves = ty: term:
    let r = builtins.tryEval (!((H.checkHoas ty term) ? error));
    in r.success && r.value;

  # Read a child type's universe during construction, attributing a
  # term-dependent or level-polymorphic failure to THIS construction site
  # rather than surfacing the bare foundation throw. Lazy: forces the child
  # universe only when the constructed type's own `.universe` is forced.
  universeOf = ctx: ty:
    let r = builtins.tryEval ty.universe;
    in if r.success then r.value
    else throw "${ctx}: child universe must be term-independent";

  # Native-recursion budget per trampoline segment (cf. foundation.nix).
  nativeWalkBudget = 512;

  # Recurse natively while fuel remains, else defer the sub-walk onto the
  # trampoline so deep Σ-spines stay in the host stack; the public 2-arg
  # validateAt reseeds the budget and would never bounce.
  descendV = t: fuel: p: x:
    if fuel <= 0
    then send "deriveBounce" { run = _: t.validateAtF nativeWalkBudget p x; }
    else t.validateAtF (fuel - 1) p x;

  Pi = { domain, codomain, universe, name ? "Π(${domain.name})", kernelType ? null }:
    let
      piType = mkType
        {
          inherit name;
          kernelType = if kernelType != null then kernelType else H.function_;
          # When no explicit kernelType, H.function_ is a sound but lossy
          # approximation — it loses domain/codomain structure. Mark as
          # approximate so _kernel/kernelCheck/prove are suppressed, letting
          # elaborateType do structural auto-detection.
          approximate = kernelType == null;
          # Guard: null for all Pi types. When kernelType is explicit, the
          # opaque lambda check (domain match + isFunction) covers guarding.
          # When kernelType is omitted (approximate, H.function_),
          # kernelDecide checks isFunction via elaboration.
          guard = null;
          universe = universe;
        } // {
        inherit domain codomain;

        apply = arg: codomain arg;

        # In higher-order contract terms (Findler & Felleisen 2002): checkAt
        # is deferred contract checking at each application site.
        #
        # Totality: if f is not a function, we send a typeCheck for the Pi
        # type itself. When domain check fails, we short-circuit: f(arg) is
        # never evaluated, because f may crash on wrong-typed arguments.
        # This mirrors the principle that elimination requires valid inputs.
        checkAt = f: arg:
          if !(builtins.isFunction f)
          then
            send "typeCheck"
              {
                type = piType;
                context = "Π check (${name})";
                value = f;
                reason = "shape-mismatch";
              }
          else
            bind
              (send "typeCheck" {
                type = domain;
                context = "Π domain (${name})";
                value = arg;
                reason = "deferred-pi";
              })
              (domPassed:
                if domPassed == false then pure null
                else
                  let
                    result = f arg;
                    codomainType = codomain arg;
                  in
                  bind
                    (send "typeCheck" {
                      type = codomainType;
                      context = "Π codomain (${name})";
                      value = result;
                      reason = "deferred-pi";
                    })
                    (_:
                      pure result));

        compose = f: other:
          Pi {
            inherit domain;
            codomain = x: other.codomain (f x);
            universe = universeOf "compose(${name}, ${other.name})" other;
            name = "compose(${name}, ${other.name})";
          };
      };
    in
    piType;
  PiTests = {
    "pi-accepts-function" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        check piT (x: x + 1);
      expected = true;
    };
    "pi-rejects-non-function" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        check piT 42;
      expected = false;
    };
    "pi-apply-computes-codomain" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          piT = Pi {
            domain = IntT;
            codomain = n: if n > 0 then StrT else IntT;
            universe = 0;
          };
        in
        (piT.apply 5).name;
      expected = "String";
    };
    "pi-apply-codomain-depends-on-value" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          piT = Pi {
            domain = IntT;
            codomain = n: if n > 0 then StrT else IntT;
            universe = 0;
          };
        in
        (piT.apply (-1)).name;
      expected = "Int";
    };
    "pi-checkAt-returns-computation" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        fx.comp.isPure (piT.checkAt (x: x * 2) 21);
      expected = false;
    };
    "pi-checkAt-first-effect-is-typeCheck" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        (piT.checkAt (x: x * 2) 21).effect.name;
      expected = "typeCheck";
    };
    "pi-checkAt-domain-context" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
          comp = piT.checkAt (x: x * 2) 21;
        in
        comp.effect.param.context;
      expected = "Π domain (Π(Int))";
    };
    "pi-validate-pure-on-valid-function" = {
      # Fail-only emission: auto-derived .validate is pure when the
      # introduction form (isFunction) succeeds.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        fx.comp.isPure (piT.validate (x: x));
      expected = true;
    };
    "pi-validate-emits-on-non-function" = {
      # The auto-derived .validate wraps the isFunction check in a
      # typeCheck effect, emitted on failure.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        fx.comp.isPure (piT.validate 42);
      expected = false;
    };
    "pi-validate-is-one-arg" = {
      # validate takes ONE arg (the value to check for introduction form).
      # checkAt takes TWO args (function + argument for elimination checking).
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
          comp = piT.validate 42;
        in
        comp.effect.param.context;
      expected = "Π(Int)";
    };
    "pi-checkAt-total-on-non-function" = {
      # Totality: checkAt on a non-function fails through the effect
      # system (sends typeCheck) rather than crashing Nix.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        fx.comp.isPure (piT.checkAt 42 5);
      expected = false;
    };
    "pi-checkAt-total-context" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = _: IntT; universe = 0; };
        in
        (piT.checkAt 42 5).effect.param.context;
      expected = "Π check (Π(Int))";
    };
    "pi-compose-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          f = Pi { domain = IntT; codomain = _: StrT; name = "f"; universe = 0; };
          g = Pi { domain = StrT; codomain = _: BoolT; name = "g"; universe = 0; };
        in
        (f.compose toString g).name;
      expected = "compose(f, g)";
    };
    "pi-compose-codomain" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          f = Pi { domain = IntT; codomain = _: StrT; name = "f"; universe = 0; };
          g = Pi { domain = StrT; codomain = _: BoolT; name = "g"; universe = 0; };
          composed = f.compose toString g;
        in
        (composed.apply 42).name;
      expected = "Bool";
    };
    "pi-non-dependent-is-arrow" = {
      # When B is constant, Π(x:A).B = A → B (ordinary function type)
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          arrowT = Pi {
            domain = IntT;
            codomain = _: StrT;
            name = "Int → String";
            universe = 0;
          };
        in
        arrowT.name;
      expected = "Int → String";
    };
    "pi-universe-explicit" = {
      # Universe is an explicit parameter at the surface API level.
      # The kernel independently computes and verifies levels via
      # checkTypeLevel when kernelType is provided.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          TypeT = mkType { name = "Type"; kernelType = H.u 0; guard = v: builtins.isAttrs v && v ? _tag && v._tag == "Type"; };
          # Int → Type lives in Type_1 (maps values to types)
          piT = Pi { domain = IntT; codomain = _: TypeT; universe = 1; };
        in
        piT.universe;
      expected = 1;
    };
    "pi-with-kernelType-has-kernel" = {
      # Pi with explicit kernelType gets _kernel and prove
      expr =
        let
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          NatT = mkType { name = "Nat"; kernelType = H.nat; };
          piT = Pi { domain = BoolT; codomain = _: NatT; universe = 0; kernelType = H.forall "x" H.bool (_: H.nat); };
        in
        piT ? _kernel && piT ? prove;
      expected = true;
    };
    "pi-has-kernelCheck" = {
      # Pi has kernelCheck from mkType (derived from decide)
      expr =
        let
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          piT = Pi { domain = BoolT; codomain = _: BoolT; universe = 0; kernelType = H.forall "x" H.bool (_: H.bool); };
        in
        piT ? kernelCheck;
      expected = true;
    };
    "pi-without-kernelType-not-precise" = {
      # Pi without explicit kernelType is approximate — not kernel-precise
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          piT = Pi { domain = IntT; codomain = n: if n > 0 then IntT else IntT; universe = 0; };
        in
        piT._kernelPrecise;
      expected = false;
    };
  };

  Sigma = { fst, snd, universe, name ? "Σ(${fst.name})", kernelType ? null }:
    mkType
      {
        inherit name;
        kernelType = if kernelType != null then kernelType else H.any;
        # When no explicit kernelType, H.any is the weakest approximation —
        # it loses all Sigma structure. Mark as approximate so _kernel is
        # suppressed, letting elaborateType do structural auto-detection.
        approximate = kernelType == null;
        # Guard: exact first-order contract. Both components are concrete
        # data, so the full dependent introduction rule is decidable.
        guard = v:
          builtins.isAttrs v
          && v ? fst && v ? snd
          && fst.check v.fst
          && (snd v.fst).check v.snd;
        universe = universe;
        # Guard-bearing sub-types (e.g. Certified snd) are invisible to the
        # kernel walker, so walker dispatch is deferred until either sub-component
        # kernel sufficiency is tracked at dispatch time or such guards are
        # kernel-encoded. The walker and bespoke path shapes (P.SigmaFst/
        # P.SigmaSnd) are invariant, so enabling dispatch later won't move them.
        verify = self: fuel: path: v:
          if !(builtins.isAttrs v && v ? fst && v ? snd)
          then
            send "typeCheck"
              {
                type = self;
                context = "Σ (${name})";
                value = v;
                reason = "shape-mismatch";
                inherit path;
              }
          else
            bind (descendV fst fuel (path ++ [ P.SigmaFst ]) v.fst) (_:
              if !(fst.check v.fst) then pure v
              else
                bind (descendV (snd v.fst) fuel (path ++ [ P.SigmaSnd ]) v.snd)
                  (_: pure v));
      } // {
      fstType = fst;
      sndFamily = snd;

      proj1 = p: p.fst;

      proj2 = p: p.snd;

      pair = fstVal: sndVal:
        if !(fst.check fstVal)
        then builtins.throw "Σ type ${name}: fst does not inhabit ${fst.name}"
        else if !((snd fstVal).check sndVal)
        then builtins.throw "Σ type ${name}: snd does not inhabit ${(snd fstVal).name}"
        else { fst = fstVal; snd = sndVal; };

      # Short-circuits on fst failure: the snd type family is never evaluated
      # on wrong-typed fst.
      pairE = fstVal: sndVal:
        bind (fst.validate fstVal) (_:
          if fst.check fstVal == false then pure { fst = fstVal; snd = sndVal; }
          else
            let sndType = snd fstVal;
            in bind (sndType.validate sndVal) (_:
              pure { fst = fstVal; snd = sndVal; }));

      # Curry/uncurry for Sigma types
      curry = f: a: b: f { fst = a; snd = b; };
      uncurry = f: p:
        if builtins.isAttrs p && p ? fst && p ? snd
        then f p.fst p.snd
        else builtins.throw "uncurry: expected Sigma pair";

      # Contravariant predicate pullback: accepts (x, y) iff the original
      # accepts (f(x), g(y)). Composition law (contravariant):
      #   pullback (f∘g) (h∘k) = pullback g k >>> pullback f h
      # Note the REVERSED order vs. covariant bimap.
      pullback = f: g: Sigma {
        fst = mkType {
          name = "${fst.name}'";
          kernelType = fst._kernel;
          guard = v: fst.check (f v);
          universe = universeOf "pullback(${name}) fst" fst;
        };
        snd = x:
          let orig = snd (f x);
          in mkType {
            name = "${orig.name}'";
            kernelType = orig._kernel;
            guard = v: orig.check (g v);
            universe = universeOf "pullback(${name}) snd" orig;
          };
        name = "pullback(${name})";
        inherit universe;
      };
    };
  SigmaTests = {
    "sigma-accepts-valid-pair" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma {
            fst = IntT;
            snd = n: mkType {
              name = "List[${toString n}]";
              kernelType = H.any;
              guard = v: builtins.isList v && builtins.length v == n;
            };
            universe = 0;
          };
        in
        check sigT { fst = 2; snd = [ "a" "b" ]; };
      expected = true;
    };
    "sigma-rejects-dependent-mismatch" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma {
            fst = IntT;
            snd = n: mkType {
              name = "List[${toString n}]";
              kernelType = H.any;
              guard = v: builtins.isList v && builtins.length v == n;
            };
            universe = 0;
          };
        in
        check sigT { fst = 3; snd = [ "a" "b" ]; };
      expected = false;
    };
    "sigma-rejects-bad-fst" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma {
            fst = IntT;
            snd = _: IntT;
            universe = 0;
          };
        in
        check sigT { fst = "nope"; snd = 0; };
      expected = false;
    };
    "sigma-proj1" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        sigT.proj1 { fst = 42; snd = 0; };
      expected = 42;
    };
    "sigma-proj2" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        sigT.proj2 { fst = 0; snd = 42; };
      expected = 42;
    };
    "sigma-validate-pure-on-valid-pair" = {
      # Fail-only emission: a well-typed pair walks through the
      # decomposed verifier without emitting any typeCheck.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        fx.comp.isPure (sigT.validate { fst = 1; snd = 2; });
      expected = true;
    };
    "sigma-validate-effect-is-typeCheck" = {
      # On failure (snd mismatched), the decomposed verifier emits
      # typeCheck through the sub-component's validateAt.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        (sigT.validate { fst = 1; snd = "bad"; }).effect.name;
      expected = "typeCheck";
    };
    "sigma-validate-total-on-non-attrset" = {
      # Totality: validate on a non-attrset fails through the effect
      # system rather than crashing Nix.
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        fx.comp.isPure (sigT.validate 42);
      expected = false;
    };
    "sigma-validate-total-on-missing-fields" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        fx.comp.isPure (sigT.validate { x = 1; });
      expected = false;
    };
    "sigma-pairE-returns-computation" = {
      # pairE is an effectful smart constructor that recursively
      # validates sub-components. Under fail-only emission, a
      # well-typed pair walks through without emitting; we drive
      # impurity via a snd that violates the snd type ("bad" : String
      # against Int).
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        fx.comp.isPure (sigT.pairE 1 "bad");
      expected = false;
    };
    "sigma-curry-uncurry" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
          add = sigT.curry (p: p.fst + p.snd);
          addPair = sigT.uncurry (a: b: a + b);
        in
        { curried = add 3 4; uncurried = addPair { fst = 3; snd = 4; }; };
      expected = { curried = 7; uncurried = 7; };
    };
    "sigma-non-dependent-is-product" = {
      # When B is constant, Σ(x:A).B = A × B (ordinary product)
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          prodT = Sigma {
            fst = IntT;
            snd = _: StrT;
            name = "Int × String";
            universe = 0;
          };
        in
        check prodT { fst = 42; snd = "hello"; };
      expected = true;
    };
    "sigma-pullback-name" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; name = "IntPair"; universe = 0; };
        in
        (sigT.pullback (x: x) (x: x)).name;
      expected = "pullback(IntPair)";
    };
    "sigma-has-pullback" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma { fst = IntT; snd = _: IntT; universe = 0; };
        in
        sigT ? pullback;
      expected = true;
    };
    "sigma-with-kernelType-has-kernel" = {
      # Sigma with explicit kernelType gets kernelCheck and prove
      expr =
        let
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          NatT = mkType { name = "Nat"; kernelType = H.nat; };
          sigT = Sigma { fst = NatT; snd = _: BoolT; universe = 0; kernelType = H.sigma "x" H.nat (_: H.bool); };
        in
        sigT ? kernelCheck && sigT ? prove;
      expected = true;
    };
    "sigma-kernelCheck-accepts" = {
      expr =
        let
          NatT = mkType { name = "Nat"; kernelType = H.nat; };
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          sigT = Sigma { fst = NatT; snd = _: BoolT; universe = 0; kernelType = H.sigma "x" H.nat (_: H.bool); };
        in
        sigT.kernelCheck { fst = 0; snd = true; };
      expected = true;
    };
    "sigma-kernelCheck-rejects" = {
      expr =
        let
          NatT = mkType { name = "Nat"; kernelType = H.nat; };
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          sigT = Sigma { fst = NatT; snd = _: BoolT; universe = 0; kernelType = H.sigma "x" H.nat (_: H.bool); };
        in
        sigT.kernelCheck { fst = true; snd = true; };
      expected = false;
    };
    "sigma-without-kernelType-no-kernel" = {
      # Sigma without explicit kernelType is approximate — kernel fields
      # suppressed so elaborateType can do structural auto-detection
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          sigT = Sigma {
            fst = IntT;
            snd = n: mkType { name = "L${toString n}"; kernelType = H.any; guard = v: builtins.isList v && builtins.length v == n; };
            universe = 0;
          };
        in
        sigT ? kernelCheck;
      expected = false;
    };
  };

  # Bundle a propositional family with its bridge for Certified's general former.
  mkPropFamily = { family, bridge }: { _tag = "PropFamily"; inherit family bridge; };

  Certified =
    { base
    , predicate ? null
    , family ? null
    , bridge ? null
    , name ? "Certified(${base.name})"
    }:
    if predicate != null && R.isKernelPred predicate then
    # decidable: Boolean-reflected certificate
      let
        t = R.ktypeOf predicate;
        El = KT.El t;
        guardHolds = R.deriveGuard predicate;
        witnessTerm = v: H.ann (H.pair (predicate.bridge v) H.tt) El;
      in
      (Sigma {
        fst = base;
        # Proof at the concrete fst; witness is the Unit inhabitant (`null`),
        # the guard decides the predicate through the kernel oracle.
        snd = v: mkType {
          name = "Proof(${name})";
          kernelType = H.unit;
          guard = _witness: guardHolds v;
        };
        inherit name;
        universe = universeOf "Certified ${name}" base;
        # Σ x:A. Unit — the host decide oracle settles this without normalizing.
        # NOT El t: decide dispatches on the snd type's syntactic head and never
        # reduces, so a stuck P(decide t x) head would be rejected. El t rides on
        # `_kernel` below, for prove/metatheory only.
        kernelType = H.sigma "x" base._kernel (_: H.unit);
      }) // {
        # `El` carries two lazy per-type caches so the structural walker's
        # normalize-before-dispatch (`walkEl`) pays the `El` elaboration once per
        # distinct `Certified` type, not once per checked value:
        #   `_elWhnf` — the WHNF (`VSigma`) used to dispatch and to instantiate
        #               the predicate closure;
        #   `_elTm`   — the lowered `Tm`, embedded as each witness pair's type
        #               annotation (`walkEl`), so the per-value witness elaborates
        #               without re-lowering `El`.
        # Both extra fields are invisible to `H.elab`/the kernel; they ride along
        # when this `_kernel` is embedded as a compound field.
        _kernel = El // {
          _elWhnf = E.forceVal (E.eval [ ] (H.elab El));
          _elTm = H.elab El;
        };
        _kernelSufficient = true;
        ktype = t;
        decidable = true;
        prove = term: proves El term;
        inherit witnessTerm;
        # Fail-closed; witness synthesized as the Unit inhabitant.
        certify = v:
          if !(base.check v)
          then builtins.throw "Certified ${name}: value does not inhabit ${base.name}"
          else if !(guardHolds v)
          then builtins.throw "Certified ${name}: predicate failed"
          else { fst = v; snd = null; };
        certifyE = v:
          bind (base.validate v) (_:
            if base.check v == false then pure { fst = v; snd = null; }
            else
              let
                proofType = mkType {
                  name = "Proof(${name})";
                  kernelType = H.unit;
                  guard = _: guardHolds v;
                };
                r = builtins.tryEval (guardHolds v);
                ok = r.success && r.value;
              in
              if ok then pure { fst = v; snd = null; }
              else bind
                (send "typeCheck" {
                  type = proofType;
                  context = "Certified predicate (${name})";
                  value = null;
                  reason = "predicate-failed";
                })
                (_: pure { fst = v; snd = null; }));
      }
    else if family != null then
    # general: truncated certificate. squash makes any family a mere prop;
    # proof irrelevance is definitional in conv. `family` is either a raw
    # family fn (legacy form, paired with `bridge`) or a mkPropFamily bundle.
      assert (family._tag or null) == "PropFamily" || bridge != null;
      let
        fam = if (family._tag or null) == "PropFamily" then family.family else family;
        brg = if (family._tag or null) == "PropFamily" then family.bridge else bridge;
        sqAt = vTerm: H.squash (fam vTerm);
        kernelTy = H.sigma "x" base._kernel (x: sqAt x);
      in
      (Sigma {
        fst = base;
        # Witness is a host-opaque HOAS term; the guard re-checks it against
        # squash(family v) via the kernel (squash inhabitation isn't host-decidable).
        snd = v: mkType {
          name = "Proof(${name})";
          kernelType = H.any;
          guard = witness: proves (sqAt (brg v)) witness;
        };
        inherit name;
        universe = universeOf "Certified ${name}" base;
        kernelType = H.sigma "x" base._kernel (_: H.any);
      }) // {
        _kernel = kernelTy;
        _kernelSufficient = false;
        decidable = false;
        prove = term: proves kernelTy term;
        # Check p : family(v), then truncate.
        certifyProof = v: p:
          if !(base.check v)
          then builtins.throw "Certified ${name}: value does not inhabit ${base.name}"
          else if !(proves (fam (brg v)) p)
          then builtins.throw "Certified ${name}: supplied proof does not check"
          else { fst = v; snd = H.squashIntro p; };
        # Effectful dual of certifyProof: sends typeCheck instead of throwing.
        certifyProofE = v: p:
          bind (base.validate v) (_:
            if base.check v == false then pure { fst = v; snd = H.squashIntro p; }
            else
              let
                proofType = mkType {
                  name = "Proof(${name})";
                  kernelType = H.any;
                  guard = witness: proves (sqAt (brg v)) witness;
                };
                r = builtins.tryEval (proves (fam (brg v)) p);
                ok = r.success && r.value;
              in
              if ok then pure { fst = v; snd = H.squashIntro p; }
              else bind
                (send "typeCheck" {
                  type = proofType;
                  context = "Certified proof (${name})";
                  value = p;
                  reason = "proof-failed";
                })
                (_: pure { fst = v; snd = H.squashIntro p; }));
      }
    else
    # No proof obtainable. The honest home for an un-proven guard is `refined`.
      builtins.throw
        ("Certified ${name}: predicate is not kernel-decidable and no propositional "
        + "family was supplied. Pass a KernelPred from fx.tc.kernel.reflect, supply "
        + "{ family; bridge; }, or use fx.types.refinement.refined for an un-proven guard.");
  CertifiedTests =
    let
      ev = h: fx.tc.eval.eval [ ] (H.elab h);
      conv = a: b: fx.tc.conv.conv 0 (ev a) (ev b);
      throws = e: !(builtins.tryEval e).success;
      isPure = fx.comp.isPure;

      IntT = mkType { name = "Int"; kernelType = H.int_; };
      StrT = mkType { name = "String"; kernelType = H.string; };

      PosInt = Certified { base = IntT; predicate = R.intPositive; name = "PosInt"; };
      Suit = Certified { base = StrT; predicate = R.strOneOf [ "clubs" "spades" "hearts" "diamonds" ]; name = "Suit"; };
      Bounded = Certified { base = IntT; predicate = R.andKP R.intNonNegative (R.intInRange 0 10); name = "Bounded[0,10]"; };

      # Pfam x = (x = x), inhabited by reflexivity. bridge = intLit.
      ReflEq = Certified { base = IntT; family = x: H.eq H.int_ x x; bridge = H.intLit; name = "ReflEq"; };
      reflProof = v: H.reflDT H.int_ (H.intLit v);
    in
    {
      # decidable: membership
      "dec-accepts-valid" = { expr = check PosInt { fst = 5; snd = null; }; expected = true; };
      "dec-rejects-failing-pred" = { expr = check PosInt { fst = -1; snd = null; }; expected = false; };
      # Contract change: the old Bool witness no longer inhabits.
      "dec-rejects-old-bool-witness" = { expr = check PosInt { fst = 5; snd = true; }; expected = false; };
      # The snd slot enforces Unit: only the canonical inhabitant (`null`) passes.
      "dec-rejects-int-witness" = { expr = check PosInt { fst = 5; snd = 42; }; expected = false; };
      "dec-rejects-string-witness" = { expr = check PosInt { fst = 5; snd = "x"; }; expected = false; };
      "dec-rejects-non-base" = { expr = check PosInt { fst = "x"; snd = null; }; expected = false; };

      # A Certified over a term-dependent (level-polymorphic) base surfaces a
      # construction-scoped universe error instead of accepting an incoherent
      # level; `.universe` throws rather than fabricating one.
      "certified-term-dependent-universe-throws" = {
        expr =
          let
            levelPoly = mkType { name = "LP"; kernelType = H.forall "k" H.level (k: H.u k); };
            C = Certified { base = levelPoly; predicate = R.intPositive; name = "Cbad"; };
          in
          (builtins.tryEval C.universe).success;
        expected = false;
      };

      # decidable: certify (fail-closed, synthesized witness)
      "dec-certify-builds-null-witness" = { expr = PosInt.certify 5; expected = { fst = 5; snd = null; }; };
      "dec-certify-fail-closed-pred" = { expr = throws (PosInt.certify (-1)); expected = true; };
      "dec-certify-fail-closed-base" = { expr = throws (PosInt.certify "x"); expected = true; };
      "dec-certified-value-checks" = { expr = check PosInt (PosInt.certify 7); expected = true; };

      # decidable: the witness is a real proof term
      "dec-kernel-sufficient" = { expr = PosInt._kernelSufficient; expected = true; };
      "dec-ktype-nonnull" = { expr = PosInt.ktype != null; expected = true; };
      "dec-kernel-is-El" = { expr = conv PosInt._kernel (KT.El (R.ktypeOf R.intPositive)); expected = true; };
      "dec-prove-accepts-real-witness" = { expr = PosInt.prove (PosInt.witnessTerm 5); expected = true; };
      "dec-prove-rejects-false-witness" = {
        expr = PosInt.prove (H.ann (H.pair (H.intLit (-1)) H.tt) PosInt._kernel);
        expected = false;
      };
      "dec-witness-normal-form" = {
        expr = conv (PosInt.witnessTerm 5) (H.ann (H.pair (H.intLit 5) H.tt) PosInt._kernel);
        expected = true;
      };

      # decidable: predicate agreement on a grid
      "dec-agreement" = {
        expr = builtins.map (n: check PosInt { fst = n; snd = null; }) [ 42 (-1) 0 7 1 ];
        expected = [ true false false true true ];
      };

      # decidable: effectful introduction + certifyE
      "dec-validate-fails-on-bad-pair" = { expr = isPure (PosInt.validate { fst = -1; snd = null; }); expected = false; };
      "dec-validate-passes-good-pair" = { expr = isPure (PosInt.validate { fst = 5; snd = null; }); expected = true; };
      "dec-certifyE-pure-on-valid" = { expr = isPure (PosInt.certifyE 5); expected = true; };
      "dec-certifyE-impure-on-invalid" = { expr = isPure (PosInt.certifyE (-1)); expected = false; };
      "dec-certifyE-effect-is-typeCheck" = { expr = (PosInt.certifyE (-1)).effect.name; expected = "typeCheck"; };

      # decidable: non-Int carrier (String bridge)
      "dec-str-accepts" = { expr = check Suit { fst = "spades"; snd = null; }; expected = true; };
      "dec-str-rejects" = { expr = check Suit { fst = "joker"; snd = null; }; expected = false; };
      "dec-str-certify" = { expr = Suit.certify "hearts"; expected = { fst = "hearts"; snd = null; }; };

      # decidable: andKP composite
      "dec-andkp-in" = { expr = check Bounded { fst = 5; snd = null; }; expected = true; };
      "dec-andkp-below" = { expr = check Bounded { fst = -1; snd = null; }; expected = false; };
      "dec-andkp-above" = { expr = check Bounded { fst = 20; snd = null; }; expected = false; };

      # general: truncated certificate
      "gen-certifyProof-accepts-valid" = {
        expr = check ReflEq (ReflEq.certifyProof 3 (reflProof 3));
        expected = true;
      };
      "gen-certifyProof-fail-closed-bad-proof" = {
        expr = throws (ReflEq.certifyProof 3 H.tt);
        expected = true;
      };
      "gen-certifyProof-fail-closed-base" = {
        expr = throws (ReflEq.certifyProof "x" (reflProof 3));
        expected = true;
      };
      # Proof irrelevance is definitional.
      "gen-proof-irrelevance" = {
        expr = conv (H.squashIntro (reflProof 3)) (H.squashIntro H.tt);
        expected = true;
      };
      "gen-prove-accepts-witness" = {
        expr = ReflEq.prove (H.ann (H.pair (H.intLit 3) (H.squashIntro (reflProof 3))) ReflEq._kernel);
        expected = true;
      };
      "gen-not-kernel-sufficient" = { expr = ReflEq._kernelSufficient; expected = false; };

      # general: effectful proof introduction
      "gen-certifyProofE-pure-on-valid" = { expr = isPure (ReflEq.certifyProofE 3 (reflProof 3)); expected = true; };
      "gen-certifyProofE-impure-on-bad-proof" = { expr = isPure (ReflEq.certifyProofE 3 H.tt); expected = false; };
      "gen-certifyProofE-effect-is-typeCheck" = { expr = (ReflEq.certifyProofE 3 H.tt).effect.name; expected = "typeCheck"; };
      "gen-certifyProofE-impure-on-bad-base" = { expr = isPure (ReflEq.certifyProofE "x" (reflProof 3)); expected = false; };

      # general: mkPropFamily bundle
      "gen-propFamily-tag" = {
        expr = (mkPropFamily { family = x: H.eq H.int_ x x; bridge = H.intLit; })._tag;
        expected = "PropFamily";
      };
      "gen-propFamily-checks-like-two-arg" = {
        expr =
          let RB = Certified {
            base = IntT;
            family = mkPropFamily { family = x: H.eq H.int_ x x; bridge = H.intLit; };
            name = "ReflEqBundled";
          };
          in check RB (RB.certifyProof 3 (reflProof 3));
        expected = true;
      };

      # no proof obtainable: rejected at construction (no Bool escape)
      "reject-raw-lambda" = { expr = throws (Certified { base = IntT; predicate = x: x > 0; }); expected = true; };
      "reject-crashing-predicate" = { expr = throws (Certified { base = IntT; predicate = _: builtins.throw "crash"; }); expected = true; };
      "reject-family-without-bridge" = { expr = throws (Certified { base = IntT; family = x: H.eq H.int_ x x; }); expected = true; };
    };

  NatT = mkType { name = "Nat"; kernelType = H.nat; };

  Vector = elemType:
    Pi {
      domain = NatT;
      codomain = n: mkType {
        name = "Vector[${toString n}, ${elemType.name}]";
        kernelType = H.any;
        guard = v:
          builtins.isList v
          && builtins.length v == n
          && builtins.all elemType.check v;
      };
      name = "Vector(${elemType.name})";
      universe = 0;
    };
  VectorTests = {
    "vector-is-pi-type" = {
      expr =
        let IntT = mkType { name = "Int"; kernelType = H.int_; };
        in (Vector IntT) ? validate;
      expected = true;
    };
    "vector-apply-gives-specific-type" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          v3i = (Vector IntT).apply 3;
        in
        check v3i [ 1 2 3 ];
      expected = true;
    };
    "vector-apply-rejects-wrong-length" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          v3i = (Vector IntT).apply 3;
        in
        check v3i [ 1 2 ];
      expected = false;
    };
    "vector-apply-rejects-wrong-element-type" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          v3i = (Vector IntT).apply 3;
        in
        check v3i [ 1 "two" 3 ];
      expected = false;
    };
    "vector-zero-accepts-empty" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          v0 = (Vector IntT).apply 0;
        in
        check v0 [ ];
      expected = true;
    };
    "vector-has-compose" = {
      expr =
        let IntT = mkType { name = "Int"; kernelType = H.int_; };
        in (Vector IntT) ? compose;
      expected = true;
    };
    "vector-check-is-function" = {
      # The Pi type's introduction form check: Vector values are functions
      # (from Nat to sized lists). This is the type-theoretic view.
      expr =
        let IntT = mkType { name = "Int"; kernelType = H.int_; };
        in check (Vector IntT) (n: builtins.genList (_: 0) n);
      expected = true;
    };
  };

  # An n-ary dependent record is isomorphic to nested Sigma:
  #   { a : A, b : B(a), c : C(a,b) }  ≅  Σ(a:A).Σ(b:B(a)).C(a,b)
  # Values are nested Sigma pairs: { fst = a; snd = { fst = b; snd = c; }; }

  # Unit type for the terminal case of nested Sigma
  UnitT = mkType { name = "Unit"; kernelType = H.unit; };

  DepRecord = fields:
    let
      fieldNames = map (f: f.name) fields;
      namesStr = builtins.concatStringsSep ", " fieldNames;

      # Build nested Sigma type from field list
      # Single field: just the field type (terminal)
      # Two+ fields: Sigma { fst = head; snd = v: recurse tail (partial // {head.name = v}); }
      buildSigma = remaining: partial:
        if builtins.length remaining == 0 then
          UnitT
        else if builtins.length remaining == 1 then
          let
            field = builtins.head remaining;
          in
          if builtins.isFunction field.type
          then field.type partial
          else field.type
        else
          let
            field = builtins.head remaining;
            rest = builtins.tail remaining;
            fieldType =
              if builtins.isFunction field.type
              then field.type partial
              else field.type;
            # Kernel propagation: when all remaining fields are non-dependent
            # and kernel-exact, compute Sigma kernel type from _kernel.
            sigmaKernelType =
              if builtins.all (f: !(builtins.isFunction f.type)) remaining
                && (fieldType._kernelPrecise or false) then
                let restType = buildSigma rest { };
                in if restType._kernelPrecise or false then
                  H.sigma "x" fieldType._kernel (_: restType._kernel)
                else null
              else null;
          in
          Sigma {
            fst = fieldType;
            snd = v: buildSigma rest (partial // { ${field.name} = v; });
            name = "DepRec{${namesStr}}.${field.name}";
            universe = universeOf "DepRecord field ${field.name}" fieldType;
            kernelType = sigmaKernelType;
          };

      sigmaType = buildSigma fields { };

      packFields = remaining: v:
        if builtins.length remaining == 0 then
          null
        else if builtins.length remaining == 1 then
          v.${(builtins.head remaining).name}
        else
          let
            field = builtins.head remaining;
            rest = builtins.tail remaining;
          in
          { fst = v.${field.name}; snd = packFields rest v; };

      unpackFields = remaining: packed:
        if builtins.length remaining == 0 then
          { }
        else if builtins.length remaining == 1 then
          { ${(builtins.head remaining).name} = packed; }
        else
          let
            field = builtins.head remaining;
            rest = builtins.tail remaining;
          in
          { ${field.name} = packed.fst; } // unpackFields rest packed.snd;

    in
    sigmaType // {
      # Override name for display
      name = "DepRecord{${namesStr}}";

      # Bijections between flat attrset and nested Sigma representation
      pack = v: packFields fields v;
      unpack = packed: unpackFields fields packed;

      # Convenience: check a flat attrset (validates via pack → Sigma check)
      checkFlat = v:
        builtins.isAttrs v
        && builtins.all (f: v ? ${f.name}) fields
        && sigmaType.check (packFields fields v);
    };
  DepRecordTests = {
    "deprec-sigma-accepts-nested-pair" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            { name = "s"; type = StrT; }
          ];
          # Nested Sigma pair: { fst = 2; snd = "hello"; }
        in
        check recT { fst = 2; snd = "hello"; };
      expected = true;
    };
    "deprec-sigma-rejects-bad-type" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            { name = "s"; type = StrT; }
          ];
        in
        check recT { fst = "not-int"; snd = "hello"; };
      expected = false;
    };
    "deprec-dependent-field" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            {
              name = "items";
              type = (self:
                mkType {
                  name = "List[n=${toString self.n}]";
                  kernelType = H.any;
                  guard = v: builtins.isList v && builtins.length v == self.n;
                });
            }
          ];
          # { fst = 2; snd = ["a" "b"]; } — snd type depends on fst
        in
        check recT { fst = 2; snd = [ "a" "b" ]; };
      expected = true;
    };
    "deprec-dependent-mismatch" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            {
              name = "items";
              type = (self:
                mkType {
                  name = "List[n=${toString self.n}]";
                  kernelType = H.any;
                  guard = v: builtins.isList v && builtins.length v == self.n;
                });
            }
          ];
        in
        check recT { fst = 3; snd = [ "a" "b" ]; };
      expected = false;
    };
    "deprec-has-validate" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            { name = "s"; type = StrT; }
          ];
        in
        recT ? validate;
      expected = true;
    };
    "deprec-pack-unpack" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            { name = "s"; type = StrT; }
          ];
          flat = { n = 42; s = "hello"; };
          packed = recT.pack flat;
          unpacked = recT.unpack packed;
        in
        unpacked;
      expected = { n = 42; s = "hello"; };
    };
    "deprec-checkFlat" = {
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          StrT = mkType { name = "String"; kernelType = H.string; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            { name = "s"; type = StrT; }
          ];
        in
        recT.checkFlat { n = 42; s = "hello"; };
      expected = true;
    };
    "deprec-non-dep-has-kernel" = {
      # Non-dependent DepRecord with kernel-backed fields propagates kernel
      expr =
        let
          NatT = mkType { name = "Nat"; kernelType = H.nat; };
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          recT = DepRecord [
            { name = "n"; type = NatT; }
            { name = "b"; type = BoolT; }
          ];
        in
        recT ? _kernel && recT ? kernelCheck;
      expected = true;
    };
    "deprec-refined-field-has-precise-kernel" = {
      # DepRecord with refined fields keeps a precise kernel through
      # _kernelPrecise while the guard remains external.
      expr =
        let
          Pos = fx.types.foundation.refine
            (mkType { name = "Int"; kernelType = H.int_; })
            (x: x > 0);
          BoolT = mkType { name = "Bool"; kernelType = H.bool; };
          recT = DepRecord [
            { name = "n"; type = Pos; }
            { name = "b"; type = BoolT; }
          ];
        in
        recT ? _kernel && recT ? kernelCheck;
      expected = true;
    };
    "deprec-dependent-field-still-approximate" = {
      # Dependent fields bail out of kernel propagation (preserved)
      expr =
        let
          IntT = mkType { name = "Int"; kernelType = H.int_; };
          recT = DepRecord [
            { name = "n"; type = IntT; }
            {
              name = "items";
              type = (self:
                mkType {
                  name = "L";
                  kernelType = H.any;
                  guard = v: builtins.isList v && builtins.length v == self.n;
                });
            }
          ];
        in
        recT ? kernelCheck;
      expected = false;
    };
  };

in
api.namespace {
  description = "fx.types.dependent: dependent contracts Pi (Π), Sigma (Σ), Certified, Vector, DepRecord — higher-order contracts checked incrementally at each application site.";
  doc = ''
    Dependent contracts: Pi (Π), Sigma (Σ), Certified, Vector, DepRecord.
    Grounded in Martin-Löf (1984) "Intuitionistic Type Theory".
  '';
  value = {
    Pi = api.leaf {
      value = Pi;
      doc = ''
        Dependent function type `Π(x:A).B(x)`.

        Arguments:

        - `domain` — Type A
        - `codomain` — A-value → Type (type family B indexed by domain values)
        - `universe` — Universe level (explicit parameter — see below)
        - `name` — optional display name

        == Higher-order contract with algebraic effects ==

        Pi is a HIGHER-ORDER CONTRACT (Findler & Felleisen 2002). Higher-order
        contracts check function values differently from data values: a data
        contract is verified immediately and completely, but a function contract
        is verified incrementally at each application site. This is the
        standard, correct strategy for function contracts — not a deficit.

        The (Specification, Guard, Verifier) triple for Pi:

        ```
        Guard (check):       builtins.isFunction — the immediate first-order
                             part of the contract. Soundly rejects non-functions.
        Verifier (validate): effectful guard (auto-derived, 1 arg) — wraps
                             the guard in a typeCheck effect for blame tracking.
        Elimination (checkAt): deferred contract check (2 args) — verifies a
                             specific application f(arg) by sending typeCheck
                             effects for both domain (arg : A) and codomain
                             (f(arg) : B(arg)).
        ```

        This is precisely the Findler-Felleisen decomposition: the immediate
        part (`isFunction`) is checked at introduction; the deferred part
        (domain + codomain) is checked at each elimination site via `checkAt`.

        == Adequacy ==

        ```
        check f ⟺ all typeCheck effects in (validate f) pass
        ```

        Both `check` and `validate` verify the introduction form (is it a function?).
        `checkAt` verifies individual applications — the deferred contract.

        == Universe level ==

        Universe level is an explicit parameter. In MLTT, the level is computed
        as `max(i, sup_{a:A} level(B(a)))` by inspecting the syntax of B.
        For types with explicit kernelType, the kernel computes and verifies
        levels via checkTypeLevel. The explicit universe parameter provides
        the level for the surface API's `.universe` field.

        == MLTT rule mapping ==

        ```
        Formation:          Pi { domain, codomain, universe }
        Introduction check: .check (guard: isFunction)
        Introduction verify: .validate (effectful guard, auto-derived)
        Elimination:        .apply (pure), .checkAt (effectful, deferred contract)
        Computation:        β-reduction (Nix evaluation)
        ```

        Operations:

        - `.checkAt f arg` — deferred contract check at elimination site
        - `.apply arg` — pure elimination: compute codomain type B(arg)
        - `.compose f other` — compose Pi types (requires witness function)
        - `.domain` — the domain type A
        - `.codomain` — the type family B
      '';
      tests = PiTests;
    };
    Sigma = api.leaf {
      value = Sigma;
      doc = ''
        Dependent pair type `Σ(x:A).B(x)`.

        Arguments:

        - `fst` — Type A (type of the first component)
        - `snd` — A-value → Type (type family for the second component)
        - `universe` — Universe level (explicit parameter)
        - `name` — optional display name
        - `kernelType` — optional explicit HOAS kernel form (see below)

        Values are `{ fst; snd; }` where `fst : A` and `snd : B(fst)`.

        == Kernel form: explicit vs. approximate ==

        `snd : A-value → Type` lives at the Nix-meta level — it operates on
        Nix values. The kernel form `H.sigma name fst._kernel (a: ...)`
        needs a closure operating on **HOAS variables**, not Nix values.
        The two categories disagree:

        ```
        snd          : NixVal → Type        (surface, Nix-meta)
        kernel snd   : HoasVar → HoasType   (kernel, HOAS-level)
        ```

        For genuinely-dependent `snd` (e.g., `x: if x > 0 then Int else String`),
        `snd` cannot be applied to an HOAS variable — the test on the variable
        would crash. So the library does not attempt automatic derivation;
        omitting `kernelType` produces `_kernel = H.any` with `approximate =
        true`. Downstream consumers that take Sigma through `elaborateType`
        recover the structure at the surface→kernel boundary; consumers that
        use `_kernel` directly (kernel walkers, the generic `deriveCheck`
        dispatcher) see `H.any`.

        Pass `kernelType` explicitly when you need the kernel form to **be** a
        Sigma — for example when piping the Type into another datatype
        constructor whose kernel walker dispatches on `_htag == "sigma"`:

        ```nix
        Prod = Sigma {
          fst = Int;
          snd = _: String;
          universe = 0;
          kernelType = H.sigma "x" Int._kernel (_: String._kernel);
        };
        ```

        For the non-dependent case (snd ignores its argument) the explicit
        form is mechanical and could in principle be derived; the library
        treats both cases uniformly to keep the dependent/non-dependent
        distinction out of the surface API.

        == First-order contract — guard is exact ==

        Sigma is a FIRST-ORDER CONTRACT: both components are concrete data,
        so the contract is checked immediately and completely. The guard
        (`check`) IS full membership — there is no over-approximation.

        ```
        Guard (check):    fst:A ∧ snd:B(fst) — exact. G = ⟦Σ(x:A).B(x)⟧.
        Verifier (verify): decomposed effectful check — sends separate
                          typeCheck effects for fst and snd for blame tracking.
        ```

        This contrasts with Pi where the guard over-approximates (`isFunction`)
        because functions are higher-order. Sigma pairs are data — the
        dependent relationship (snd's type depends on fst's value) can be
        fully verified because both values are available.

        Adequacy:

        ```
        T.check v ⟺ all typeCheck effects in T.validate v pass
        ```

        Under the all-pass handler. The guard is exact and the decomposed
        verifier sends individual `typeCheck` effects per component — the all-pass
        handler's boolean state tracks whether all passed. Totality: if the input
        is structurally malformed (not an attrset, missing `fst`/`snd`), verify falls
        back to a single `typeCheck` for the whole type — failure goes through the
        effect system, never crashes Nix.

        Universe level is an explicit parameter (computing
        `sup_{a:A} snd(a).universe` requires evaluating the type family on
        all domain values, same as Pi).

        == MLTT rule mapping ==

        ```
        Formation:    Sigma { fst, snd, universe }
        Introduction: .check (exact guard), .validate (effectful, decomposed)
        Elimination:  .proj1 (π₁), .proj2 (π₂)
        Computation:  π₁(a,b) ≡ a, π₂(a,b) ≡ b
        ```

        Operations:

        - `.proj1 pair` — first projection π₁
        - `.proj2 pair` — second projection π₂
        - `.pair a b` — smart constructor (throws on invalid)
        - `.validate v` — effectful: decomposed typeCheck effects for blame
        - `.pairE a b` — effectful smart constructor
        - `.pullback f g` — contravariant predicate pullback (see below)
        - `.curry` / `.uncurry` — standard Sigma adjunction
        - `.fstType` — the type A
        - `.sndFamily` — the type family B
      '';
      tests = SigmaTests;
    };
    Certified = api.leaf {
      value = Certified;
      doc = ''
        Subset type `Σ(x:A).P(x)` with `P(x)` a mere proposition. The witness
        is an inhabitant of `P(x)`, not the host Bool. Two formers, one type:

        - decidable `predicate` (a `reflect` KernelPred) → `P x = KT.P(decide t x)`
          (`Unit`/`Void` ≡ `KT.El t`); witness is the Unit inhabitant (`null`),
          synthesized by `certify`. `_kernelSufficient = true`; `_kernel = El t`.
        - general `{ family; bridge; }` (`family : A → U`, or a `mkPropFamily`
          bundle passed as `family`) → `P x = squash(family x)`, proof
          irrelevance definitional; witness is `squashIntro` of a checked HOAS
          proof supplied to `certifyProof v p`. `_kernelSufficient = false`.

        A predicate that is neither (a raw host lambda) yields no proof, so it is
        not a `Certified` — construction throws. For an un-proven runtime guard
        use `fx.types.refinement.refined`.

        Construction:

        - `.certify v` — decidable: pure, fail-closed, synthesizes the witness.
        - `.certifyProof v p` — general: checks `p : family(v)`, then truncates.
        - `.certifyE v` — decidable effectful dual (sends `typeCheck` on failure).
        - `.certifyProofE v p` — general effectful dual (sends `typeCheck` on failure).
        - `.check` / `.validate` — inherited from Sigma (pair check / effectful intro).
        - `.prove term` — checks a term against the genuine subset `_kernel`.

        Membership decides component-wise: `.check`/`.validate` ride a structural
        `Σ x:A. Unit` kernelType (host-decidable without normalizing), with the
        predicate decided at the concrete fst; `_kernel` exposes the real `El t`.
      '';
      tests = CertifiedTests;
    };
    mkPropFamily = api.leaf {
      value = mkPropFamily;
      doc = ''
        Bundle a propositional `family` (`A → U`) with its `bridge` into one
        handle for `Certified`'s general former. Pass it via the `family`
        argument: `Certified { base; family = mkPropFamily { family; bridge; }; }`.
        The two-argument `{ family; bridge; }` form remains valid.
      '';
    };
    Vector = api.leaf {
      value = Vector;
      doc = ''
        Length-indexed list type family, built on Pi.

        ```
        Vector(A) = Π(n:Nat).{xs : List(A) | |xs| = n}
        ```

        This is the correct Martin-Löf encoding: Vector IS a Pi type.
        It inherits `.validate` (effectful), `.compose`, `.apply`, `.domain`, `.codomain`
        from Pi.

        Usage:

        ```nix
        Vector elemType           # the Pi type family (Nat → SizedList)
        (Vector elemType).apply 3 # specific type for length 3
        ```
      '';
      tests = VectorTests;
    };
    DepRecord = api.leaf {
      value = DepRecord;
      doc = ''
        Dependent record type built on nested Sigma.

        Schema is an ordered list of `{ name; type; }` where `type` can be:

        - A Type (static field)
        - A function (`partial-record → Type`) for dependent fields

        Isomorphic to nested Sigma types:

        ```
        { a : A, b : B(a) }              ≅  Σ(a:A).B(a)
        { a : A, b : B(a), c : C(a,b) }  ≅  Σ(a:A).Σ(b:B(a)).C(a,b)
        ```

        Values are nested Sigma pairs:

        ```nix
        { fst = a; snd = { fst = b; snd = c; }; }
        ```

        Inherits from Sigma: `.validate` (effectful), `.proj1`, `.proj2`,
        `.pair`, `.pairE`, `.curry`, `.uncurry`.

        Use `.pack` to convert flat attrset → nested Sigma value.
        Use `.unpack` to convert nested Sigma value → flat attrset.
      '';
      tests = DepRecordTests;
    };

  };
}
