# nix-effects dependent contracts: Pi (Π) and Sigma (Σ)
#
# Higher-order contracts with algebraic effects for dependent type
# constructors, following the MLTT structure of Martin-Löf (1984).
#
# == Architecture: contracts + effects, not weakened MLTT ==
#
# nix-effects types are RUNTIME PREDICATES operating on values, not a
# syntactic type checker operating on terms. This is a fundamentally
# different system from Agda/Lean — not a broken version of their MLTT.
# The correct theoretical framework is:
#
#   - Higher-order contracts (Findler & Felleisen 2002) for the checking
#     strategy: first-order contracts checked immediately, higher-order
#     contracts deferred to elimination sites.
#   - Algebraic effects (Plotkin & Pretnar 2009) for blame tracking and
#     configurable error policy via the typeCheck effect.
#   - Fire Triangle (Pedrot & Tabareau 2020) for the three-level
#     architecture: types as pure values, checking as effects, policy
#     as handlers.
#
# == Handler semantics ==
#
# The handler (Level 3 of the Fire Triangle) determines error policy:
#   strict     — throws on first failure (abort semantics)
#   collecting — accumulates all errors in state (continues with false resume)
#   logging    — records all checks (pass and fail) for observability
#   all-pass   — boolean state = state ∧ passed; canonical for adequacy testing
#
# Known constraint: builtins.tryEval only evaluates to WHNF. When catching
# handler throws, force .value on the result to trigger trampoline execution.
# Cross-type comparison (e.g. "str" > 0) is uncatchable by tryEval — predicates
# must guard input types before comparison operators.
#
# == Types as (Specification, Guard, Verifier) triples ==
#
# Every type constructed by mkType is a triple (S, G, V):
#   S = Specification — the type-theoretic content (name, universe)
#   G = Guard (check) — pure decidable predicate, used for composition
#   V = Verifier (validate) — effectful, sends typeCheck for blame tracking
#
# The adequacy invariant connects them:
#   T.check v ⟺ all typeCheck effects in T.validate v pass
# Tested via the all-pass handler: state = state ∧ (param.type.check param.value)
#
# == First-order vs. higher-order contracts ==
#
# First-order (Sigma, base types): Guard IS full membership. G = ⟦T⟧.
#   Both components of a Sigma pair are concrete data — the full
#   dependent introduction rule is decidable and checked immediately.
#
# Higher-order (Pi): Guard OVER-APPROXIMATES. G ⊋ ⟦Π(x:A).B(x)⟧.
#   A function contract cannot be checked at introduction — only at each
#   elimination site. The guard (isFunction) is the immediate first-order
#   part; checkAt verifies specific applications (the deferred part).
#   This is the standard Findler-Felleisen decomposition for function
#   contracts, not a limitation.
#
# == Two judgment forms ==
#
# There is ONE type system with TWO presentations:
#   Analytic (check):   pure, compositional — Sigma.check calls fst.check
#   Synthetic (validate): effectful, observable — sends typeCheck effects
#
# The pure guard MUST exist because types compose by composing guards.
# Sigma.check calls sub-type checks which must be pure Bool returns, not
# effectful computations. The effectful verifier is built on top for
# observability. They cannot be unified.
#
# == Operations naming convention ==
#
#   check / validate = introduction verification (guard / effectful guard)
#   apply / proj1 / proj2 / checkAt = elimination
#   pair / pairE / certify / certifyE = introduction construction
#
# == MLTT rule mapping ==
#
# Π(x:A).B(x) — Dependent function (Curry-Howard: ∀)
#   Formation:    Pi.value { domain, codomain, universe }
#   Introduction: .check (isFunction), .validate (effectful guard)
#   Elimination:  .apply (pure), .checkAt (deferred contract)
#   Computation:  β-reduction (Nix evaluation)
#
# Σ(x:A).B(x) — Dependent pair (Curry-Howard: ∃)
#   Formation:    Sigma.value { fst, snd, universe }
#   Introduction: .check (exact guard), .validate (decomposed for blame)
#   Elimination:  .proj1, .proj2
#   Computation:  π₁(a,b) ≡ a, π₂(a,b) ≡ b
{ fx, api, ... }:

let
  inherit (api) mk;
  inherit (fx.types.foundation) mkType check;
  inherit (fx.kernel) pure bind send;

  # ===========================================================================
  # PI TYPES (DEPENDENT FUNCTIONS)
  # ===========================================================================

  Pi = mk {
    doc = ''
      Dependent function type Π(x:A).B(x).

      Arguments:
        domain:   Type A
        codomain: A-value → Type (type family B indexed by domain values)
        universe: Universe level (explicit parameter — see below)
        name:     optional display name

      == Higher-order contract with algebraic effects ==

      Pi is a HIGHER-ORDER CONTRACT (Findler & Felleisen 2002). Higher-order
      contracts check function values differently from data values: a data
      contract is verified immediately and completely, but a function contract
      is verified incrementally at each application site. This is the
      standard, correct strategy for function contracts — not a deficit.

      The (Specification, Guard, Verifier) triple for Pi:

        Guard (check):       builtins.isFunction — the immediate first-order
                             part of the contract. Soundly rejects non-functions.
        Verifier (validate): effectful guard (auto-derived, 1 arg) — wraps
                             the guard in a typeCheck effect for blame tracking.
        Elimination (checkAt): deferred contract check (2 args) — verifies a
                             specific application f(arg) by sending typeCheck
                             effects for both domain (arg : A) and codomain
                             (f(arg) : B(arg)).

      This is precisely the Findler-Felleisen decomposition: the immediate
      part (isFunction) is checked at introduction; the deferred part
      (domain + codomain) is checked at each elimination site via checkAt.

      == Adequacy ==

      check f ⟺ all typeCheck effects in (validate f) pass (all-pass handler).
      Both check and validate verify the introduction form (is it a function?).
      checkAt verifies individual applications — the deferred contract.

      == Universe level ==

      Universe level is an explicit parameter. In MLTT, the level is computed
      as max(i, sup_{a:A} level(B(a))) by inspecting the syntax of B. Since
      nix-effects operates on runtime predicates (not syntax trees), the
      universe is declared by the caller.

      == MLTT rule mapping ==

        Formation:          Pi.value { domain, codomain, universe }
        Introduction check: .check (guard: isFunction)
        Introduction verify: .validate (effectful guard, auto-derived)
        Elimination:        .apply (pure), .checkAt (effectful, deferred contract)
        Computation:        β-reduction (Nix evaluation)

      Operations:
        .checkAt f arg   — deferred contract check at elimination site
        .apply arg       — pure elimination: compute codomain type B(arg)
        .compose f other — compose Pi types (requires witness function)
        .domain          — the domain type A
        .codomain        — the type family B
    '';
    value = { domain, codomain, universe, name ? "Π(${domain.name})" }:
      let piType = mkType {
        inherit name universe;
        # Guard: immediate first-order part of the higher-order contract.
        # Soundly rejects non-functions. The deferred part (domain +
        # codomain verification) is checked at elimination sites via
        # .checkAt — standard Findler-Felleisen higher-order contract
        # decomposition.
        check = builtins.isFunction;
      } // {
        inherit domain codomain;

        # Elimination rule: given a : A, compute B(a)
        apply = arg: codomain arg;

        # Pointwise elimination check: verifies a SPECIFIC application f(arg).
        # Sends typeCheck effects for both domain (arg : A) and codomain
        # (f(arg) : B(arg)). This is the ELIMINATION rule — it checks one
        # use of the function, not the introduction form.
        #
        # In higher-order contract terms (Findler & Felleisen 2002): checkAt
        # is deferred contract checking at each application site.
        #
        # Totality: if f is not a function, we send a typeCheck for the Pi
        # type itself. When domain check fails, we short-circuit: f(arg) is
        # never evaluated, because f may crash on wrong-typed arguments.
        # This mirrors the principle that elimination requires valid inputs.
        #
        # checkAt : (A → B(a)) → a → Computation result
        checkAt = f: arg:
          if !(builtins.isFunction f)
          then send "typeCheck" { type = piType; context = "Π check (${name})"; value = f; }
          else
            bind (send "typeCheck" { type = domain; context = "Π domain (${name})"; value = arg; }) (domPassed:
              if domPassed == false then pure null
              else
                let
                  result = f arg;
                  codomainType = codomain arg;
                in
                bind (send "typeCheck" { type = codomainType; context = "Π codomain (${name})"; value = result; }) (_:
                  pure result));

        # Compose Pi types: for this: Π(x:A)→B(x) and other: Π(y:C)→D(y),
        # produce Π(x:A)→D(f(x)). Requires a witness function f inhabiting
        # this Pi type, because the composed codomain depends on f's output.
        compose = f: other:
          Pi.value {
            inherit domain;
            codomain = x: other.codomain (f x);
            universe = other.universe;
            name = "compose(${name}, ${other.name})";
          };
      };
      in piType;
    tests = {
      "pi-accepts-function" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in check piT (x: x + 1);
        expected = true;
      };
      "pi-rejects-non-function" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in check piT 42;
        expected = false;
      };
      "pi-apply-computes-codomain" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            piT = Pi.value {
              domain = IntT;
              codomain = n: if n > 0 then StrT else IntT;
              universe = 0;
            };
          in (piT.apply 5).name;
        expected = "String";
      };
      "pi-apply-codomain-depends-on-value" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            piT = Pi.value {
              domain = IntT;
              codomain = n: if n > 0 then StrT else IntT;
              universe = 0;
            };
          in (piT.apply (-1)).name;
        expected = "Int";
      };
      "pi-checkAt-returns-computation" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in (piT.checkAt (x: x * 2) 21)._tag;
        expected = "Impure";
      };
      "pi-checkAt-first-effect-is-typeCheck" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in (piT.checkAt (x: x * 2) 21).effect.name;
        expected = "typeCheck";
      };
      "pi-checkAt-domain-context" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
            comp = piT.checkAt (x: x * 2) 21;
          in comp.effect.param.context;
        expected = "Π domain (Π(Int))";
      };
      "pi-validate-is-effectful-guard" = {
        # The auto-derived .validate from mkType is the effectful introduction
        # check — it wraps builtins.isFunction in a typeCheck effect.
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in (piT.validate (x: x))._tag;
        expected = "Impure";
      };
      "pi-validate-is-one-arg" = {
        # validate takes ONE arg (the value to check for introduction form).
        # checkAt takes TWO args (function + argument for elimination checking).
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
            comp = piT.validate (x: x);
          in comp.effect.param.context;
        expected = "Π(Int)";
      };
      "pi-checkAt-total-on-non-function" = {
        # Totality: checkAt on a non-function fails through the effect
        # system (sends typeCheck) rather than crashing Nix.
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in (piT.checkAt 42 5)._tag;
        expected = "Impure";
      };
      "pi-checkAt-total-context" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            piT = Pi.value { domain = IntT; codomain = _: IntT; universe = 0; };
          in (piT.checkAt 42 5).effect.param.context;
        expected = "Π check (Π(Int))";
      };
      "pi-compose-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            BoolT = mkType { name = "Bool"; check = builtins.isBool; };
            f = Pi.value { domain = IntT; codomain = _: StrT; name = "f"; universe = 0; };
            g = Pi.value { domain = StrT; codomain = _: BoolT; name = "g"; universe = 0; };
          in (f.compose toString g).name;
        expected = "compose(f, g)";
      };
      "pi-compose-codomain" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            BoolT = mkType { name = "Bool"; check = builtins.isBool; };
            f = Pi.value { domain = IntT; codomain = _: StrT; name = "f"; universe = 0; };
            g = Pi.value { domain = StrT; codomain = _: BoolT; name = "g"; universe = 0; };
            composed = f.compose toString g;
          in (composed.apply 42).name;
        expected = "Bool";
      };
      "pi-non-dependent-is-arrow" = {
        # When B is constant, Π(x:A).B = A → B (ordinary function type)
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            arrowT = Pi.value {
              domain = IntT;
              codomain = _: StrT;
              name = "Int → String";
              universe = 0;
            };
          in arrowT.name;
        expected = "Int → String";
      };
      "pi-universe-explicit" = {
        # Universe is an explicit trusted parameter (not computed as in MLTT)
        # because computing sup_{a:A} codomain(a).universe requires
        # evaluating the codomain on all domain values — undecidable.
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            TypeT = mkType { name = "Type"; check = v: v ? _tag && v._tag == "Type"; universe = 1; };
            # Int → Type lives in Type_1 (maps values to types)
            piT = Pi.value { domain = IntT; codomain = _: TypeT; universe = 1; };
          in piT.universe;
        expected = 1;
      };
    };
  };

  # ===========================================================================
  # SIGMA TYPES (DEPENDENT PAIRS)
  # ===========================================================================

  Sigma = mk {
    doc = ''
      Dependent pair type Σ(x:A).B(x).

      Arguments:
        fst:      Type A — type of the first component
        snd:      A-value → Type — type family for the second component
        universe: Universe level (explicit parameter)
        name:     optional display name

      Values are { fst; snd; } where fst : A and snd : B(fst).

      == First-order contract — guard is exact ==

      Sigma is a FIRST-ORDER CONTRACT: both components are concrete data,
      so the contract is checked immediately and completely. The guard
      (check) IS full membership — there is no over-approximation.

        Guard (check):    fst:A ∧ snd:B(fst) — exact. G = ⟦Σ(x:A).B(x)⟧.
        Verifier (verify): decomposed effectful check — sends separate
                          typeCheck effects for fst and snd for blame tracking.

      This contrasts with Pi where the guard over-approximates (isFunction)
      because functions are higher-order. Sigma pairs are data — the
      dependent relationship (snd's type depends on fst's value) can be
      fully verified because both values are available.

      Adequacy: T.check v ⟺ all typeCheck effects in T.validate v pass
      (under the all-pass handler). The guard is exact and the decomposed
      verifier sends individual typeCheck effects per component — the all-pass
      handler's boolean state tracks whether all passed. Totality: if the input
      is structurally malformed (not an attrset, missing fst/snd), verify falls
      back to a single typeCheck for the whole type — failure goes through the
      effect system, never crashes Nix.

      Universe level is an explicit parameter (computing
      sup_{a:A} snd(a).universe requires evaluating the type family on
      all domain values, same as Pi).

      == MLTT rule mapping ==

        Formation:    Sigma.value { fst, snd, universe }
        Introduction: .check (exact guard), .validate (effectful, decomposed)
        Elimination:  .proj1 (π₁), .proj2 (π₂)
        Computation:  π₁(a,b) ≡ a, π₂(a,b) ≡ b

      Operations:
        .proj1 pair    — first projection π₁
        .proj2 pair    — second projection π₂
        .pair a b      — smart constructor (throws on invalid)
        .validate v    — effectful: decomposed typeCheck effects for blame
        .pairE a b     — effectful smart constructor
        .pullback f g  — contravariant predicate pullback (see below)
        .curry / .uncurry — standard Sigma adjunction
        .fstType       — the type A
        .sndFamily     — the type family B
    '';
    value = { fst, snd, universe, name ? "Σ(${fst.name})" }:
      mkType {
        inherit name universe;
        # Guard: exact first-order contract. Both components are concrete
        # data, so the full dependent introduction rule is decidable.
        check = v:
          builtins.isAttrs v
          && v ? fst && v ? snd
          && fst.check v.fst
          && (snd v.fst).check v.snd;
        # Custom verifier: recursively validates sub-components via their own
        # .validate (not atomic .check) for deep blame tracking. A Sigma with
        # ListOf fst produces per-element typeCheck effects — the handler sees
        # the full recursive decomposition (Findler & Felleisen 2002) and can
        # attribute blame at the leaf level.
        #
        # Totality: structurally malformed inputs (not an attrset, missing
        # fst/snd) fall back to a single typeCheck for the whole type.
        # When fst fails (via pure .check after effectful .validate), we
        # short-circuit: the snd type family (snd v.fst) is never evaluated,
        # because it may crash on wrong-typed fst values.
        #
        # The .validate → .check pattern: validate produces deep effects
        # (per-element errors for collecting handler), then .check (pure,
        # memoized by Nix) gives the boolean for short-circuit.
        verify = self: v:
          if !(builtins.isAttrs v && v ? fst && v ? snd)
          then send "typeCheck" { type = self; context = "Σ (${name})"; value = v; }
          else
            bind (fst.validate v.fst) (_:
              if fst.check v.fst == false then pure v
              else
                let sndType = snd v.fst;
                in bind (sndType.validate v.snd) (_:
                  pure v));
      } // {
        fstType = fst;
        sndFamily = snd;

        # π₁ : Σ(x:A).B(x) → A
        proj1 = p: p.fst;

        # π₂ : (p : Σ(x:A).B(x)) → B(π₁(p))
        proj2 = p: p.snd;

        # Smart constructor with dependent validation (throws — for pure contexts)
        pair = fstVal: sndVal:
          if !(fst.check fstVal)
          then builtins.throw "Σ type ${name}: fst does not inhabit ${fst.name}"
          else if !((snd fstVal).check sndVal)
          then builtins.throw "Σ type ${name}: snd does not inhabit ${(snd fstVal).name}"
          else { fst = fstVal; snd = sndVal; };

        # Effectful smart constructor. Recursively validates sub-components
        # for deep blame tracking. Short-circuits on fst failure:
        # the snd type family is never evaluated on wrong-typed fst.
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

        # Contravariant predicate pullback on Sigma types.
        #
        # Given transforms f and g, creates a new Sigma type that accepts
        # (x, y) iff the original accepts (f(x), g(y)). This is the
        # PREIMAGE/PULLBACK — not a covariant bimap.
        #
        # In category theory: types-as-predicates are contravariant functors
        # (a predicate P : X → Bool can be pulled back along f : Y → X to
        # give P ∘ f : Y → Bool). A covariant bimap would map VALUES forward:
        # (a,b) ↦ (f(a), g(b)) — but predicates can only pull back, not push
        # forward, because they test membership, not construct inhabitants.
        #
        # Composition law (contravariant):
        #   pullback (f∘g) (h∘k) = pullback g k >>> pullback f h
        # Note the REVERSED order vs. covariant bimap.
        pullback = f: g: Sigma.value {
          fst = mkType {
            name = "${fst.name}'";
            check = v: fst.check (f v);
            inherit (fst) universe;
          };
          snd = x:
            let orig = snd (f x);
            in mkType {
              name = "${orig.name}'";
              check = v: orig.check (g v);
              inherit (orig) universe;
            };
          name = "pullback(${name})";
          inherit universe;
        };
      };
    tests = {
      "sigma-accepts-valid-pair" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value {
              fst = IntT;
              snd = n: mkType {
                name = "List[${toString n}]";
                check = v: builtins.isList v && builtins.length v == n;
              };
              universe = 0;
            };
          in check sigT { fst = 2; snd = [ "a" "b" ]; };
        expected = true;
      };
      "sigma-rejects-dependent-mismatch" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value {
              fst = IntT;
              snd = n: mkType {
                name = "List[${toString n}]";
                check = v: builtins.isList v && builtins.length v == n;
              };
              universe = 0;
            };
          in check sigT { fst = 3; snd = [ "a" "b" ]; };
        expected = false;
      };
      "sigma-rejects-bad-fst" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value {
              fst = IntT;
              snd = _: IntT;
              universe = 0;
            };
          in check sigT { fst = "nope"; snd = 0; };
        expected = false;
      };
      "sigma-proj1" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in sigT.proj1 { fst = 42; snd = 0; };
        expected = 42;
      };
      "sigma-proj2" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in sigT.proj2 { fst = 0; snd = 42; };
        expected = 42;
      };
      "sigma-validate-returns-computation" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in (sigT.validate { fst = 1; snd = 2; })._tag;
        expected = "Impure";
      };
      "sigma-validate-effect-is-typeCheck" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in (sigT.validate { fst = 1; snd = 2; }).effect.name;
        expected = "typeCheck";
      };
      "sigma-validate-total-on-non-attrset" = {
        # Totality: validate on a non-attrset fails through the effect
        # system rather than crashing Nix.
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in (sigT.validate 42)._tag;
        expected = "Impure";
      };
      "sigma-validate-total-on-missing-fields" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in (sigT.validate { x = 1; })._tag;
        expected = "Impure";
      };
      "sigma-pairE-returns-computation" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in (sigT.pairE 1 2)._tag;
        expected = "Impure";
      };
      "sigma-curry-uncurry" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
            add = sigT.curry (p: p.fst + p.snd);
            addPair = sigT.uncurry (a: b: a + b);
          in { curried = add 3 4; uncurried = addPair { fst = 3; snd = 4; }; };
        expected = { curried = 7; uncurried = 7; };
      };
      "sigma-non-dependent-is-product" = {
        # When B is constant, Σ(x:A).B = A × B (ordinary product)
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            prodT = Sigma.value {
              fst = IntT;
              snd = _: StrT;
              name = "Int × String";
              universe = 0;
            };
          in check prodT { fst = 42; snd = "hello"; };
        expected = true;
      };
      "sigma-pullback-name" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; name = "IntPair"; universe = 0; };
          in (sigT.pullback (x: x) (x: x)).name;
        expected = "pullback(IntPair)";
      };
      "sigma-has-pullback" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            sigT = Sigma.value { fst = IntT; snd = _: IntT; universe = 0; };
          in sigT ? pullback;
        expected = true;
      };
    };
  };

  # ===========================================================================
  # CERTIFIED VALUES (Σ WITH PROOF WITNESS)
  # ===========================================================================
  #
  # Certified(A, P) = Σ(v:A).{p : Bool | p ∧ P(v)}
  # A dependent pair of a value and a witness that a predicate holds.
  # The witness is `true` — the predicate is checked at construction time.

  Certified = mk {
    doc = ''
      Certified value: Σ(v:A).Proof(P(v)).

      A dependent pair where:
        fst : A              — the value
        snd : true           — proof witness (must be true AND predicate must hold)

      The second component's type depends on the first: it checks both
      that the proof is `true` and that predicate(fst) holds.

      Certified is a first-order contract — both components are concrete
      data, so the contract is checked immediately and completely (like
      Sigma). The guard IS full membership.

      Construction:
        .certify v   — pure smart constructor (throws on invalid)
        .certifyE v  — effectful smart constructor (sends typeCheck effects)
        .check       — inherited from Sigma (full dependent pair check)
        .validate    — inherited from Sigma (effectful introduction check)

      The .certifyE constructor is NOT an introduction check — it's a
      convenience that takes a raw value, evaluates the predicate, and
      produces the Sigma pair { fst = v; snd = true; }. The actual
      introduction check (.validate) is inherited from Sigma and verifies
      an already-formed pair.
    '';
    value = { base, predicate, name ? "Certified(${base.name})" }:
      Sigma.value {
        fst = base;
        snd = v: mkType {
          name = "Proof(${name})";
          check = proof: proof == true && predicate v;
        };
        inherit name;
        inherit (base) universe;
      } // {
        # Pure smart constructor: evaluate predicate and build pair (throws on invalid)
        certify = v:
          if !(base.check v)
          then builtins.throw "Certified ${name}: value does not inhabit ${base.name}"
          else if !(predicate v)
          then builtins.throw "Certified ${name}: predicate failed"
          else { fst = v; snd = true; };

        # Effectful smart constructor: recursively validates the base type
        # (for deep blame if base is compound), then evaluates the predicate.
        # This is NOT the introduction check (that's .validate, inherited
        # from Sigma) — it's a convenience for constructing certified values
        # with blame tracking.
        #
        # Short-circuits on base failure: if v doesn't inhabit the base type,
        # the predicate is never evaluated (it may crash on wrong-typed input,
        # e.g., cross-type comparison which tryEval cannot catch).
        certifyE = v:
          bind (base.validate v) (_:
            if base.check v == false then pure { fst = v; snd = true; }
            else
              let
                proofType = mkType {
                  name = "Proof(${name})";
                  check = (proof: proof == true && predicate v);
                };
                # Guard against throwing predicates: if predicate crashes, catch it
                # and pass false to the typeCheck effect. The handler sees a failed
                # proof check instead of a Nix-level crash.
                predResult = builtins.tryEval (predicate v);
                predValue = if predResult.success then predResult.value else false;
              in bind (send "typeCheck" { type = proofType; context = "Certified predicate (${name})"; value = predValue; }) (_:
                pure { fst = v; snd = true; }));
      };
    tests = {
      "certified-accepts-valid-proof" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in check PosInt { fst = 5; snd = true; };
        expected = true;
      };
      "certified-rejects-failing-predicate" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in check PosInt { fst = -1; snd = true; };
        expected = false;
      };
      "certified-rejects-false-proof" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in check PosInt { fst = 5; snd = false; };
        expected = false;
      };
      "certified-certifyE-returns-computation" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in (PosInt.certifyE 5)._tag;
        expected = "Impure";
      };
      "certified-certifyE-effect-is-typeCheck" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in (PosInt.certifyE 5).effect.name;
        expected = "typeCheck";
      };
      "certified-inherits-sigma-validate" = {
        # Certified inherits .validate from Sigma — this is the introduction
        # check for the pair, NOT the smart constructor. It takes an
        # already-formed pair and verifies it effectfully.
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
          in (PosInt.validate { fst = 5; snd = true; })._tag;
        expected = "Impure";
      };
      "certify-constructs-valid-pair" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            PosInt = Certified.value {
              base = IntT;
              predicate = x: x > 0;
              name = "PosInt";
            };
            pair = PosInt.certify 5;
          in pair.fst == 5 && pair.snd == true;
        expected = true;
      };
    };
  };

  # ===========================================================================
  # VECTOR (LENGTH-INDEXED LIST — CANONICAL DEPENDENT CONTRACT EXAMPLE)
  # ===========================================================================

  # NatT — non-negative integer type used by Vector as domain
  NatT = mkType { name = "Nat"; check = v: builtins.isInt v && v >= 0; };

  Vector = mk {
    doc = ''
      Length-indexed list type family, built ON Pi.

      Vector(A) = Π(n:Nat).{xs : List(A) | |xs| = n}

      This is the correct Martin-Löf encoding: Vector IS a Pi type.
      It inherits .validate (effectful), .compose, .apply, .domain, .codomain
      from Pi.

      Usage:
        Vector elemType       — the Pi type family (Nat → SizedList)
        (Vector elemType).apply 3  — specific type for length 3
    '';
    value = elemType:
      Pi.value {
        domain = NatT;
        codomain = n: mkType {
          name = "Vector[${toString n}, ${elemType.name}]";
          check = v:
            builtins.isList v
            && builtins.length v == n
            && builtins.all elemType.check v;
        };
        name = "Vector(${elemType.name})";
        universe = 0;
      };
    tests = {
      "vector-is-pi-type" = {
        expr =
          let IntT = mkType { name = "Int"; check = builtins.isInt; };
          in (Vector.value IntT) ? validate;
        expected = true;
      };
      "vector-apply-gives-specific-type" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            v3i = (Vector.value IntT).apply 3;
          in check v3i [1 2 3];
        expected = true;
      };
      "vector-apply-rejects-wrong-length" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            v3i = (Vector.value IntT).apply 3;
          in check v3i [1 2];
        expected = false;
      };
      "vector-apply-rejects-wrong-element-type" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            v3i = (Vector.value IntT).apply 3;
          in check v3i [1 "two" 3];
        expected = false;
      };
      "vector-zero-accepts-empty" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            v0 = (Vector.value IntT).apply 0;
          in check v0 [];
        expected = true;
      };
      "vector-has-compose" = {
        expr =
          let IntT = mkType { name = "Int"; check = builtins.isInt; };
          in (Vector.value IntT) ? compose;
        expected = true;
      };
      "vector-check-is-function" = {
        # The Pi type's introduction form check: Vector values are functions
        # (from Nat to sized lists). This is the type-theoretic view.
        expr =
          let IntT = mkType { name = "Int"; check = builtins.isInt; };
          in check (Vector.value IntT) (n: builtins.genList (_: 0) n);
        expected = true;
      };
    };
  };

  # ===========================================================================
  # DEPENDENT RECORD (N-ARY SIGMA ENCODING)
  # ===========================================================================
  #
  # An n-ary dependent record is isomorphic to nested Sigma:
  #   { a : A, b : B(a), c : C(a,b) }  ≅  Σ(a:A).Σ(b:B(a)).C(a,b)
  #
  # Values are nested Sigma pairs: { fst = a; snd = { fst = b; snd = c; }; }
  # This gives DepRecord full Sigma inheritance: .validate (effectful),
  # .proj1, .proj2, .pair, .pairE, .curry, .uncurry.

  # Unit type for the terminal case of nested Sigma
  UnitT = mkType { name = "Unit"; check = v: v == null; };

  DepRecord = mk {
    doc = ''
      Dependent record type built on nested Sigma.

      Schema is an ordered list of { name; type; } where type can be:
        - A Type (static field)
        - A function (partial-record → Type) for dependent fields

      Isomorphic to nested Sigma types:
        { a : A, b : B(a) }  ≅  Σ(a:A).B(a)
        { a : A, b : B(a), c : C(a,b) }  ≅  Σ(a:A).Σ(b:B(a)).C(a,b)

      Values are nested Sigma pairs:
        { fst = a; snd = { fst = b; snd = c; }; }

      Inherits from Sigma: .validate (effectful), .proj1, .proj2,
      .pair, .pairE, .curry, .uncurry.

      Use .pack to convert flat attrset → nested Sigma value.
      Use .unpack to convert nested Sigma value → flat attrset.
    '';
    value = fields:
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
            in Sigma.value {
              fst = fieldType;
              snd = v: buildSigma rest (partial // { ${field.name} = v; });
              name = "DepRec{${namesStr}}.${field.name}";
              universe = fieldType.universe;
            };

        sigmaType = buildSigma fields {};

        # Convert flat attrset → nested Sigma value
        packFields = remaining: v:
          if builtins.length remaining == 0 then
            null
          else if builtins.length remaining == 1 then
            v.${(builtins.head remaining).name}
          else
            let field = builtins.head remaining;
                rest = builtins.tail remaining;
            in { fst = v.${field.name}; snd = packFields rest v; };

        # Convert nested Sigma value → flat attrset
        unpackFields = remaining: packed:
          if builtins.length remaining == 0 then
            {}
          else if builtins.length remaining == 1 then
            { ${(builtins.head remaining).name} = packed; }
          else
            let field = builtins.head remaining;
                rest = builtins.tail remaining;
            in { ${field.name} = packed.fst; } // unpackFields rest packed.snd;

      in sigmaType // {
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
    tests = {
      "deprec-sigma-accepts-nested-pair" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "s"; type = StrT; }
            ];
          # Nested Sigma pair: { fst = 2; snd = "hello"; }
          in check recT { fst = 2; snd = "hello"; };
        expected = true;
      };
      "deprec-sigma-rejects-bad-type" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "s"; type = StrT; }
            ];
          in check recT { fst = "not-int"; snd = "hello"; };
        expected = false;
      };
      "deprec-dependent-field" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "items"; type = (self:
                mkType {
                  name = "List[n=${toString self.n}]";
                  check = v: builtins.isList v && builtins.length v == self.n;
                });
              }
            ];
          # { fst = 2; snd = ["a" "b"]; } — snd type depends on fst
          in check recT { fst = 2; snd = [ "a" "b" ]; };
        expected = true;
      };
      "deprec-dependent-mismatch" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "items"; type = (self:
                mkType {
                  name = "List[n=${toString self.n}]";
                  check = v: builtins.isList v && builtins.length v == self.n;
                });
              }
            ];
          in check recT { fst = 3; snd = [ "a" "b" ]; };
        expected = false;
      };
      "deprec-has-validate" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "s"; type = StrT; }
            ];
          in recT ? validate;
        expected = true;
      };
      "deprec-pack-unpack" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "s"; type = StrT; }
            ];
            flat = { n = 42; s = "hello"; };
            packed = recT.pack flat;
            unpacked = recT.unpack packed;
          in unpacked;
        expected = { n = 42; s = "hello"; };
      };
      "deprec-checkFlat" = {
        expr =
          let
            IntT = mkType { name = "Int"; check = builtins.isInt; };
            StrT = mkType { name = "String"; check = builtins.isString; };
            recT = DepRecord.value [
              { name = "n"; type = IntT; }
              { name = "s"; type = StrT; }
            ];
          in recT.checkFlat { n = 42; s = "hello"; };
        expected = true;
      };
    };
  };

in mk {
  doc = ''
    Dependent contracts: Pi (Π), Sigma (Σ), Certified, Vector, DepRecord.
    Grounded in Martin-Löf (1984) "Intuitionistic Type Theory".
  '';
  value = {
    inherit Pi Sigma Certified Vector DepRecord;
  };
}
