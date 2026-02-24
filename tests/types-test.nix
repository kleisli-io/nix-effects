# nix-effects type system integration tests
#
# Tests 1-10:  Core types — refinement, Vector, universe hierarchy, Record,
#              Maybe, DepRecord, make, Variant, predicates, universe safety
# Tests 11-15: Effectful type checking — Pi.checkAt effects, strict handler,
#              collecting handler, logging handler, same-comp-different-handler
# Tests 16-25: Semantic unification — Sigma/Certified/Vector/DepRecord through
#              handlers, foundation.validate
# Tests 26-33: Adequacy & contracts — guard/verifier agreement for Pi, Sigma,
#              Certified, DepRecord, primitives, Vector; checkAt vs validate
# Tests 34-46: Edge cases — malformed inputs, Pi domain failure, certifyE
#              crash/wrong-base, pairE, compose+checkAt, handler diversity
# Tests 47-50: Short-circuit totality — crash-path guard (Sigma with crashing
#              snd family), adequacy on short-circuit path, Pi.checkAt
#              short-circuit, universe trust boundary
{ lib, fx }:

let
  inherit (fx) types;
  H = types.hoas;

  # All-pass handler: the canonical handler for testing the adequacy invariant.
  # Resumes with the check result so computation proceeds naturally, while
  # tracking via boolean state whether ALL typeCheck effects passed.
  #
  # Adequacy invariant: T.check v ⟺ (allPassHandle(T.validate v)).state
  allPassHandle = comp:
    fx.handle {
      handlers.typeCheck = { param, state }:
        let passed = param.type.check param.value;
        in { resume = passed; state = state && passed; };
      state = true;
    } comp;

  # -- Test 1: ValidPort refinement type --
  validPortTest =
    let
      ValidPort = types.refined "ValidPort" types.Int (types.inRange 1 65535);
    in types.check ValidPort 8080
       && !(types.check ValidPort 99999)
       && !(types.check ValidPort 0)
       && !(types.check ValidPort (-1));

  # -- Test 2: Vector 3 Int (Vector is now a Pi type family) --
  vectorTest =
    let V3I = (types.Vector types.Int).apply 3;
    in types.check V3I [1 2 3]
       && !(types.check V3I [1 2])
       && !(types.check V3I [1 2 3 4])
       && !(types.check V3I [1 "two" 3]);

  # -- Test 3: Universe hierarchy --
  universeTest =
    types.check types.Type_1 types.Type_0
    && types.check types.Type_2 types.Type_1
    && !(types.check types.Type_0 types.Type_0)
    && !(types.check types.Type_1 types.Type_1);

  # -- Test 4: Record + refinement composition --
  recordRefinementTest =
    let
      ServiceConfig = types.Record {
        name = types.String;
        port = types.refined "ValidPort" types.Int (types.inRange 1 65535);
      };
    in types.check ServiceConfig { name = "nginx"; port = 443; }
       && !(types.check ServiceConfig { name = "nginx"; port = 99999; })
       && !(types.check ServiceConfig { name = "nginx"; });

  # -- Test 5: Maybe type --
  maybeTest =
    let MaybeInt = types.Maybe types.Int;
    in types.check MaybeInt null
       && types.check MaybeInt 42
       && !(types.check MaybeInt "hello");

  # -- Test 6: Dependent record (nested Sigma pairs) --
  depRecordTest =
    let
      SizedList = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "items"; type = (self:
          types.mkType {
            name = "List[n=${toString self.n}]";
            kernelType = H.any;
            guard = v: builtins.isList v && builtins.length v == self.n;
          });
        }
      ];
    # Values are now nested Sigma: { fst = n; snd = items; }
    in types.check SizedList { fst = 2; snd = [ "a" "b" ]; }
       && !(types.check SizedList { fst = 3; snd = [ "a" "b" ]; });

  # -- Test 7: make throws on invalid --
  makeThrowsTest =
    let
      result = builtins.tryEval (types.make types.Int "not-an-int");
    in !result.success;

  # -- Test 8: Variant type --
  variantTest =
    let
      Shape = types.Variant {
        circle = types.Float;
        rect = types.Record { w = types.Float; h = types.Float; };
      };
    in types.check Shape { _tag = "circle"; value = 5.0; }
       && types.check Shape { _tag = "rect"; value = { w = 3.0; h = 4.0; }; }
       && !(types.check Shape { _tag = "triangle"; value = null; });

  # -- Test 9: Predicate combinators --
  predicateTest =
    let
      EvenPositive = types.refined "EvenPositive" types.Int
        (types.allOf [ types.positive (x: lib.mod x 2 == 0) ]);
    in types.check EvenPositive 4
       && !(types.check EvenPositive 3)
       && !(types.check EvenPositive (-2));

  # -- Test 10: Universe tower safety --
  universeSafetyTest =
    let
      noSelfMembership = !(types.check (types.typeAt 5) (types.typeAt 5));
      chain = types.check types.Type_2 types.Type_1
              && types.check types.Type_1 types.Type_0;
    in noSelfMembership && chain;

  # ===========================================================================
  # EFFECTFUL TYPE CHECKING TESTS
  # ===========================================================================
  #
  # These demonstrate the core innovation: type checking IS an algebraic effect.
  # Same computation, different handler, different behavior.
  # Per Pedrot & Tabareau "Fire Triangle" (POPL 2020).

  # -- Test 11: Pi.checkAt returns Computation with typeCheck effect --
  piCheckAtIsEffectful =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
    in comp._tag == "Impure"
       && comp.effect.name == "typeCheck"
       && comp.effect.param.type.name == "Int";

  # -- Test 12: Strict handler — passes when types match --
  strictHandlerPassesTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else throw "Type error in ${param.context}: expected ${param.type.name}";
      } comp;
    in result.value == 42;

  # -- Test 13: Collecting handler — gathers codomain error --
  collectingHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # f returns int (42), but codomain expects String → codomain check fails
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [{ context = param.context; expected = param.type.name; }]; };
        state = [];
      } comp;
    in builtins.length result.state == 1
       && (builtins.head result.state).expected == "String";

  # -- Test 14: Logging handler — records ALL checks --
  loggingHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle {
        handlers.typeCheck = { param, state }: {
          resume = (param.type.check param.value);
          state = state ++ [{
            context = param.context;
            passed = (param.type.check param.value);
          }];
        };
        state = [];
      } comp;
    # Both domain (Int check on 21) and codomain (Int check on 42) pass
    in builtins.length result.state == 2
       && (builtins.elemAt result.state 0).passed
       && (builtins.elemAt result.state 1).passed;

  # -- Test 15: Same computation, different handler, different outcome --
  sameCompDifferentHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # This computation has a codomain error (42 is not a String)
      comp = piT.checkAt (x: x * 2) 21;

      # Handler A: collecting (gathers errors)
      collectResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } comp;

      # Handler B: logging (records all checks, no errors)
      logResult = fx.handle {
        handlers.typeCheck = { param, state }: {
          resume = (param.type.check param.value);
          state = state ++ [(param.type.check param.value)];
        };
        state = [];
      } comp;
    in
      # Collecting handler: 1 error (codomain)
      builtins.length collectResult.state == 1
      # Logging handler: 2 entries (domain + codomain), second is false
      && builtins.length logResult.state == 2
      && builtins.elemAt logResult.state 0 == true   # domain passes
      && builtins.elemAt logResult.state 1 == false;  # codomain fails

  # -- Test 16: Sigma.validate is effectful --
  sigmaValidateIsEffectful =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.Int; universe = 0; };
      comp = sigT.validate { fst = 1; snd = 2; };
    in comp._tag == "Impure"
       && comp.effect.name == "typeCheck";

  # -- Test 17: Sigma.validate through strict handler --
  sigmaStrictHandlerTest =
    let
      sigT = types.Sigma {
        fst = types.Int;
        snd = n: types.mkType {
          name = "List[${toString n}]";
          kernelType = H.any;
          guard = v: builtins.isList v && builtins.length v == n;
        };
        universe = 0;
      };
      comp = sigT.validate { fst = 2; snd = [ "a" "b" ]; };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else throw "Type error: ${param.context}";
      } comp;
    in result.value == { fst = 2; snd = [ "a" "b" ]; };

  # -- Test 18: Certified.certifyE is effectful --
  certifiedCertifyETest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = x: x > 0;
        name = "PosInt";
      };
      comp = PosInt.certifyE 5;
    in comp._tag == "Impure"
       && comp.effect.name == "typeCheck";

  # -- Test 19: Certified.certifyE through collecting handler --
  certifiedCertifyECollectingTest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = x: x > 0;
        name = "PosInt";
      };
      comp = PosInt.certifyE 5;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } comp;
    in result.value == { fst = 5; snd = true; }
       && builtins.length result.state == 0;  # no errors

  # -- Test 20: Certified.certifyE failing predicate through collecting handler --
  certifiedCertifyEFailTest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = x: x > 0;
        name = "PosInt";
      };
      # -5 is int (base passes) but predicate fails
      comp = PosInt.certifyE (-5);
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } comp;
    in builtins.length result.state == 1;  # predicate check fails

  # -- Test 21: Vector-as-Pi has checkAt, validate, and other Pi operations --
  vectorIsEffectful =
    let
      vecFamily = types.Vector types.Int;
    in vecFamily ? validate
       && vecFamily ? checkAt
       && vecFamily ? compose
       && vecFamily ? apply
       && vecFamily ? domain
       && vecFamily ? codomain;

  # -- Test 22: Vector.checkAt through strict handler --
  vectorCheckAtStrictTest =
    let
      vecFamily = types.Vector types.Int;
      # A function from Nat to sized lists — a valid Vector value
      mkList = n: builtins.genList (i: i) n;
      comp = vecFamily.checkAt mkList 3;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else throw "Type error: ${param.context}";
      } comp;
    in result.value == [0 1 2];

  # -- Test 23: DepRecord-as-Sigma has validate (effectful) --
  depRecordIsEffectful =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in recT ? validate && recT ? proj1 && recT ? proj2;

  # -- Test 24: DepRecord.validate through strict handler --
  depRecordValidateStrictTest =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      # Nested Sigma value: { fst = 42; snd = "hello"; }
      comp = recT.validate { fst = 42; snd = "hello"; };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else throw "Type error: ${param.context}";
      } comp;
    in result.value == { fst = 42; snd = "hello"; };

  # -- Test 25: foundation.validate is now effectful (not result attrset) --
  foundationValidateIsEffectful =
    let
      comp = types.validate types.Int 42 "test-context";
    in comp._tag == "Impure"
       && comp.effect.name == "typeCheck"
       && comp.effect.param.context == "test-context";

  # ===========================================================================
  # ADEQUACY AND CONTRACT TESTS
  # ===========================================================================
  #
  # These demonstrate the formal framework: one type system, two judgment
  # forms (guard/verifier), connected by the adequacy invariant.

  # -- Test 26: Pi.validate is the effectful guard (1 arg, auto-derived) --
  piValidateIsGuard =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # validate takes ONE arg (the value to check as introduction form)
      comp = piT.validate (x: x);
    in comp._tag == "Impure"
       && comp.effect.name == "typeCheck"
       # The context is the type name, not "Π domain" — it's the guard,
       # not the elimination check
       && comp.effect.param.context == "Π(Int)";

  # -- Test 27: Pi adequacy — check and validate agree --
  piAdequacy =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      f = x: x * 2;
      notF = 42;
      # Trivial handler: resumes with check result
      trivialHandle = comp: (fx.handle {
        handlers.typeCheck = { param, state }: {
          resume = param.type.check param.value;
          inherit state;
        };
      } comp).value;
    in
      # Adequacy: check f = true ⟺ validate f succeeds (returns true)
      (types.check piT f) == (trivialHandle (piT.validate f))
      # Adequacy: check notF = false ⟺ validate notF fails (returns false)
      && (types.check piT notF) == (trivialHandle (piT.validate notF));

  # -- Test 28: Sigma adequacy — check and validate agree --
  #
  # Sigma has a CUSTOM verifier that returns `pure v` (the original pair),
  # not a bool. The adequacy invariant uses the all-pass handler's boolean
  # state, not result.value, to uniformly test all type constructors.
  sigmaAdequacy =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      good = { fst = 42; snd = "hello"; };
      bad = { fst = 42; snd = 99; };
    in
      # Good pair: check passes, all effects pass
      (types.check sigT good) == (allPassHandle (sigT.validate good)).state
      # Bad pair: check fails, some effect fails
      && (types.check sigT bad) == (allPassHandle (sigT.validate bad)).state;

  # -- Test 29: checkAt differs from validate — a bad function passes
  #    validate (it IS a function) but fails checkAt (wrong codomain) --
  piCheckAtDiffersFromValidate =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # This IS a function (passes guard), but returns Int not String
      badF = x: x * 2;
      # validate (guard): passes — it's a function
      guardResult = fx.handle {
        handlers.typeCheck = { param, state }: {
          resume = param.type.check param.value;
          inherit state;
        };
      } (piT.validate badF);
      # checkAt (deferred contract): fails at codomain
      checkAtResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; state = state ++ ["pass"]; }
          else { resume = false; state = state ++ ["fail:${param.context}"]; };
        state = [];
      } (piT.checkAt badF 21);
    in
      # Guard passes (it IS a function)
      guardResult.value == true
      # Deferred contract: domain passes (21 is Int), codomain fails (42 is not String)
      && builtins.length checkAtResult.state == 2
      && builtins.elemAt checkAtResult.state 0 == "pass"
      && builtins.elemAt checkAtResult.state 1 == "fail:Π codomain (Π(Int))";

  # -- Test 30: Certified adequacy — check and validate agree --
  certifiedAdequacy =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = x: x > 0;
        name = "PosInt";
      };
      good = { fst = 5; snd = true; };
      bad = { fst = -1; snd = true; };
    in
      (types.check PosInt good) == (allPassHandle (PosInt.validate good)).state
      && (types.check PosInt bad) == (allPassHandle (PosInt.validate bad)).state;

  # -- Test 31: DepRecord adequacy — check and validate agree --
  depRecordAdequacy =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      good = { fst = 42; snd = "hello"; };
      bad = { fst = "nope"; snd = "hello"; };
    in
      (types.check recT good) == (allPassHandle (recT.validate good)).state
      && (types.check recT bad) == (allPassHandle (recT.validate bad)).state;

  # -- Test 32: Primitive (Int) adequacy — auto-derived validate --
  primitiveAdequacy =
    (types.check types.Int 42) == (allPassHandle (types.Int.validate 42)).state
    && (types.check types.Int "bad") == (allPassHandle (types.Int.validate "bad")).state;

  # -- Test 33: Vector (Pi-based) adequacy — auto-derived validate --
  vectorAdequacy =
    let
      vecFamily = types.Vector types.Int;
      good = n: builtins.genList (i: i) n;
      bad = 42;
    in
      (types.check vecFamily good) == (allPassHandle (vecFamily.validate good)).state
      && (types.check vecFamily bad) == (allPassHandle (vecFamily.validate bad)).state;

  # ===========================================================================
  # EXHAUSTIVE EDGE-CASE TESTS
  # ===========================================================================

  # -- Test 34: Sigma.validate on empty attrset --
  sigmaValidateEmpty =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in (allPassHandle (sigT.validate {})).state == false;

  # -- Test 35: Sigma.validate on {fst=1} (missing snd) --
  sigmaValidateMissingSnd =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in (allPassHandle (sigT.validate { fst = 1; })).state == false;

  # -- Test 36: Sigma.validate on {snd=1} (missing fst) --
  sigmaValidateMissingFst =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in (allPassHandle (sigT.validate { snd = 1; })).state == false;

  # -- Test 37: Sigma.validate wrong snd through collecting handler --
  # Deep recursive validation: snd type's own validate produces the context
  sigmaValidateWrongSnd =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.Int; universe = 0; };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (sigT.validate { fst = 1; snd = "wrong"; });
    in
      builtins.length result.state == 1
      && builtins.head result.state == "Int";

  # -- Test 38: Pi.checkAt domain failure — strict handler throws --
  piCheckAtDomainFailure =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # Force .value to trigger trampoline execution (tryEval only evals to WHNF)
      result = builtins.tryEval ((fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else builtins.throw "Type error: ${param.context}";
      } (piT.checkAt (x: x * 2) "not-int")).value);
    in !result.success;

  # -- Test 39: certifyE with crashing predicate — caught by tryEval guard --
  certifyECrashingPredicate =
    let
      CrashType = types.Certified {
        base = types.Int;
        predicate = _: builtins.throw "crash";
        name = "CrashType";
      };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (CrashType.certifyE 5);
    in
      # Base passes (5 is Int), predicate crash caught → proof check fails
      builtins.length result.state == 1
      && builtins.head result.state == "Certified predicate (CrashType)";

  # -- Test 40: certifyE with wrong base type --
  # certifyE short-circuits on base failure: predicate is never evaluated
  # (it may crash on wrong-typed input via uncatchable cross-type comparison).
  certifyEWrongBase =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = x: builtins.isInt x && x > 0;
        name = "PosInt";
      };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (PosInt.certifyE "not-int");
    in
      # Base fails → short-circuit, predicate never evaluated
      builtins.length result.state == 1
      && builtins.elemAt result.state 0 == "Int";

  # -- Test 41: DepRecord.validate non-attrset --
  depRecordValidateNonAttrset =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in (allPassHandle (recT.validate 42)).state == false;

  # -- Test 42: DepRecord.validate missing field --
  depRecordValidateMissingField =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in (allPassHandle (recT.validate { fst = 42; })).state == false;

  # -- Test 43: DepRecord.validate wrong field types --
  # DepRecord inherits Sigma's short-circuit: when fst fails, snd type
  # family is never evaluated (it depends on fst value being well-typed).
  depRecordValidateWrongTypes =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (recT.validate { fst = "wrong"; snd = 42; });
    in
      # fst fails → short-circuit, snd type family never evaluated
      builtins.length result.state == 1;

  # -- Test 44: pairE through handlers — success and failure --
  pairEThroughHandlers =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      goodResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else builtins.throw "Type error: ${param.context}";
      } (sigT.pairE 42 "hello");
      badResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (sigT.pairE 42 99);
    in
      goodResult.value == { fst = 42; snd = "hello"; }
      && builtins.length badResult.state == 1
      && builtins.head badResult.state == "String";

  # -- Test 45: Pi compose + checkAt interaction --
  composeCheckAt =
    let
      piF = types.Pi { domain = types.Int; codomain = _: types.String; name = "f"; universe = 0; };
      piG = types.Pi { domain = types.String; codomain = _: types.Int; name = "g"; universe = 0; };
      composed = piF.compose toString piG;
      comp = composed.checkAt (x: builtins.stringLength (toString x)) 42;
      result = allPassHandle comp;
    in
      composed.name == "compose(f, g)"
      && composed.domain.name == "Int"
      && (composed.apply 42).name == "Int"
      && result.state == true
      && result.value == 2;

  # -- Test 46: Handler diversity — Sigma through strict/collecting/logging --
  sigmaHandlerDiversity =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      bad = { fst = 42; snd = 99; };
      comp = sigT.validate bad;

      # Strict: throws on snd failure (force .value — tryEval only evals to WHNF)
      strictFails = !(builtins.tryEval ((fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else builtins.throw "Type error: ${param.context}";
      } comp).value)).success;

      # Collecting: gathers snd error
      collectResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } comp;

      # Logging: records all checks, fst passes, snd fails
      logResult = fx.handle {
        handlers.typeCheck = { param, state }: {
          resume = param.type.check param.value;
          state = state ++ [{ context = param.context; passed = param.type.check param.value; }];
        };
        state = [];
      } comp;
    in
      strictFails
      && builtins.length collectResult.state == 1
      && builtins.head collectResult.state == "String"
      && builtins.length logResult.state == 2
      && (builtins.elemAt logResult.state 0).passed == true
      && (builtins.elemAt logResult.state 1).passed == false;

  # -- Test 47: Sigma short-circuit guards crash path --
  # The snd type family crashes on non-int fst. Without short-circuit,
  # validate would crash Nix. With short-circuit, we get a clean failure.
  sigmaShortCircuitGuardsCrash =
    let
      sigT = types.Sigma {
        fst = types.Int;
        # Type family that CRASHES on non-int fst (arithmetic on string)
        snd = n: types.mkType {
          name = "Items[${toString (n + 1)}]";  # n + 1 crashes if n is string
          kernelType = H.any;
          guard = v: builtins.isList v && builtins.length v == n + 1;
        };
        universe = 0;
      };
      # fst = "bad" is wrong type. Without short-circuit, snd "bad" would
      # crash at "bad" + 1. With short-circuit, it's never evaluated.
      result = allPassHandle (sigT.validate { fst = "bad"; snd = [1]; });
    in result.state == false;

  # -- Test 48: Sigma adequacy with wrong fst (short-circuit path) --
  sigmaAdequacyWrongFst =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      badFst = { fst = "wrong"; snd = "hello"; };
    in
      # check short-circuits via &&, validate short-circuits via fstPassed==false
      # Both return false — adequacy holds on the short-circuit path.
      (types.check sigT badFst) == (allPassHandle (sigT.validate badFst)).state;

  # -- Test 49: Pi.checkAt short-circuit on domain failure --
  piCheckAtShortCircuit =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # f that crashes on non-int arg
      crashF = x: x + 1;  # "str" + 1 would crash
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (piT.checkAt crashF "not-int");
    in
      # Domain fails → short-circuit, f("not-int") never evaluated
      builtins.length result.state == 1
      && builtins.head result.state == "Π domain (Π(Int))"
      # Result is null sentinel (f was never applied)
      && result.value == null;

  # -- Test 50: Universe trust boundary — typeAt guards missing universe --
  universeTrustBoundary =
    let
      fakeNoUniverse = { _tag = "Type"; name = "fake"; check = _: true; };
      fakeWithUniverse = { _tag = "Type"; name = "fake"; check = _: true; universe = 0; };
    in
      # Missing universe → rejected by v?universe guard in typeAt
      !(types.check types.Type_0 fakeNoUniverse)
      # With universe → accepted (universe is explicit/trusted)
      && types.check types.Type_0 fakeWithUniverse;

  # -- Test 51: ListOf validate is effectful (per-element) --
  listOfValidateIsEffectful =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
    in (listT.validate [1 2 3])._tag == "Impure";

  # -- Test 52: ListOf collecting handler gets per-element errors with indices --
  listOfCollectingPerElement =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [{ inherit (param) context; }]; };
        state = [];
      } (listT.validate [1 "bad" 3 "worse"]);
    in
      # Two errors: indices 1 and 3
      builtins.length result.state == 2
      && (builtins.elemAt result.state 0).context == "List[Int][1]"
      && (builtins.elemAt result.state 1).context == "List[Int][3]";

  # -- Test 53: ListOf empty list validate returns pure --
  listOfEmptyValidatePure =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
    in (listT.validate [])._tag == "Pure";

  # -- Test 54: ListOf non-list input totality --
  listOfNonListTotality =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      # Non-list goes through effect system, doesn't crash
    in (listT.validate 42)._tag == "Impure"
       && (listT.validate 42).effect.name == "typeCheck";

  # -- Test 55: ListOf adequacy (check agrees with all-pass handler) --
  listOfAdequacy =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      # All-pass handler: state = state AND check-passed
      allPassHandler = {
        typeCheck = { param, state }:
          let passed = param.type.check param.value;
          in { resume = passed; state = state && passed; };
      };
      testAdequacy = v:
        let
          checkResult = listT.check v;
          handleResult = fx.run (listT.validate v) allPassHandler true;
        in checkResult == handleResult.state;
    in
      testAdequacy [1 2 3]       # all pass
      && testAdequacy [1 "x" 3]  # mixed
      && testAdequacy []          # empty
      && testAdequacy "not-list"; # wrong type

  # ===========================================================================
  # DEEP RECURSIVE VALIDATION TESTS
  # ===========================================================================
  #
  # Tests 56-61: Verify that Sigma.verify, pairE, and certifyE recursively
  # call sub-type .validate (not atomic .check), producing deep blame through
  # compound types like ListOf. Grounded in Findler & Felleisen (2002):
  # contract checking decomposes recursively; Plotkin & Pretnar (2009):
  # effects compose via bind (N+M effects, not 2).

  # -- Test 56: Sigma with ListOf fst — collecting handler gets per-element errors --
  sigmaDeepCollecting =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (sigT.validate { fst = [1 "bad" 3]; snd = "hello"; });
    in
      # Per-element blame: only index 1 fails, fst ListOf fails overall → snd short-circuited
      builtins.length result.state == 1
      && builtins.head result.state == "List[Int][1]";

  # -- Test 57: DepRecord with dependent ListOf — per-element blame through nested Sigma --
  depRecordDeepBlame =
    let
      recT = types.DepRecord [
        { name = "mode"; type = types.Bool; }
        { name = "items"; type = self:
            if self.mode
            then types.ListOf types.Int
            else types.ListOf types.String; }
      ];
      bad = { mode = true; items = [1 "oops" 3]; };
      packed = recT.pack bad;
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (recT.validate packed);
    in
      # Bool passes (no error), ListOf Int decomposes: index 1 fails
      builtins.length result.state == 1
      && builtins.head result.state == "List[Int][1]";

  # -- Test 58: Adequacy holds for Sigma with compound sub-types --
  sigmaDeepAdequacy =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      good = { fst = [1 2 3]; snd = "hello"; };
      bad = { fst = [1 "x" 3]; snd = "hello"; };
    in
      (types.check sigT good) == (allPassHandle (sigT.validate good)).state
      && (types.check sigT bad) == (allPassHandle (sigT.validate bad)).state;

  # -- Test 59: Deep validation + short-circuit interaction --
  # fst is compound (ListOf), snd type family crashes on wrong-typed fst.
  # Deep validation produces per-element effects, then short-circuits.
  sigmaDeepShortCircuit =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        # snd type family crashes if fst is not a list (calls builtins.length)
        snd = lst: types.mkType {
          name = "SizedVec[${toString (builtins.length lst)}]";
          kernelType = H.any;
          guard = _: true;
        };
        universe = 0;
      };
      # fst = "not-a-list": ListOf validates (1 effect, fails), short-circuit
      nonListResult = allPassHandle (sigT.validate { fst = "not-a-list"; snd = null; });
      # fst = [1 "bad"]: ListOf validates per-element, short-circuits before snd
      mixedResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; state = state ++ [param.context]; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (sigT.validate { fst = [1 "bad"]; snd = null; });
    in
      nonListResult.state == false
      # Deep effects: both list elements checked, snd never reached
      && builtins.length mixedResult.state == 2
      && builtins.elemAt mixedResult.state 0 == "List[Int][0]"
      && builtins.elemAt mixedResult.state 1 == "List[Int][1]";

  # -- Test 60: pairE with compound types gets per-element blame --
  pairEDeepBlame =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      badResult = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (sigT.pairE [1 "bad" 3] "hello");
      goodResult = allPassHandle (sigT.pairE [1 2 3] "hello");
    in
      # Bad fst: per-element blame flows through pairE, snd short-circuited
      builtins.length badResult.state == 1
      && builtins.head badResult.state == "List[Int][1]"
      # Good: all pass, adequacy holds
      && goodResult.state == true;

  # -- Test 61: certifyE with compound base gets deep blame --
  certifyEDeepBlame =
    let
      ListOfInts = types.ListOf types.Int;
      CertifiedList = types.Certified {
        base = ListOfInts;
        predicate = lst: builtins.length lst > 0;
        name = "NonEmptyIntList";
      };
      result = fx.handle {
        handlers.typeCheck = { param, state }:
          if param.type.check param.value
          then { resume = true; inherit state; }
          else { resume = false; state = state ++ [param.context]; };
        state = [];
      } (CertifiedList.certifyE [1 "bad" 3]);
    in
      # Per-element blame from ListOf flows through certifyE
      # Base fails at index 1 → short-circuit, predicate never evaluated
      builtins.length result.state == 1
      && builtins.head result.state == "List[Int][1]";

  # -- Test 62: Cross-type parametric adequacy --
  # check and allPassHandle agree across multiple type constructors and values
  crossTypeAdequacy =
    let
      testAdequacy = type: value:
        let
          checkResult = types.check type value;
          handleResult = allPassHandle (type.validate value);
        in checkResult == handleResult.state;
    in
      # Primitives
      testAdequacy types.Int 42
      && testAdequacy types.Int "bad"
      && testAdequacy types.String "hello"
      && testAdequacy types.String 42
      && testAdequacy types.Bool true
      && testAdequacy types.Bool "bad"
      # Compound
      && testAdequacy (types.ListOf types.Int) [1 2 3]
      && testAdequacy (types.ListOf types.Int) [1 "x" 3]
      && testAdequacy (types.Maybe types.Int) null
      && testAdequacy (types.Maybe types.Int) 42
      && testAdequacy (types.Maybe types.Int) "bad"
      # Refinement
      && testAdequacy (types.refined "Pos" types.Int (x: x > 0)) 5
      && testAdequacy (types.refined "Pos" types.Int (x: x > 0)) (0 - 1)
      # Sigma
      && testAdequacy (types.Sigma { fst = types.Bool; snd = _: types.Int; universe = 0; }) { fst = true; snd = 1; }
      && testAdequacy (types.Sigma { fst = types.Bool; snd = _: types.Int; universe = 0; }) { fst = "bad"; snd = 1; };

in {
  inherit validPortTest vectorTest universeTest
          recordRefinementTest maybeTest depRecordTest
          makeThrowsTest variantTest predicateTest universeSafetyTest;

  # Effectful type checking tests
  inherit piCheckAtIsEffectful
          strictHandlerPassesTest collectingHandlerTest loggingHandlerTest
          sameCompDifferentHandlerTest
          sigmaValidateIsEffectful sigmaStrictHandlerTest
          certifiedCertifyETest certifiedCertifyECollectingTest certifiedCertifyEFailTest;

  # Semantic unification tests
  inherit vectorIsEffectful vectorCheckAtStrictTest
          depRecordIsEffectful depRecordValidateStrictTest
          foundationValidateIsEffectful;

  # Adequacy and contract tests
  inherit piValidateIsGuard piAdequacy sigmaAdequacy piCheckAtDiffersFromValidate
          certifiedAdequacy depRecordAdequacy primitiveAdequacy vectorAdequacy;

  # Exhaustive edge-case tests
  inherit sigmaValidateEmpty sigmaValidateMissingSnd sigmaValidateMissingFst
          sigmaValidateWrongSnd
          piCheckAtDomainFailure
          certifyECrashingPredicate certifyEWrongBase
          depRecordValidateNonAttrset depRecordValidateMissingField depRecordValidateWrongTypes
          pairEThroughHandlers composeCheckAt
          sigmaHandlerDiversity
          sigmaShortCircuitGuardsCrash sigmaAdequacyWrongFst piCheckAtShortCircuit
          universeTrustBoundary;

  # ListOf effectful verify tests
  inherit listOfValidateIsEffectful listOfCollectingPerElement
          listOfEmptyValidatePure listOfNonListTotality listOfAdequacy;

  # Deep recursive validation tests
  inherit sigmaDeepCollecting depRecordDeepBlame sigmaDeepAdequacy
          sigmaDeepShortCircuit pairEDeepBlame certifyEDeepBlame;

  # Cross-type parametric adequacy
  inherit crossTypeAdequacy;

  allPass = validPortTest && vectorTest && universeTest
            && recordRefinementTest && maybeTest && depRecordTest
            && makeThrowsTest && variantTest && predicateTest
            && universeSafetyTest
            && piCheckAtIsEffectful
            && strictHandlerPassesTest && collectingHandlerTest && loggingHandlerTest
            && sameCompDifferentHandlerTest
            && sigmaValidateIsEffectful && sigmaStrictHandlerTest
            && certifiedCertifyETest && certifiedCertifyECollectingTest
            && certifiedCertifyEFailTest
            && vectorIsEffectful && vectorCheckAtStrictTest
            && depRecordIsEffectful && depRecordValidateStrictTest
            && foundationValidateIsEffectful
            && piValidateIsGuard && piAdequacy && sigmaAdequacy
            && piCheckAtDiffersFromValidate
            && certifiedAdequacy && depRecordAdequacy
            && primitiveAdequacy && vectorAdequacy
            && sigmaValidateEmpty && sigmaValidateMissingSnd
            && sigmaValidateMissingFst && sigmaValidateWrongSnd
            && piCheckAtDomainFailure
            && certifyECrashingPredicate && certifyEWrongBase
            && depRecordValidateNonAttrset && depRecordValidateMissingField
            && depRecordValidateWrongTypes
            && pairEThroughHandlers && composeCheckAt
            && sigmaHandlerDiversity
            && sigmaShortCircuitGuardsCrash && sigmaAdequacyWrongFst
            && piCheckAtShortCircuit
            && universeTrustBoundary
            && listOfValidateIsEffectful && listOfCollectingPerElement
            && listOfEmptyValidatePure && listOfNonListTotality
            && listOfAdequacy
            && sigmaDeepCollecting && depRecordDeepBlame
            && sigmaDeepAdequacy && sigmaDeepShortCircuit
            && pairEDeepBlame && certifyEDeepBlame
            && crossTypeAdequacy;
}
