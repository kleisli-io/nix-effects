# nix-effects type system integration tests
{ lib, fx }:

let
  inherit (fx) types;
  H = types.hoas;
  R = fx.tc.kernel.reflect;

  # All-pass handler: resumes with the check result, tracks via boolean state
  # whether ALL typeCheck effects passed.
  validationPassHandle = comp:
    fx.handle
      {
        handlers.typeCheck = { param, state }:
          let passed = param.type.check param.value;
          in { resume = passed; state = state && passed; };
        state = true;
      }
      comp;

  # Shared fixtures for the nested-decidable-Certified regression cases below.
  # A decidable `Certified` embeds `El t` in its kernel; when nested inside a
  # compound, the monolithic kernel `.check` could not unfold that head and
  # over-rejected valid values, diverging from the structural `.validate`. The
  # `adq` helper asserts the two agree (the membership decision and the
  # structural verify must give the same answer).
  nestedCert = rec {
    IntC = types.mkType { name = "Int"; kernelType = H.int_; };
    StrC = types.mkType { name = "Str"; kernelType = H.string; };
    PosInt = types.Certified { base = IntC; predicate = R.intPositive; name = "PosInt"; };
    NeStr = types.Certified { base = StrC; predicate = R.strNonEmpty; name = "NeStr"; };
    Range = types.Certified { base = IntC; predicate = R.intInRange 10 20; name = "R10_20"; };
    cert = v: { fst = v; snd = null; };
    adq = type: value:
      (types.check type value) == (validationPassHandle (type.validate value)).state;
  };

  # ValidPort refinement type
  validPortTest =
    let
      ValidPort = types.refined "ValidPort" types.Int (types.inRange 1 65535);
    in
    types.check ValidPort 8080
    && !(types.check ValidPort 99999)
    && !(types.check ValidPort 0)
    && !(types.check ValidPort (-1));

  # Vector 3 Int (Vector is now a Pi type family)
  vectorTest =
    let V3I = (types.Vector types.Int).apply 3;
    in types.check V3I [ 1 2 3 ]
      && !(types.check V3I [ 1 2 ])
      && !(types.check V3I [ 1 2 3 4 ])
      && !(types.check V3I [ 1 "two" 3 ]);

  # Universe hierarchy
  universeTest =
    types.check types.Type_1 types.Type_0
    && types.check types.Type_2 types.Type_1
    && !(types.check types.Type_0 types.Type_0)
    && !(types.check types.Type_1 types.Type_1);

  # Record + refinement composition
  recordRefinementTest =
    let
      ServiceConfig = types.Record {
        name = types.String;
        port = types.refined "ValidPort" types.Int (types.inRange 1 65535);
      };
    in
    types.check ServiceConfig { name = "nginx"; port = 443; }
    && !(types.check ServiceConfig { name = "nginx"; port = 99999; })
    && !(types.check ServiceConfig { name = "nginx"; });

  # Maybe type
  maybeTest =
    let MaybeInt = types.Maybe types.Int;
    in types.check MaybeInt null
      && types.check MaybeInt 42
      && !(types.check MaybeInt "hello");

  # Dependent record (nested Sigma pairs)
  depRecordTest =
    let
      SizedList = types.DepRecord [
        { name = "n"; type = types.Int; }
        {
          name = "items";
          type = (self:
            types.mkType {
              name = "List[n=${toString self.n}]";
              kernelType = H.any;
              guard = v: builtins.isList v && builtins.length v == self.n;
            });
        }
      ];
      # Values are nested Sigma: { fst = n; snd = items; }
    in
    types.check SizedList { fst = 2; snd = [ "a" "b" ]; }
    && !(types.check SizedList { fst = 3; snd = [ "a" "b" ]; });

  # make throws on invalid
  makeThrowsTest =
    let
      result = builtins.tryEval (types.make types.Int "not-an-int");
    in
      !result.success;

  # Variant type
  variantTest =
    let
      Shape = types.Variant {
        circle = types.Float;
        rect = types.Record { w = types.Float; h = types.Float; };
      };
    in
    types.check Shape { _tag = "circle"; value = 5.0; }
    && types.check Shape { _tag = "rect"; value = { w = 3.0; h = 4.0; }; }
    && !(types.check Shape { _tag = "triangle"; value = null; });

  # Predicate combinators
  predicateTest =
    let
      EvenPositive = types.refined "EvenPositive" types.Int
        (types.allOf [ types.positive (x: lib.mod x 2 == 0) ]);
    in
    types.check EvenPositive 4
    && !(types.check EvenPositive 3)
    && !(types.check EvenPositive (-2));

  # Universe tower safety
  universeSafetyTest =
    let
      noSelfMembership = !(types.check (types.typeAt 5) (types.typeAt 5));
      chain = types.check types.Type_2 types.Type_1
        && types.check types.Type_1 types.Type_0;
    in
    noSelfMembership && chain;

  # Pi.checkAt returns Computation with typeCheck effect
  piCheckAtIsEffectful =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
    in
    !(fx.isPure comp)
    && comp.effect.name == "typeCheck"
    && comp.effect.param.type.name == "Int";

  # Strict handler — passes when types match
  strictHandlerPassesTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else throw "Type error in ${param.context}: expected ${param.type.name}";
        }
        comp;
    in
    result.value == 42;

  # Collecting handler — gathers codomain error
  collectingHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # f returns int (42), but codomain expects String → codomain check fails
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [{ context = param.context; expected = param.type.name; }]; };
          state = [ ];
        }
        comp;
    in
    builtins.length result.state == 1
    && (builtins.head result.state).expected == "String";

  # Logging handler — records ALL checks
  loggingHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      comp = piT.checkAt (x: x * 2) 21;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }: {
            resume = (param.type.check param.value);
            state = state ++ [{
              context = param.context;
              passed = (param.type.check param.value);
            }];
          };
          state = [ ];
        }
        comp;
      # Both domain (Int check on 21) and codomain (Int check on 42) pass
    in
    builtins.length result.state == 2
    && (builtins.elemAt result.state 0).passed
    && (builtins.elemAt result.state 1).passed;

  # Same computation, different handler, different outcome
  sameCompDifferentHandlerTest =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # This computation has a codomain error (42 is not a String)
      comp = piT.checkAt (x: x * 2) 21;

      # Handler A: collecting (gathers errors)
      collectResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        comp;

      # Handler B: logging (records all checks, no errors)
      logResult = fx.handle
        {
          handlers.typeCheck = { param, state }: {
            resume = (param.type.check param.value);
            state = state ++ [ (param.type.check param.value) ];
          };
          state = [ ];
        }
        comp;
    in
    # Collecting handler: 1 error (codomain)
    builtins.length collectResult.state == 1
    # Logging handler: 2 entries (domain + codomain), second is false
    && builtins.length logResult.state == 2
    && builtins.elemAt logResult.state 0 == true   # domain passes
    && builtins.elemAt logResult.state 1 == false; # codomain fails

  # Sigma.validate emits typeCheck on failure
  # Under fail-only emission, a well-typed pair walks through without
  # emitting; a snd mismatch (Int ≠ String) drives the failure path.
  sigmaValidateIsEffectful =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.Int; universe = 0; };
      comp = sigT.validate { fst = 1; snd = "bad"; };
    in
    !(fx.isPure comp)
    && comp.effect.name == "typeCheck";

  # Sigma.validate through strict handler
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
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else throw "Type error: ${param.context}";
        }
        comp;
    in
    result.value == { fst = 2; snd = [ "a" "b" ]; };

  # Certified.certifyE is pure on a valid value
  certifiedCertifyETest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = R.intPositive;
        name = "PosInt";
      };
      comp = PosInt.certifyE 5;
    in
    fx.isPure comp
    && comp.value == { fst = 5; snd = null; };

  # Certified.certifyE through collecting handler
  certifiedCertifyECollectingTest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = R.intPositive;
        name = "PosInt";
      };
      comp = PosInt.certifyE 5;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        comp;
    in
    result.value == { fst = 5; snd = null; }
    && builtins.length result.state == 0; # valid → pure, no effects

  # Certified.certifyE failing predicate through collecting handler
  certifiedCertifyEFailTest =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = R.intPositive;
        name = "PosInt";
      };
      # -5 is int (base passes) but predicate fails
      comp = PosInt.certifyE (-5);
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        comp;
    in
    builtins.length result.state == 1; # predicate check fails

  # Vector-as-Pi has checkAt, validate, and other Pi operations
  vectorIsEffectful =
    let
      vecFamily = types.Vector types.Int;
    in
    vecFamily ? validate
    && vecFamily ? checkAt
    && vecFamily ? compose
    && vecFamily ? apply
    && vecFamily ? domain
    && vecFamily ? codomain;

  # Vector.checkAt through strict handler
  vectorCheckAtStrictTest =
    let
      vecFamily = types.Vector types.Int;
      # A function from Nat to sized lists — a valid Vector value
      mkList = n: builtins.genList (i: i) n;
      comp = vecFamily.checkAt mkList 3;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else throw "Type error: ${param.context}";
        }
        comp;
    in
    result.value == [ 0 1 2 ];

  # DepRecord-as-Sigma has validate (effectful)
  depRecordIsEffectful =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in
    recT ? validate && recT ? proj1 && recT ? proj2;

  # DepRecord.validate through strict handler
  depRecordValidateStrictTest =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      # Nested Sigma value: { fst = 42; snd = "hello"; }
      comp = recT.validate { fst = 42; snd = "hello"; };
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else throw "Type error: ${param.context}";
        }
        comp;
    in
    result.value == { fst = 42; snd = "hello"; };

  # foundation.validate is effectful (not a result attrset)
  foundationValidateIsEffectful =
    let
      comp = types.validate types.Int 42 "test-context";
    in
    !(fx.isPure comp)
    && comp.effect.name == "typeCheck"
    && comp.effect.param.context == "test-context";

  # Pi.validate is the effectful guard (1 arg, auto-derived)
  # Under fail-only emission, the guard is observed by driving the
  # failure path with a non-function value (42 against Π(Int)).
  piValidateIsGuard =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # validate takes ONE arg (the value to check as introduction form)
      comp = piT.validate 42;
    in
    !(fx.isPure comp)
    && comp.effect.name == "typeCheck"
    # The context is the type name, not "Π domain" — it's the guard,
    # not the elimination check
    && comp.effect.param.context == "Π(Int)";

  # Pi adequacy — check and validate agree
  # Adequacy uses the all-pass handler's state (bool) rather than
  # `.value`: under fail-only emission, `pure v` keeps `.value = v`
  # (the validated value) and never invokes the handler, so the
  # bool channel must come from handler state.
  piAdequacy =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      f = x: x * 2;
      notF = 42;
    in
    # Adequacy: check f ⟺ (validationPassHandle (validate f)).state
    (types.check piT f) == (validationPassHandle (piT.validate f)).state
    && (types.check piT notF) == (validationPassHandle (piT.validate notF)).state;

  # Sigma adequacy — check and validate agree
  # Sigma.validate returns `pure v` (the pair), not a bool; adequacy is tested
  # via handler state, not result.value.
  sigmaAdequacy =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      good = { fst = 42; snd = "hello"; };
      bad = { fst = 42; snd = 99; };
    in
    # Good pair: check passes, all effects pass
    (types.check sigT good) == (validationPassHandle (sigT.validate good)).state
    # Bad pair: check fails, some effect fails
    && (types.check sigT bad) == (validationPassHandle (sigT.validate bad)).state;

  # checkAt differs from validate — a bad function passes
  #    validate (it IS a function) but fails checkAt (wrong codomain)
  piCheckAtDiffersFromValidate =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.String; universe = 0; };
      # This IS a function (passes guard), but returns Int not String
      badF = x: x * 2;
      # validate (guard): passes — under fail-only emission, no typeCheck
      # fires, so the computation is pure.
      guardPasses = fx.isPure (piT.validate badF);
      # checkAt (deferred contract): fails at codomain
      checkAtResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; state = state ++ [ "pass" ]; }
            else { resume = false; state = state ++ [ "fail:${param.context}" ]; };
          state = [ ];
        }
        (piT.checkAt badF 21);
    in
    # Guard passes (it IS a function)
    guardPasses
    # Deferred contract: domain passes (21 is Int), codomain fails (42 is not String)
    && builtins.length checkAtResult.state == 2
    && builtins.elemAt checkAtResult.state 0 == "pass"
    && builtins.elemAt checkAtResult.state 1 == "fail:Π codomain (Π(Int))";

  # Certified adequacy — check and validate agree
  certifiedAdequacy =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = R.intPositive;
        name = "PosInt";
      };
      good = { fst = 5; snd = null; };
      bad = { fst = -1; snd = null; };
    in
    (types.check PosInt good) == (validationPassHandle (PosInt.validate good)).state
    && (types.check PosInt bad) == (validationPassHandle (PosInt.validate bad)).state;

  # DepRecord adequacy — check and validate agree
  depRecordAdequacy =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      good = { fst = 42; snd = "hello"; };
      bad = { fst = "nope"; snd = "hello"; };
    in
    (types.check recT good) == (validationPassHandle (recT.validate good)).state
    && (types.check recT bad) == (validationPassHandle (recT.validate bad)).state;

  # Primitive (Int) adequacy — auto-derived validate
  primitiveAdequacy =
    (types.check types.Int 42) == (validationPassHandle (types.Int.validate 42)).state
    && (types.check types.Int "bad") == (validationPassHandle (types.Int.validate "bad")).state;

  # Vector (Pi-based) adequacy — auto-derived validate
  vectorAdequacy =
    let
      vecFamily = types.Vector types.Int;
      good = n: builtins.genList (i: i) n;
      bad = 42;
    in
    (types.check vecFamily good) == (validationPassHandle (vecFamily.validate good)).state
    && (types.check vecFamily bad) == (validationPassHandle (vecFamily.validate bad)).state;

  # Sigma.validate on empty attrset
  sigmaValidateEmpty =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in
    (validationPassHandle (sigT.validate { })).state == false;

  # Sigma.validate on {fst=1} (missing snd)
  sigmaValidateMissingSnd =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in
    (validationPassHandle (sigT.validate { fst = 1; })).state == false;

  # Sigma.validate on {snd=1} (missing fst)
  sigmaValidateMissingFst =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
    in
    (validationPassHandle (sigT.validate { snd = 1; })).state == false;

  # Sigma.validate wrong snd through collecting handler
  # Deep recursive validation: snd type's own validate produces the context
  sigmaValidateWrongSnd =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.Int; universe = 0; };
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        (sigT.validate { fst = 1; snd = "wrong"; });
    in
    builtins.length result.state == 1
    && builtins.head result.state == "Int";

  # Pi.checkAt domain failure — strict handler throws
  piCheckAtDomainFailure =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # Force .value to trigger trampoline execution (tryEval only evals to WHNF)
      result = builtins.tryEval (
        (fx.handle
          {
            handlers.typeCheck = { param, state }:
              if param.type.check param.value
              then { resume = true; inherit state; }
              else builtins.throw "Type error: ${param.context}";
          }
          (piT.checkAt (x: x * 2) "not-int")).value
      );
    in
      !result.success;

  # a raw host-lambda predicate yields no proof → rejected at construction
  certifiedRejectsRawPredicate =
    let
      mk = types.Certified {
        base = types.Int;
        predicate = _: builtins.throw "crash";
        name = "CrashType";
      };
    in
    !(builtins.tryEval mk).success;

  # certifyE with wrong base type
  # certifyE short-circuits on base failure: predicate is never evaluated
  # (it may crash on wrong-typed input via uncatchable cross-type comparison).
  certifyEWrongBase =
    let
      PosInt = types.Certified {
        base = types.Int;
        predicate = R.intPositive;
        name = "PosInt";
      };
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        (PosInt.certifyE "not-int");
    in
    # Base fails → short-circuit, predicate never evaluated
    builtins.length result.state == 1
    && builtins.elemAt result.state 0 == "Int";

  # DepRecord.validate non-attrset
  depRecordValidateNonAttrset =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in
    (validationPassHandle (recT.validate 42)).state == false;

  # DepRecord.validate missing field
  depRecordValidateMissingField =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
    in
    (validationPassHandle (recT.validate { fst = 42; })).state == false;

  # DepRecord.validate wrong field types
  # DepRecord inherits Sigma's short-circuit: when fst fails, snd type
  # family is never evaluated (it depends on fst value being well-typed).
  depRecordValidateWrongTypes =
    let
      recT = types.DepRecord [
        { name = "n"; type = types.Int; }
        { name = "s"; type = types.String; }
      ];
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        (recT.validate { fst = "wrong"; snd = 42; });
    in
    # fst fails → short-circuit, snd type family never evaluated
    builtins.length result.state == 1;

  # pairE through handlers — success and failure
  pairEThroughHandlers =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      goodResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else builtins.throw "Type error: ${param.context}";
        }
        (sigT.pairE 42 "hello");
      badResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        (sigT.pairE 42 99);
    in
    goodResult.value == { fst = 42; snd = "hello"; }
    && builtins.length badResult.state == 1
    && builtins.head badResult.state == "String";

  # Pi compose + checkAt interaction
  composeCheckAt =
    let
      piF = types.Pi { domain = types.Int; codomain = _: types.String; name = "f"; universe = 0; };
      piG = types.Pi { domain = types.String; codomain = _: types.Int; name = "g"; universe = 0; };
      composed = piF.compose toString piG;
      comp = composed.checkAt (x: builtins.stringLength (toString x)) 42;
      result = validationPassHandle comp;
    in
    composed.name == "compose(f, g)"
    && composed.domain.name == "Int"
    && (composed.apply 42).name == "Int"
    && result.state == true
    && result.value == 2;

  # Handler diversity — Sigma through strict/collecting/logging
  # Under fail-only emission, only failing components emit. With
  # bad = {fst=42; snd=99}, fst (Int) passes silently and snd (String)
  # fails — exactly one typeCheck event reaches the handler.
  sigmaHandlerDiversity =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      bad = { fst = 42; snd = 99; };
      comp = sigT.validate bad;

      # Strict: throws on snd failure (force .value — tryEval only evals to WHNF)
      strictFails = !(builtins.tryEval (
        (fx.handle
          {
            handlers.typeCheck = { param, state }:
              if param.type.check param.value
              then { resume = true; inherit state; }
              else builtins.throw "Type error: ${param.context}";
          }
          comp).value
      )).success;

      # Collecting: gathers snd error
      collectResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        comp;

      # Logging: records every emitted event. Under fail-only, that's
      # exactly the snd failure.
      logResult = fx.handle
        {
          handlers.typeCheck = { param, state }: {
            resume = param.type.check param.value;
            state = state ++ [{ context = param.context; passed = param.type.check param.value; }];
          };
          state = [ ];
        }
        comp;
    in
    strictFails
    && builtins.length collectResult.state == 1
    && builtins.head collectResult.state == "String"
    && builtins.length logResult.state == 1
    && (builtins.head logResult.state).passed == false;

  # Sigma short-circuit guards crash path
  # The snd type family crashes on non-int fst. Without short-circuit,
  # validate would crash Nix. With short-circuit, we get a clean failure.
  sigmaShortCircuitGuardsCrash =
    let
      sigT = types.Sigma {
        fst = types.Int;
        # Type family that CRASHES on non-int fst (arithmetic on string)
        snd = n: types.mkType {
          name = "Items[${toString (n + 1)}]"; # n + 1 crashes if n is string
          kernelType = H.any;
          guard = v: builtins.isList v && builtins.length v == n + 1;
        };
        universe = 0;
      };
      # fst = "bad" is wrong type. Without short-circuit, snd "bad" would
      # crash at "bad" + 1. With short-circuit, it's never evaluated.
      result = validationPassHandle (sigT.validate { fst = "bad"; snd = [ 1 ]; });
    in
    result.state == false;

  # Sigma adequacy with wrong fst (short-circuit path)
  sigmaAdequacyWrongFst =
    let
      sigT = types.Sigma { fst = types.Int; snd = _: types.String; universe = 0; };
      badFst = { fst = "wrong"; snd = "hello"; };
    in
    # check short-circuits via &&, validate short-circuits via fstPassed==false
      # Both return false — adequacy holds on the short-circuit path.
    (types.check sigT badFst) == (validationPassHandle (sigT.validate badFst)).state;

  # Pi.checkAt short-circuit on domain failure
  piCheckAtShortCircuit =
    let
      piT = types.Pi { domain = types.Int; codomain = _: types.Int; universe = 0; };
      # f that crashes on non-int arg
      crashF = x: x + 1; # "str" + 1 would crash
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.context ]; };
          state = [ ];
        }
        (piT.checkAt crashF "not-int");
    in
    # Domain fails → short-circuit, f("not-int") never evaluated
    builtins.length result.state == 1
    && builtins.head result.state == "Π domain (Π(Int))"
    # Result is null sentinel (f was never applied)
    && result.value == null;

  # Universe trust boundary — typeAt guards missing fields
  universeTrustBoundary =
    let
      fakeNoUniverse = { _tag = "Type"; name = "fake"; check = _: true; };
      fakeNoKernel = { _tag = "Type"; name = "fake"; check = _: true; universe = 0; };
      wellFormed = { _tag = "Type"; name = "fake"; check = _: true; universe = 0; _kernel = H.nat; };
    in
    # Missing universe → rejected by guard
    !(types.check types.Type_0 fakeNoUniverse)
    # Missing _kernel → rejected by kernel (can't elaborate for U)
    && !(types.check types.Type_0 fakeNoKernel)
    # Well-formed fake type → accepted (kernel verifies level, guard verifies universe)
    && types.check types.Type_0 wellFormed;

  # ListOf validate is effectful when an element fails
  # Walker contract: per-element checks are predicate-based; typeCheck
  # effects emit only on failure. An all-pass list is therefore pure;
  # any failing element makes the computation effectful at that index.
  listOfValidateIsEffectful =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
    in
      !(fx.isPure (listT.validate [ 1 "bad" 3 ]));

  # ListOf collecting handler gets per-element errors with indices
  listOfCollectingPerElement =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [{ inherit (param) path; }]; };
          state = [ ];
        }
        (listT.validate [ 1 "bad" 3 "worse" ]);
      # Inspect path segments via tag/idx; avoids coupling to internal diag.positions.
      seg0 = builtins.elemAt (builtins.elemAt result.state 0).path 0;
      seg1 = builtins.elemAt (builtins.elemAt result.state 1).path 0;
    in
    # Two errors: indices 1 and 3 — path carries the structural descent
      # as a list of Position records.
    builtins.length result.state == 2
    && seg0.tag == "Elem" && seg0.idx == 1
    && seg1.tag == "Elem" && seg1.idx == 3;

  # ListOf empty list validate returns pure
  listOfEmptyValidatePure =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
    in
    fx.isPure (listT.validate [ ]);

  # ListOf non-list input totality
  listOfNonListTotality =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      # Non-list goes through effect system, doesn't crash
    in
    !(fx.isPure (listT.validate 42))
    && (listT.validate 42).effect.name == "typeCheck";

  # ListOf adequacy (check agrees with all-pass handler)
  listOfAdequacy =
    let
      IntT = types.mkType { name = "Int"; kernelType = H.int_; };
      listT = types.ListOf IntT;
      # All-pass handler: state = state AND check-passed
      validationPassHandler = {
        typeCheck = { param, state }:
          let passed = param.type.check param.value;
          in { resume = passed; state = state && passed; };
      };
      testAdequacy = v:
        let
          checkResult = listT.check v;
          handleResult = fx.run (listT.validate v) validationPassHandler true;
        in
        checkResult == handleResult.state;
    in
    testAdequacy [ 1 2 3 ]       # all pass
    && testAdequacy [ 1 "x" 3 ]  # mixed
    && testAdequacy [ ]          # empty
    && testAdequacy "not-list"; # wrong type

  # Sigma with ListOf fst — collecting handler gets per-element errors
  sigmaDeepCollecting =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.path ]; };
          state = [ ];
        }
        (sigT.validate { fst = [ 1 "bad" 3 ]; snd = "hello"; });
    in
    # Per-element blame: only index 1 fails, fst ListOf fails overall → snd short-circuited
    builtins.length result.state == 1
    && fx.types.generic.path.renderAll (builtins.head result.state) == "Σ.fst[1]";

  # DepRecord with dependent ListOf — per-element blame through nested Sigma
  depRecordDeepBlame =
    let
      recT = types.DepRecord [
        { name = "mode"; type = types.Bool; }
        {
          name = "items";
          type = self:
            if self.mode
            then types.ListOf types.Int
            else types.ListOf types.String;
        }
      ];
      bad = { mode = true; items = [ 1 "oops" 3 ]; };
      packed = recT.pack bad;
      result = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.path ]; };
          state = [ ];
        }
        (recT.validate packed);
    in
    # Bool passes (no error), ListOf Int decomposes: index 1 fails.
      # DepRecord is a Sigma-of-Sigma chain, so the path picks up a
      # structural tag for the nested position before entering the list.
    builtins.length result.state == 1
    && (lib.last (builtins.head result.state)).segment == "[1]";

  # Adequacy holds for Sigma with compound sub-types
  sigmaDeepAdequacy =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      good = { fst = [ 1 2 3 ]; snd = "hello"; };
      bad = { fst = [ 1 "x" 3 ]; snd = "hello"; };
    in
    (types.check sigT good) == (validationPassHandle (sigT.validate good)).state
    && (types.check sigT bad) == (validationPassHandle (sigT.validate bad)).state;

  # Deep validation + short-circuit interaction
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
      nonListResult = validationPassHandle (sigT.validate { fst = "not-a-list"; snd = null; });
      # fst = [1 "bad"]: ListOf validates per-element, short-circuits before snd
      mixedResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; state = state ++ [ param.path ]; }
            else { resume = false; state = state ++ [ param.path ]; };
          state = [ ];
        }
        (sigT.validate { fst = [ 1 "bad" ]; snd = null; });
    in
    nonListResult.state == false
    # Walker contract: typeCheck emits per failing element only; the
    # passing element at index 0 produces no event. Short-circuit
    # still holds: snd is never reached (no `Σ.snd*` path in state).
    && builtins.length mixedResult.state == 1
    && fx.types.generic.path.renderAll (builtins.head mixedResult.state) == "Σ.fst[1]";

  # pairE with compound types gets per-element blame
  pairEDeepBlame =
    let
      sigT = types.Sigma {
        fst = types.ListOf types.Int;
        snd = _: types.String;
        universe = 0;
      };
      badResult = fx.handle
        {
          handlers.typeCheck = { param, state }:
            if param.type.check param.value
            then { resume = true; inherit state; }
            else { resume = false; state = state ++ [ param.path ]; };
          state = [ ];
        }
        (sigT.pairE [ 1 "bad" 3 ] "hello");
      goodResult = validationPassHandle (sigT.pairE [ 1 2 3 ] "hello");
    in
    # Bad fst: per-element blame flows through pairE, snd short-circuited.
      # pairE calls fst.validate (1-arg → empty path root), so the ListOf
      # element index is the full path.
    builtins.length badResult.state == 1
    && fx.types.generic.path.renderAll (builtins.head badResult.state) == "[1]"
    # Good: all pass, adequacy holds
    && goodResult.state == true;

  # no KernelPred decides a list property, so a compound-base raw
  # predicate yields no proof → rejected at construction (use `refined`).
  certifiedRejectsCompoundRawPredicate =
    let
      mk = types.Certified {
        base = types.ListOf types.Int;
        predicate = lst: builtins.length lst > 0;
        name = "NonEmptyIntList";
      };
    in
    !(builtins.tryEval mk).success;

  # Cross-type parametric adequacy
  # check and validationPassHandle agree across multiple type constructors and values
  crossTypeAdequacy =
    let
      testAdequacy = type: value:
        let
          checkResult = types.check type value;
          handleResult = validationPassHandle (type.validate value);
        in
        checkResult == handleResult.state;
    in
    # Primitives
    testAdequacy types.Int 42
    && testAdequacy types.Int "bad"
    && testAdequacy types.String "hello"
    && testAdequacy types.String 42
    && testAdequacy types.Bool true
    && testAdequacy types.Bool "bad"
    # Compound
    && testAdequacy (types.ListOf types.Int) [ 1 2 3 ]
    && testAdequacy (types.ListOf types.Int) [ 1 "x" 3 ]
    && testAdequacy (types.Maybe types.Int) null
    && testAdequacy (types.Maybe types.Int) 42
    && testAdequacy (types.Maybe types.Int) "bad"
    # Refinement
    && testAdequacy (types.refined "Pos" types.Int (x: x > 0)) 5
    && testAdequacy (types.refined "Pos" types.Int (x: x > 0)) (0 - 1)
    # Sigma
    && testAdequacy (types.Sigma { fst = types.Bool; snd = _: types.Int; universe = 0; }) { fst = true; snd = 1; }
    && testAdequacy (types.Sigma { fst = types.Bool; snd = _: types.Int; universe = 0; }) { fst = "bad"; snd = 1; };

  # Decidable Certified nested in a Record field: `.check` accepts good values,
  # rejects bad, and agrees with the structural `.validate` (it previously
  # over-rejected and diverged).
  nestedCertifiedRecord =
    let g = nestedCert; Rec1 = types.Record { f = g.PosInt; }; in
    types.check Rec1 { f = g.cert 5; }
    && !(types.check Rec1 { f = g.cert (-1); })
    && g.adq Rec1 { f = g.cert 5; }
    && g.adq Rec1 { f = g.cert (-1); };

  # Multiple Certified fields, mixed carriers (Int / String) and a range
  # predicate: each bad field independently rejects.
  nestedCertifiedRecordMixed =
    let
      g = nestedCert;
      Rec3 = types.Record { a = g.PosInt; b = g.NeStr; c = g.Range; };
      ok = { a = g.cert 7; b = g.cert "hi"; c = g.cert 12; };
    in
    types.check Rec3 ok
    && !(types.check Rec3 (ok // { a = g.cert 0; }))
    && !(types.check Rec3 (ok // { b = g.cert ""; }))
    && !(types.check Rec3 (ok // { c = g.cert 99; }))
    && g.adq Rec3 ok;

  # Decidable Certified as a ListOf element, including the vacuous empty list.
  nestedCertifiedListOf =
    let g = nestedCert; Lst = types.ListOf g.PosInt; in
    types.check Lst [ (g.cert 1) (g.cert 2) (g.cert 3) ]
    && !(types.check Lst [ (g.cert 1) (g.cert (-2)) ])
    && types.check Lst [ ]
    && g.adq Lst [ (g.cert 1) (g.cert 2) ]
    && g.adq Lst [ (g.cert 1) (g.cert (-2)) ];

  # Decidable Certified in a Variant arm; sibling arms stay unaffected.
  nestedCertifiedVariant =
    let g = nestedCert; Var = types.Variant { Some = g.PosInt; None = types.Unit; }; in
    types.check Var { _tag = "Some"; value = g.cert 5; }
    && !(types.check Var { _tag = "Some"; value = g.cert (-5); })
    && types.check Var { _tag = "None"; value = null; }
    && g.adq Var { _tag = "Some"; value = g.cert 5; }
    && g.adq Var { _tag = "Some"; value = g.cert (-5); };

  # Decidable Certified as a Sigma first component.
  nestedCertifiedSigma =
    let g = nestedCert; Pair = types.Sigma { fst = g.PosInt; snd = _: g.IntC; universe = 0; }; in
    types.check Pair { fst = g.cert 5; snd = 99; }
    && !(types.check Pair { fst = g.cert (-5); snd = 99; })
    && g.adq Pair { fst = g.cert 5; snd = 99; }
    && g.adq Pair { fst = g.cert (-5); snd = 99; };

  # Deep nesting: ListOf (Record { xs = ListOf PosInt }).
  nestedCertifiedDeep =
    let g = nestedCert; Deep = types.ListOf (types.Record { xs = types.ListOf g.PosInt; }); in
    types.check Deep [ { xs = [ (g.cert 1) (g.cert 2) ]; } { xs = [ (g.cert 3) ]; } ]
    && !(types.check Deep [ { xs = [ (g.cert 1) ]; } { xs = [ (g.cert (-9)) ]; } ])
    && g.adq Deep [ { xs = [ (g.cert 1) (g.cert 2) ]; } ]
    && g.adq Deep [ { xs = [ (g.cert (-9)) ]; } ];

in
{
  inherit validPortTest vectorTest universeTest
    recordRefinementTest maybeTest depRecordTest
    makeThrowsTest variantTest predicateTest universeSafetyTest;

  inherit piCheckAtIsEffectful
    strictHandlerPassesTest collectingHandlerTest loggingHandlerTest
    sameCompDifferentHandlerTest
    sigmaValidateIsEffectful sigmaStrictHandlerTest
    certifiedCertifyETest certifiedCertifyECollectingTest certifiedCertifyEFailTest;

  inherit vectorIsEffectful vectorCheckAtStrictTest
    depRecordIsEffectful depRecordValidateStrictTest
    foundationValidateIsEffectful;

  inherit piValidateIsGuard piAdequacy sigmaAdequacy piCheckAtDiffersFromValidate
    certifiedAdequacy depRecordAdequacy primitiveAdequacy vectorAdequacy;

  inherit sigmaValidateEmpty sigmaValidateMissingSnd sigmaValidateMissingFst
    sigmaValidateWrongSnd
    piCheckAtDomainFailure
    certifiedRejectsRawPredicate certifyEWrongBase
    depRecordValidateNonAttrset depRecordValidateMissingField depRecordValidateWrongTypes
    pairEThroughHandlers composeCheckAt
    sigmaHandlerDiversity
    sigmaShortCircuitGuardsCrash sigmaAdequacyWrongFst piCheckAtShortCircuit
    universeTrustBoundary;

  inherit listOfValidateIsEffectful listOfCollectingPerElement
    listOfEmptyValidatePure listOfNonListTotality listOfAdequacy;

  inherit sigmaDeepCollecting depRecordDeepBlame sigmaDeepAdequacy
    sigmaDeepShortCircuit pairEDeepBlame certifiedRejectsCompoundRawPredicate;

  inherit crossTypeAdequacy;

  inherit nestedCertifiedRecord nestedCertifiedRecordMixed nestedCertifiedListOf
    nestedCertifiedVariant nestedCertifiedSigma nestedCertifiedDeep;
}
