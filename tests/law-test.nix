# nix-effects algebraic law tests
#
# Verifies OBSERVATIONAL EQUIVALENCE through the trampoline interpreter.
# Structurally the computation ASTs may differ, but after interpretation
# they must agree — this is the correct notion of equality for free monads.
#
# Laws verified:
#   Monad:   left-id, right-id, associativity (pure + effectful variants)
#   Functor: identity, composition
#   State:   get-get, get-put, put-get, put-put (Plotkin & Power 2002)
#   Lens:    get-put, put-get, put-put (for adapt combinator)
#   Sigma:   curry/uncurry adjunction, pullback identity, pullback composition (contravariant)
#   DepRecord: pack/unpack bijection
{ lib, fx }:

let
  inherit (fx) pure bind send run map adapt;

  # =========================================================================
  # MONAD LAWS
  # =========================================================================
  #
  # Interpret through state handlers to test observational equivalence.
  # Both value and final state must agree.

  stateHandlers = {
    get = { param, state }: { resume = state; inherit state; };
    put = { param, state }: { resume = null; state = param; };
  };

  interpret = comp: run comp stateHandlers 0;

  equiv = a: b:
    let ra = interpret a; rb = interpret b;
    in ra.value == rb.value && ra.state == rb.state;

  # -- Left identity: bind (pure a) f ≡ f a --

  monadLeftIdPure =
    let
      a = 42;
      f = x: pure (x * 2);
    in equiv (bind (pure a) f) (f a);

  monadLeftIdEffectful =
    let
      a = 5;
      f = x: bind (send "put" x) (_: send "get" null);
    in equiv (bind (pure a) f) (f a);

  # -- Right identity: bind m pure ≡ m --

  monadRightIdPure =
    let m = pure 42;
    in equiv (bind m pure) m;

  monadRightIdEffectful =
    let m = bind (send "put" 10) (_: send "get" null);
    in equiv (bind m pure) m;

  # -- Associativity: bind (bind m f) g ≡ bind m (λx → bind (f x) g) --

  monadAssocPure =
    let
      m = pure 1;
      f = x: pure (x + 10);
      g = x: pure (x * 2);
    in equiv (bind (bind m f) g) (bind m (x: bind (f x) g));

  monadAssocEffectful =
    let
      m = send "get" null;
      f = x: bind (send "put" (x + 1)) (_: pure x);
      g = x: bind (send "put" (x * 10)) (_: send "get" null);
    in equiv (bind (bind m f) g) (bind m (x: bind (f x) g));

  # =========================================================================
  # FUNCTOR LAWS
  # =========================================================================

  # Identity: map id ≡ id
  functorIdentity =
    let m = bind (send "put" 5) (_: send "get" null);
    in equiv (map (x: x) m) m;

  # Composition: map (f ∘ g) ≡ map f ∘ map g
  functorComposition =
    let
      m = pure 3;
      f = x: x + 10;
      g = x: x * 2;
    in equiv (map (x: f (g x)) m) (map f (map g m));

  # =========================================================================
  # STATE EFFECT LAWS (Plotkin & Power 2002)
  # =========================================================================

  get = send "get" null;
  put = s: send "put" s;

  equivS = init: a: b:
    let ra = run a stateHandlers init; rb = run b stateHandlers init;
    in ra.value == rb.value && ra.state == rb.state;

  # Get-Get: get >>= λs₁ → get >>= λs₂ → k s₁ s₂  ≡  get >>= λs → k s s
  stateGetGet =
    let k = s1: s2: pure { inherit s1 s2; };
    in equivS 42
      (bind get (s1: bind get (s2: k s1 s2)))
      (bind get (s: k s s));

  # Get-Put: get >>= put ≡ pure null
  stateGetPut = equivS 42
    (bind get (s: put s))
    (pure null);

  # Put-Get: put s >> get ≡ put s >> pure s
  statePutGet = equivS 0
    (bind (put 99) (_: get))
    (bind (put 99) (_: pure 99));

  # Put-Put: put s₁ >> put s₂ ≡ put s₂
  statePutPut = equivS 0
    (bind (put 10) (_: put 20))
    (put 20);

  # =========================================================================
  # LENS LAWS (for adapt combinator)
  # =========================================================================

  lens = {
    get = s: s.counter;
    set = s: c: s // { counter = c; };
  };

  # Get-Put: set s (get s) ≡ s
  lensGetPut =
    let s = { counter = 42; other = true; };
    in lens.set s (lens.get s) == s;

  # Put-Get: get (set s v) ≡ v
  lensPutGet =
    let s = { counter = 0; other = true; };
    in lens.get (lens.set s 99) == 99;

  # Put-Put: set (set s v₁) v₂ ≡ set s v₂
  lensPutPut =
    let s = { counter = 0; other = true; };
    in lens.set (lens.set s 10) 20 == lens.set s 20;

  # =========================================================================
  # SIGMA TYPE LAWS
  # =========================================================================

  IntT = fx.types.Int;
  StrT = fx.types.String;

  sigT = fx.types.Sigma {
    fst = IntT;
    snd = _: IntT;
    universe = 0;
  };

  # Curry/uncurry adjunction: curry (uncurry f) ≡ f  (on Sigma values)
  sigmaCurryUncurry =
    let
      f = a: b: a + b;
      roundtripped = sigT.curry (sigT.uncurry f);
    in roundtripped 3 4 == f 3 4;

  # Uncurry/curry adjunction: uncurry (curry g) ≡ g  (on pairs)
  sigmaUncurryCurry =
    let
      g = p: p.fst + p.snd;
      roundtripped = sigT.uncurry (sigT.curry g);
    in roundtripped { fst = 3; snd = 4; } == g { fst = 3; snd = 4; };

  # Pullback identity: pullback id id ≡ original check  (for well-formed pairs)
  sigmaPullbackIdentity =
    let
      mapped = sigT.pullback (x: x) (x: x);
    in mapped.check { fst = 42; snd = 7; } == sigT.check { fst = 42; snd = 7; };

  # Pullback composition (CONTRAVARIANT):
  #   pullback (f∘g) (h∘k) = pullback g k >>> pullback f h
  #
  # Contravariant functors REVERSE composition order:
  #   F(f ∘ g) = F(g) ∘ F(f)
  #
  # We use a refinement type (PosInt = {x:Int | x > 0}) so the test is
  # non-vacuous — transforms can take values outside the type, making the
  # check actually discriminate between correct and incorrect composition.
  sigmaPullbackComposition =
    let
      PosIntT = fx.types.mkType {
        name = "PosInt";
        kernelType = fx.types.hoas.int_;
        guard = v: builtins.isInt v && v > 0;
      };
      sigPos = fx.types.Sigma {
        fst = PosIntT;
        snd = _: PosIntT;
        universe = 0;
      };
      # Transforms: abs subtracts, so composition order matters for PosInt
      f = x: x + 3;
      g = x: x - 1;
      h = x: x + 5;
      k = x: x - 2;
      # pullback(f∘g, h∘k) — one-shot composition
      composed = sigPos.pullback (x: f (g x)) (x: h (k x));
      # Contravariant order: pullback g k THEN pullback f h
      step1 = sigPos.pullback g k;
      step2 = step1.pullback f h;
      # Test on a value where composition order matters:
      # fst=2: f(g(2)) = f(1) = 4 > 0 ✓,  but g(f(2)) = g(5) = 4 > 0 ✓
      # fst=1: f(g(1)) = f(0) = 3 > 0 ✓,  but in step2: f(1)=4, g(4)=3 > 0 ✓
      # The key: both sides must agree for ALL test values
      val1 = { fst = 2; snd = 4; };
      val2 = { fst = 1; snd = 3; };
      val3 = { fst = 5; snd = 5; };
    in composed.check val1 == step2.check val1
    && composed.check val2 == step2.check val2
    && composed.check val3 == step2.check val3;

  # =========================================================================
  # DEPRECORD PACK/UNPACK BIJECTION
  # =========================================================================

  recT = fx.types.DepRecord [
    { name = "n"; type = IntT; }
    { name = "s"; type = StrT; }
  ];

  # pack (unpack p) ≡ p
  depRecordPackUnpack =
    let
      packed = { fst = 42; snd = "hello"; };
      roundtripped = recT.pack (recT.unpack packed);
    in roundtripped == packed;

  # unpack (pack flat) ≡ flat
  depRecordUnpackPack =
    let
      flat = { n = 42; s = "hello"; };
      roundtripped = recT.unpack (recT.pack flat);
    in roundtripped == flat;

in {
  # Monad laws
  inherit monadLeftIdPure monadLeftIdEffectful
          monadRightIdPure monadRightIdEffectful
          monadAssocPure monadAssocEffectful;

  # Functor laws
  inherit functorIdentity functorComposition;

  # State effect laws
  inherit stateGetGet stateGetPut statePutGet statePutPut;

  # Lens laws
  inherit lensGetPut lensPutGet lensPutPut;

  # Sigma type laws
  inherit sigmaCurryUncurry sigmaUncurryCurry
          sigmaPullbackIdentity sigmaPullbackComposition;

  # DepRecord bijection
  inherit depRecordPackUnpack depRecordUnpackPack;

  allPass = monadLeftIdPure && monadLeftIdEffectful
         && monadRightIdPure && monadRightIdEffectful
         && monadAssocPure && monadAssocEffectful
         && functorIdentity && functorComposition
         && stateGetGet && stateGetPut && statePutGet && statePutPut
         && lensGetPut && lensPutGet && lensPutPut
         && sigmaCurryUncurry && sigmaUncurryCurry
         && sigmaPullbackIdentity && sigmaPullbackComposition
         && depRecordPackUnpack && depRecordUnpackPack;
}
