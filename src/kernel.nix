# nix-effects kernel: Freer monad ADT with FTCQueue
#
# Implements the freer monad from Kiselyov & Ishii (2015):
#   Computation a = Pure a | Impure (Effect x) (FTCQueue x a)
#
# Pure: computation finished with a value
# Impure: computation suspended at an effect, with a queue of continuations
#
# The FTCQueue gives O(1) bind (snoc onto queue) instead of O(n)
# continuation composition. Left-nested bind chains are now O(n) total
# instead of O(n²).
{ fx, api, ... }:

let
  queue = fx.queue;
  inherit (api) mk;

  # -- Core ADT --

  pure = mk {
    doc = "Lift a value into a pure computation (Return constructor).";
    value = value: { _tag = "Pure"; inherit value; };
    tests = {
      "creates-pure" = {
        expr = (pure.value 42)._tag;
        expected = "Pure";
      };
      "stores-value" = {
        expr = (pure.value 42).value;
        expected = 42;
      };
    };
  };

  impure = mk {
    doc = "Create a suspended computation (OpCall constructor). Takes an effect and a continuation queue.";
    value = effect: q: {
      _tag = "Impure";
      inherit effect;
      queue = q;
    };
    tests = {
      "creates-impure" = {
        expr = (impure.value { name = "test"; param = null; } (queue.singleton (x: pure.value x)))._tag;
        expected = "Impure";
      };
    };
  };

  # -- Derived operations --

  send = mk {
    doc = "Send an effect request. Returns the handler's response via continuation.";
    value = name: param: {
      _tag = "Impure";
      effect = { inherit name param; };
      queue = queue.singleton (value: { _tag = "Pure"; inherit value; });
    };
    tests = {
      "creates-impure-with-effect" = {
        expr = (send.value "get" null).effect.name;
        expected = "get";
      };
      "queue-applied-returns-pure" = {
        expr = (queue.qApp (send.value "get" null).queue 42)._tag;
        expected = "Pure";
      };
      "queue-applied-passes-value" = {
        expr = (queue.qApp (send.value "get" null).queue 42).value;
        expected = 42;
      };
    };
  };

  bind = mk {
    doc = ''
      Monadic bind: sequence two computations.
      bind comp f = case comp of
        Pure a       -> f a
        Impure e q   -> Impure e (snoc q f)

      O(1) per bind via FTCQueue snoc (Kiselyov & Ishii 2015, Section 3.1).
    '';
    value = comp: f:
      if comp._tag == "Pure"
      then f comp.value
      else {
        _tag = "Impure";
        inherit (comp) effect;
        queue = queue.snoc comp.queue f;
      };
    tests = {
      "pure-bind-applies-f" = {
        expr = (bind.value (pure.value 21) (x: pure.value (x * 2))).value;
        expected = 42;
      };
      "impure-bind-preserves-effect" = {
        expr = (bind.value (send.value "get" null) (x: pure.value x)).effect.name;
        expected = "get";
      };
      "impure-bind-chains-via-queue" = {
        expr =
          let
            comp = bind.value (send.value "get" null) (x: pure.value (x + 1));
          in (queue.qApp comp.queue 10).value;
        expected = 11;
      };
    };
  };

  mapComp = mk {
    doc = "Map a function over the result of a computation (Functor instance).";
    value = f: comp: bind.value comp (x: pure.value (f x));
    tests = {
      "maps-pure" = {
        expr = (mapComp.value (x: x * 2) (pure.value 21)).value;
        expected = 42;
      };
    };
  };

  # -- Sequencing helpers --

  seq = mk {
    doc = "Sequence a list of computations, threading state via bind. Returns the last result.";
    value = comps:
      builtins.foldl'
        (acc: comp: bind.value acc (_: comp))
        (pure.value null)
        comps;
    tests = {
      "sequences-empty" = {
        expr = (seq.value [])._tag;
        expected = "Pure";
      };
    };
  };

in mk {
  doc = "Freer monad kernel: Return/OpCall ADT with FTCQueue bind, send, map, seq.";
  value = {
    inherit pure impure send bind;
    map = mapComp;
    inherit seq;
    # Expose queue for advanced use (handler composition, adapt)
    inherit queue;
  };
}
