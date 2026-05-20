# nix-effects kernel: Freer monad operations with FTCQueue
#
# Monadic operations for the freer monad (Kiselyov & Ishii 2015).
# The Computation ADT (Pure/Impure) lives in comp.nix; this module
# builds send, bind, map, seq, pipe, and kleisli on top of it.
#
# The FTCQueue gives O(1) bind (snoc onto queue) instead of O(n)
# continuation composition. Left-nested bind chains are now O(n) total
# instead of O(n²).
{ fx, ... }:

let
  queue = fx.queue;
  inherit (fx.comp) pure impure isPure;

  send = name: param:
    impure { inherit name param; } queue.identity;

  bind = comp: f:
    if isPure comp then f comp.value
    else if comp.queue._variant == "Identity" then impure comp.effect (queue.singleton f)
    else impure comp.effect (queue.snoc comp.queue f);

  mapComp = f: comp: bind comp (x: pure (f x));

  seq = comps:
    builtins.foldl'
      (acc: comp: bind acc (_: comp))
      (pure null)
      comps;

  pipe = init: arrows:
    builtins.foldl'
      (acc: f: bind acc f)
      init
      arrows;

  kleisli = f: g: x: bind (f x) g;

in {
  inherit pure impure send bind;
  map = mapComp;
  inherit seq pipe kleisli;
  # Expose queue for advanced use (handler composition, adapt)
  inherit queue;

  __docs = {
    _self = {
      description = "Freer monad kernel: `send`/`bind`/`map`/`seq`/`pipe`/`kleisli` over the `Computation` ADT with FTCQueue continuations for O(1) bind.";
      doc = "Freer monad kernel: Return/OpCall ADT with FTCQueue bind, `send`, `map`, `seq`, `pipe`, `kleisli`.";
    };

    send = {
      description = "send: lift an effect request named `name` carrying `param` into a computation suspended at that effect; the handler's response resumes via the continuation queue.";
      signature = "send : String -> a -> Computation b";
      doc = "Send an effect request. Returns an `Impure` computation whose continuation queue resolves to the handler's response.";
      tests = {
        "creates-impure-with-effect" = {
          expr = (send "get" null).effect.name;
          expected = "get";
        };
        "queue-is-identity" = {
          expr = (send "get" null).queue._variant;
          expected = "Identity";
        };
      };
    };

    bind = {
      description = "bind: sequence two computations; if the first is `Pure`, apply `f` to its value; otherwise snoc `f` onto the FTCQueue for O(1) per-step composition.";
      signature = "bind : Computation a -> (a -> Computation b) -> Computation b";
      doc = ''
        Monadic bind:

        ```
        bind comp f = case comp of
          Pure a     -> f a
          Impure e q -> Impure e (snoc q f)
        ```

        O(1) per bind via FTCQueue snoc (Kiselyov & Ishii 2015, §3.1).
      '';
      tests = {
        "pure-bind-applies-f" = {
          expr = (bind (pure 21) (x: pure (x * 2))).value;
          expected = 42;
        };
        "impure-bind-preserves-effect" = {
          expr = (bind (send "get" null) (x: pure x)).effect.name;
          expected = "get";
        };
        "impure-bind-has-singleton-queue" = {
          expr =
            let
              comp = bind (send "get" null) (x: pure (x + 1));
            in comp.queue._variant;
          expected = "Leaf";
        };
      };
    };

    map = {
      description = "mapComp (exported as `map`): apply `f` to the eventual result of a computation (Functor instance); implemented as `bind comp (x: pure (f x))`.";
      signature = "map : (a -> b) -> Computation a -> Computation b";
      doc = "Map a function over the result of a computation (Functor instance). Exposed as `map` at the module's top-level.";
      tests = {
        "maps-pure" = {
          expr = (mapComp (x: x * 2) (pure 21)).value;
          expected = 42;
        };
      };
    };

    seq = {
      description = "seq: thread a list of computations left-to-right via bind, discarding intermediate values and returning only the last; the empty list yields `pure null`.";
      signature = "seq : [Computation a] -> Computation a";
      doc = "Sequence a list of computations, threading effects via `bind`. Returns the last result; intermediate values are discarded.";
      tests = {
        "sequences-empty" = {
          expr = isPure (seq []);
          expected = true;
        };
      };
    };

    pipe = {
      description = "pipe: chain a computation through a list of Kleisli arrows, threading each result into the next via bind; the empty arrow list yields `init` unchanged.";
      signature = "pipe : Computation a -> [(a -> Computation b)] -> Computation b";
      doc = "Chain a computation through a list of Kleisli arrows. Each arrow's input is the previous arrow's output.";
      tests = {
        "pipe-empty-returns-init" = {
          expr = (pipe (pure 42) []).value;
          expected = 42;
        };
        "pipe-single-arrow" = {
          expr = (pipe (pure 21) [(x: pure (x * 2))]).value;
          expected = 42;
        };
        "pipe-chains-results" = {
          expr = (pipe (pure 1) [
            (x: pure (x + 10))
            (x: pure (x * 3))
            (x: pure (x + 1))
          ]).value;
          expected = 34;  # (1 + 10) * 3 + 1
        };
        "pipe-threads-through-effects" = {
          expr = (pipe (send "get" null) [(x: pure (x + 1))]).effect.name;
          expected = "get";
        };
      };
    };

    kleisli = {
      description = "kleisli: compose two Kleisli arrows `(a -> M b)` and `(b -> M c)` into a single `(a -> M c)`; the arrow product of the freer-monad Kleisli category.";
      signature = "kleisli : (a -> Computation b) -> (b -> Computation c) -> a -> Computation c";
      doc = "Kleisli composition. Compose two Kleisli arrows into a single arrow. The associative `>=>` operator in Haskell terminology.";
      tests = {
        "kleisli-composes-pure" = {
          expr = (kleisli (x: pure (x + 1)) (x: pure (x * 2)) 10).value;
          expected = 22;  # (10 + 1) * 2
        };
        "kleisli-identity-left" = {
          expr = (kleisli pure (x: pure (x * 3)) 7).value;
          expected = 21;
        };
        "kleisli-identity-right" = {
          expr = (kleisli (x: pure (x * 3)) pure 7).value;
          expected = 21;
        };
        "kleisli-associative" = {
          expr =
            let
              f = x: pure (x + 1);
              g = x: pure (x * 2);
              h = x: pure (x - 3);
            in {
              lhs = (kleisli (kleisli f g) h 5).value;
              rhs = (kleisli f (kleisli g h) 5).value;
            };
          expected = {
            lhs = 9;  # ((5 + 1) * 2) - 3
            rhs = 9;
          };
        };
      };
    };
  };
}
