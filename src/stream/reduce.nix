# nix-effects stream/reduce: Stream consumption/folding
#
# Terminal operations that consume a stream into a single value.
{ fx, api, ... }:
let
  inherit (fx.kernel) pure bind;
  fold = f: z: stream:
    bind stream (step:
      if step._tag == "Done" then pure z
      else fold f (f z step.head) step.tail);

  toList = stream: fold (acc: x: acc ++ [ x ]) [ ] stream;

  length = stream: fold (n: _: n + 1) 0 stream;

  sum = stream: fold (acc: x: acc + x) 0 stream;

  signalOn = z: cmp: stream:
    let
      go = current: s:
        bind s (step:
          if step._tag == "Done" then pure step
          else
            let
              next = step.head;
              same = cmp current next;
            in
            if same
            then go current step.tail
            else fx.stream.core.more next (go next step.tail));
    in
    fx.stream.core.more z (go z stream);

  signal = z: stream: signalOn z (x: y: x == y) stream;

  any = pred: stream:
    bind stream (step:
      if step._tag == "Done" then pure false
      else if pred step.head then pure true
      else any pred step.tail);

  all = pred: stream:
    bind stream (step:
      if step._tag == "Done" then pure true
      else if !(pred step.head) then pure false
      else all pred step.tail);

in
api.namespace {
  description = "Stream reduction: `fold`/`toList`/`length`/`sum`/`signal`/`signalOn`/`any`/`all` — terminal operations that consume a stream into a single computation.";
  doc = "Stream reduction: fold, toList, length, sum, signal, signalOn, any, all.";
  value = {
    fold = api.leaf {
      value = fold;
      description = "fold: left-fold a stream into a single value with initial accumulator `z`; the canonical terminal combinator other reducers delegate to.";
      signature = "fold : (b -> a -> b) -> b -> Computation (Step r a) -> Computation b";
      doc = ''
        Left fold over a stream. Drains the stream, threading the
        accumulator through `f` for each element.
      '';
    };

    toList = api.leaf {
      value = toList;
      description = "toList: collect all stream elements into a list in emission order; equivalent to `fold (acc: x: acc ++ [x]) []`.";
      signature = "toList : Computation (Step r a) -> Computation [a]";
      doc = ''
        Collect all stream elements into a list, preserving emission order.
      '';
    };

    length = api.leaf {
      value = length;
      description = "length: count the number of elements in a stream; equivalent to `fold (n: _: n + 1) 0` over the stream's element steps.";
      signature = "length : Computation (Step r a) -> Computation Int";
      doc = ''
        Count the number of elements in a stream.
      '';
    };

    sum = api.leaf {
      value = sum;
      description = "sum: sum all numeric elements in a stream starting from 0; equivalent to `fold (acc: x: acc + x) 0`.";
      signature = "sum : Computation (Step r Number) -> Computation Number";
      doc = ''
        Sum all numeric elements in a stream. Initial accumulator is `0`.
      '';
    };

    signalOn = api.leaf {
      value = signalOn;
      description = "signalOn: emit `z` then forward only values the comparator deems different from the previous emission; suppresses runs of equivalent inputs.";
      signature = "signalOn : a -> (a -> a -> Bool) -> Computation (Step r a) -> Computation (Step r a)";
      doc = ''
        Return a stream that emits only when the incoming values change.
        The comparator receives the current value and the next stream value;
        if they compare equal, the next value is skipped.

        The returned stream begins with the provided initial value `z`.
      '';
      tests = {
        "signalOn-empty-stream" = {
          expr = (fx.stream.reduce.toList (signalOn 42 (x: y: x == y) (fx.stream.core.fromList [ ]))).value;
          expected = [ 42 ];
        };
        "signalOn-skips-duplicate-values" = {
          expr = (fx.stream.reduce.toList (signalOn 0 (x: y: x == y) (fx.stream.core.fromList [ 0 0 1 1 2 ]))).value;
          expected = [ 0 1 2 ];
        };
        "signalOn-uses-comparator" = {
          expr = (fx.stream.reduce.toList (signalOn "init" (curr: next: builtins.substring 0 3 curr == builtins.substring 0 3 next) (fx.stream.core.fromList [ "odd-1" "odd-3" "even-2" "even-4" "odd-5" ]))).value;
          expected = [ "init" "odd-1" "even-2" "odd-5" ];
        };
      };
    };

    signal = api.leaf {
      value = signal;
      description = "signal: emit `z` then forward only values not structurally equal to the previous emission; specialisation of `signalOn` over `==`.";
      signature = "signal : a -> Computation (Step r a) -> Computation (Step r a)";
      doc = ''
        Return a stream that emits only when the incoming values change,
        using structural equality to detect duplicates.
        Equivalent to `signalOn z (x: y: x == y)`.
      '';
      tests = {
        "signal-identity-checks-equality" = {
          expr = (fx.stream.reduce.toList (signal 0 (fx.stream.core.fromList [ 0 0 1 1 2 ]))).value;
          expected = [ 0 1 2 ];
        };
      };
    };

    any = api.leaf {
      value = any;
      description = "any: return `true` if any element satisfies the predicate; short-circuits on first match via lazy evaluation of the stream tail.";
      signature = "any : (a -> Bool) -> Computation (Step r a) -> Computation Bool";
      doc = ''
        Check if any element satisfies a predicate. Short-circuits on
        first match — the rest of the stream is never forced.
      '';
    };

    all = api.leaf {
      value = all;
      description = "all: return `true` if every element satisfies the predicate; short-circuits on first miss via lazy evaluation of the stream tail.";
      signature = "all : (a -> Bool) -> Computation (Step r a) -> Computation Bool";
      doc = ''
        Check if all elements satisfy a predicate. Short-circuits on
        first failing element.
      '';
    };

  };
}
