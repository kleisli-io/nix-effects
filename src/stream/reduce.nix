# nix-effects stream/reduce: Stream consumption/folding
#
# Terminal operations that consume a stream into a single value.
{ fx, api, ... }:

let
  inherit (fx.kernel) pure bind;
  inherit (api) mk;

  fold = mk {
    doc = ''
      Left fold over a stream.

      ```
      fold : (b -> a -> b) -> b -> Computation (Step r a) -> Computation b
      ```
    '';
    value = f: z: stream:
      bind stream (step:
        if step._tag == "Done" then pure z
        else fold f (f z step.head) step.tail);
  };

  toList = mk {
    doc = ''
      Collect all stream elements into a list.

      ```
      toList : Computation (Step r a) -> Computation [a]
      ```
    '';
    value = stream: fold (acc: x: acc ++ [ x ]) [] stream;
  };

  length = mk {
    doc = ''
      Count the number of elements in a stream.

      ```
      length : Computation (Step r a) -> Computation int
      ```
    '';
    value = stream: fold (n: _: n + 1) 0 stream;
  };

  sum = mk {
    doc = ''
      Sum all numeric elements in a stream.

      ```
      sum : Computation (Step r number) -> Computation number
      ```
    '';
    value = stream: fold (acc: x: acc + x) 0 stream;
  };

  signalOn = mk {
    doc = ''
      Return a stream that emits only when the incoming values change.
      The comparator receives the current value and the next stream value;
      if they compare equal, the next value is skipped.

      The returned stream begins with the provided initial value.

      ```
      signalOn : a -> (a -> a -> bool) -> Computation (Step r a) -> Computation (Step r a)
      ```
    '';
    value = z: cmp: stream:
      let
        go = current: s:
          bind s (step:
            if step._tag == "Done" then pure step
            else let next = step.head;
                     same = cmp current next;
                 in if same
                    then go current step.tail
                    else  fx.stream.core.more next (go next step.tail));
      in fx.stream.core.more z (go z stream);
    tests = {
      "signalOn-empty-stream" = {
        expr = (fx.stream.reduce.toList (signalOn 42 (x: y: x == y) (fx.stream.core.fromList []))).value;
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

  signal = mk {
    doc = ''
      Return a stream that emits only when the incoming values change,
      using structural equality to detect duplicates.
      Equivalent to `signalOn initialValue (x: y: x == y)`.

      ```
      signal : a -> Computation (Step r a) -> Computation (Step r a)
      ```
    '';
    value = z: stream: signalOn z (x: y: x == y) stream;
    tests = {
      "signal-identity-checks-equality" = {
        expr = (fx.stream.reduce.toList (signal 0 (fx.stream.core.fromList [ 0 0 1 1 2 ]))).value;
        expected = [ 0 1 2 ];
      };
    };
  };

  any = mk {
    doc = ''
      Check if any element satisfies a predicate.
      Short-circuits on first match (via lazy evaluation).

      ```
      any : (a -> bool) -> Computation (Step r a) -> Computation bool
      ```
    '';
    value = pred: stream:
      bind stream (step:
        if step._tag == "Done" then pure false
        else if pred step.head then pure true
        else any pred step.tail);
  };

  all = mk {
    doc = ''
      Check if all elements satisfy a predicate.

      ```
      all : (a -> bool) -> Computation (Step r a) -> Computation bool
      ```
    '';
    value = pred: stream:
      bind stream (step:
        if step._tag == "Done" then pure true
        else if !(pred step.head) then pure false
        else all pred step.tail);
  };

in mk {
  doc = "Stream reduction: fold, toList, length, sum, signal, signalOn, any, all.";
  value = {
    inherit fold toList length sum signal signalOn any all;
  };
}
