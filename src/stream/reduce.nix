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
        else fold.value f (f z step.head) step.tail);
  };

  toList = mk {
    doc = ''
      Collect all stream elements into a list.

      ```
      toList : Computation (Step r a) -> Computation [a]
      ```
    '';
    value = stream: fold.value (acc: x: acc ++ [ x ]) [] stream;
  };

  length = mk {
    doc = ''
      Count the number of elements in a stream.

      ```
      length : Computation (Step r a) -> Computation int
      ```
    '';
    value = stream: fold.value (n: _: n + 1) 0 stream;
  };

  sum = mk {
    doc = ''
      Sum all numeric elements in a stream.

      ```
      sum : Computation (Step r number) -> Computation number
      ```
    '';
    value = stream: fold.value (acc: x: acc + x) 0 stream;
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
        else any.value pred step.tail);
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
        else all.value pred step.tail);
  };

in mk {
  doc = "Stream reduction: fold, toList, length, sum, any, all.";
  value = {
    inherit fold toList length sum any all;
  };
}
