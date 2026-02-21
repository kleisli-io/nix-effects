# nix-effects stream/combine: Stream combination
#
# Combinators for merging multiple streams.
{ fx, api, ... }:

let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  inherit (api) mk;

  concat = mk {
    doc = ''
      Concatenate two streams: all elements of the first, then all of the second.

      concat : Computation (Step r a) -> Computation (Step s a) -> Computation (Step s a)
    '';
    value = s1: s2:
      bind s1 (step:
        if step._tag == "Done" then s2
        else pure { _tag = "More"; inherit (step) head; tail = concat.value step.tail s2; });
  };

  interleave = mk {
    doc = ''
      Interleave two streams: alternate elements from each.

      interleave : Computation (Step r a) -> Computation (Step s a) -> Computation (Step null a)
    '';
    value = s1: s2:
      bind s1 (step1:
        if step1._tag == "Done" then s2
        else pure {
          _tag = "More";
          inherit (step1) head;
          tail = interleave.value s2 step1.tail;
        });
  };

  zip = mk {
    doc = ''
      Zip two streams into a stream of pairs.
      Stops when either stream ends.

      zip : Computation (Step r a) -> Computation (Step s b) -> Computation (Step null {fst: a, snd: b})
    '';
    value = s1: s2:
      bind s1 (step1:
        if step1._tag == "Done" then core.done null
        else bind s2 (step2:
          if step2._tag == "Done" then core.done null
          else pure {
            _tag = "More";
            head = { fst = step1.head; snd = step2.head; };
            tail = zip.value step1.tail step2.tail;
          }));
  };

  zipWith = mk {
    doc = ''
      Zip two streams with a combining function.

      zipWith : (a -> b -> c) -> Computation (Step r a) -> Computation (Step s b) -> Computation (Step null c)
    '';
    value = f: s1: s2:
      bind s1 (step1:
        if step1._tag == "Done" then core.done null
        else bind s2 (step2:
          if step2._tag == "Done" then core.done null
          else pure {
            _tag = "More";
            head = f step1.head step2.head;
            tail = zipWith.value f step1.tail step2.tail;
          }));
  };

in mk {
  doc = "Stream combination: concat, interleave, zip, zipWith.";
  value = {
    inherit concat interleave zip zipWith;
  };
}
