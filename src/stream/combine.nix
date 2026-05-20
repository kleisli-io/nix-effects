# nix-effects stream/combine: Stream combination
#
# Combinators for merging multiple streams.
{ fx, ... }:
let
  core = fx.stream.core;
  inherit (fx.kernel) pure bind;
  concat = s1: s2:
    bind s1 (step:
      if step._tag == "Done" then s2
      else pure { _tag = "More"; inherit (step) head; tail = concat step.tail s2; });

  interleave = s1: s2:
    bind s1 (step1:
      if step1._tag == "Done" then s2
      else pure {
        _tag = "More";
        inherit (step1) head;
        tail = interleave s2 step1.tail;
      });

  zip = s1: s2:
    bind s1 (step1:
      if step1._tag == "Done" then core.done null
      else bind s2 (step2:
        if step2._tag == "Done" then core.done null
        else pure {
          _tag = "More";
          head = { fst = step1.head; snd = step2.head; };
          tail = zip step1.tail step2.tail;
        }));

  zipWith = f: s1: s2:
    bind s1 (step1:
      if step1._tag == "Done" then core.done null
      else bind s2 (step2:
        if step2._tag == "Done" then core.done null
        else pure {
          _tag = "More";
          head = f step1.head step2.head;
          tail = zipWith f step1.tail step2.tail;
        }));

in {
  inherit concat interleave zip zipWith;



  __docs = {
    _self = {
      description = "Stream combination: `concat`/`interleave`/`zip`/`zipWith` — merge two streams sequentially, alternately, or positionally.";
      doc = "Stream combination: concat, interleave, zip, zipWith.";
    };

    concat = {
      description = "concat: yield all elements of `s1`, then all elements of `s2`; if `s1` ends immediately we forward `s2` directly without rewrapping.";
      signature = "concat : Computation (Step r a) -> Computation (Step s a) -> Computation (Step s a)";
      doc = ''
        Concatenate two streams: all elements of the first, then all of
        the second. Sequential, not interleaved.
      '';
    };

    interleave = {
      description = "interleave: alternate elements between two streams; when the leading stream ends, the trailing stream takes over uninterrupted.";
      signature = "interleave : Computation (Step r a) -> Computation (Step s a) -> Computation (Step null a)";
      doc = ''
        Interleave two streams: alternate elements from each. When one
        stream ends the other continues to completion.
      '';
    };

    zip = {
      description = "zip: pair elements positionally into `{ fst, snd }` records; stops when either input stream ends.";
      signature = "zip : Computation (Step r a) -> Computation (Step s b) -> Computation (Step null { fst : a, snd : b })";
      doc = ''
        Zip two streams into a stream of pairs. Stops when either stream ends.
      '';
    };

    zipWith = {
      description = "zipWith: pair elements positionally and combine each pair with `f`; stops when either input stream ends.";
      signature = "zipWith : (a -> b -> c) -> Computation (Step r a) -> Computation (Step s b) -> Computation (Step null c)";
      doc = ''
        Zip two streams with a combining function. Stops when either stream ends.
      '';
    };

  };
}
