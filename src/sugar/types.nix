{ fx, ... }:

let
  inherit (fx.types.refinement) refined;
  inherit (fx.types.primitives) Int String Bool Float Path Null Unit Any;

  sugared = t: t // {
    __functor = self: pred: sugared (refined "${self.name}?" self pred);
    __toString = self: self.name;
  };
in {
  scope = {
    types = {
      wrap = sugared;
      Int    = sugared Int;
      String = sugared String;
      Bool   = sugared Bool;
      Float  = sugared Float;
      Path   = sugared Path;
      Null   = sugared Null;
      Unit   = sugared Unit;
      Any    = sugared Any;
    };
  };

  tests = {};

  __docs = {
    types = {
      description = "types: refinement-applicable type wrappers — each primitive becomes a `__functor`-bearing record so `Int (n: n > 0)` chains another `refined` layer; `wrap` lifts an arbitrary type into the same callable form.";
      doc = ''
        Sugar layer over `fx.types.refinement.refined`. Each entry
        carries `__functor self pred = sugared (refined "name?" self pred)`,
        so calling a type as a function tightens it with a predicate.
        `__toString self = self.name` makes interpolated names
        readable. The wrapped primitives (`Int`, `String`, `Bool`,
        `Float`, `Path`, `Null`, `Unit`, `Any`) come from
        `fx.types.primitives`; `wrap` lets callers lift any other
        type into the same chainable shape.
      '';
    };
  };
}
