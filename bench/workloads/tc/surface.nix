{ fx }:

let
  S = fx.surface;
  H = fx.tc.hoas;

  boolIf = hoas: condition: onTrue: onFalse:
    hoas.boolElim 0 (hoas.lam "_" hoas.bool (_: hoas.bool)) onTrue onFalse condition;

  Toy = S.defineSurface {
    name = "BenchToyBool";
    constructors = {
      lit = {
        tag = "bench-toy.lit";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (if h.value then hoas.true_ else hoas.false_);
      };
      not = {
        tag = "bench-toy.not";
        handler = { depth, h, elaborate, hoas, ... }:
          elaborate depth (boolIf hoas h.term hoas.false_ hoas.true_);
      };
    };
  };

  lit = value: Toy.mk "lit" { inherit value; };
  not_ = term: Toy.mk "not" { inherit term; };

  nestedNot = n:
    builtins.foldl' (term: _: not_ term) (lit true) (builtins.genList (i: i) n);
in
{
  "toy-elaborate-100" = (H.elab (nestedNot 100)).tag;
}
