{ fx }:

{
  interp = import ./interp { inherit fx; };
  buildSim = import ./build-sim { inherit fx; };
  categoryTheory = import ./category-theory { inherit fx; };
}
