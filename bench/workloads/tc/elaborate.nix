# Elaborate-dominated workloads.
#
# `H.elab` runs the HOAS-to-Tm elaborator without invoking the kernel
# checker. The two ctorShape profiles in the elaborator's
# chain-flatten path correspond to the two workloads here:
#
#   - "saturated": every macro-ctor field is plain data; a single
#     flat `desc-con` Tm is emitted with the data field list as
#     payload.
#   - "recursive": exactly one rec field at the tail; the chain
#     trampolines along the rec arg via `genericClosure` and emits a
#     layered `desc-con` pyramid.
#
# Each workload returns the outer Tm tag; the recursive structure
# under it is forced lazily, so deepening the input mostly affects
# elaborator-internal cost rather than the .tag access itself.
{ fx }:

let
  H = fx.types.hoas;

  # Single-constructor datatype with `n` `data` fields, no `rec`.
  # Saturated application of `mk` triggers the flat-payload path.
  flatDT = n:
    let fields = builtins.genList
          (i: H.field "f${toString i}" H.nat) n;
    in H.datatype "Flat" [ (H.con "mk" fields) ];

  # n-ary saturated application: `mk 0 0 0 … 0`.
  flatApp = n:
    let DT = flatDT n;
        args = builtins.genList (_: H.zero) n;
    in builtins.foldl' (acc: a: H.app acc a) DT.mk args;

  # n-deep cons chain at `List Nat`. Trailing `rec` field on `cons`
  # routes through the linear-recursive flatten path.
  consChain = n:
    builtins.foldl'
      (acc: _: H.cons H.nat H.zero acc)
      (H.nil H.nat)
      (builtins.genList (x: x) n);

in {
  # Saturated chain at a 1000-data-field constructor. Forces the
  # elaborator to walk a 1000-arg app spine and assemble a single
  # flat `desc-con` Tm.
  flatten = (H.elab (flatApp 1000)).tag;

  # 1000-deep cons chain. Forces the recursive flatten path's
  # trampoline along the rec tail.
  recursive = (H.elab (consChain 1000)).tag;
}
