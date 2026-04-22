# Check-dominated whole-pipeline workloads.
#
# Each entry is a `checkHoas TY TM` invocation chosen to push the
# kernel checker over a long term-or-type tree. The dominant cost is
# the bidirectional check pass; conv and eval costs are present but
# constant per workload.
{ fx }:

let
  H = fx.types.hoas;

  # Right-fold cons-chain of length n at element type `Nat`, fully
  # applied to nil at the tail. The HOAS elaborator trampolines large
  # cons chains via `genericClosure`, so the elaboration step is safe;
  # the check pass walks the resulting `desc-con` chain of length n.
  consChain = n:
    builtins.foldl'
      (acc: _: H.cons H.nat H.zero acc)
      (H.nil H.nat)
      (builtins.genList (x: x) n);

  # Datatype with `n` data fields on a single constructor. Each field
  # is a `field "fI" H.nat` slot; checking a constructor application
  # forces the kernel to validate every payload position.
  bigCtorDT = n:
    let fields = builtins.genList
          (i: H.field "f${toString i}" H.nat) n;
    in H.datatype "BigCtor" [ (H.con "mk" fields) ];

in {
  # 5000-deep `succ^5000 zero` checked at `Nat`. Forces the checker
  # over a desc-con tree whose recursion depth is dominated by
  # successive Nat constructor checks.
  nat-chain-5000 = (H.checkHoas H.nat (H.natLit 5000)).tag;

  # 5000-deep cons chain at `List Nat`. Each cons layer drives a
  # fresh check of the head + a recursion into the tail's check.
  list-chain-5000 = (H.checkHoas (H.listOf H.nat) (consChain 5000)).tag;

  # Single-constructor datatype with 20 nat-typed fields. Checking
  # the constructor application against the type forces 20 nested
  # field checks plus the surrounding mu walk.
  macro-field =
    let DT = bigCtorDT 20;
        args = builtins.genList (_: H.zero) 20;
        applied = builtins.foldl' (acc: a: H.app acc a) DT.mk args;
    in (H.checkHoas DT.T applied).tag;
}
