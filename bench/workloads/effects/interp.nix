# Interpreter benchmarks — effect-based interpreter running scalable expressions.
#
# `fib*` — recursive Fibonacci at depth N (stresses bind/pure recursion).
# `lets*` — N nested let-bindings (stresses environment extension).
# `sum*` — arithmetic over N-element list (stresses primop + state).
# `countdown*` — N iterations of state decrement (stresses state handler).
# `ack*` — Ackermann function at small N (stresses deep recursion).
{ fx }:

let
  interp = import ../../../apps/interp { inherit fx; };
in {
  fib10  = interp.run interp.exprs.benchmarks.fib10;
  fib15  = interp.run interp.exprs.benchmarks.fib15;
  fib20  = interp.run interp.exprs.benchmarks.fib20;
  fib25  = interp.run interp.exprs.benchmarks.fib25;

  lets100  = interp.run interp.exprs.benchmarks.lets100;
  lets500  = interp.run interp.exprs.benchmarks.lets500;
  lets1000 = interp.run interp.exprs.benchmarks.lets1000;

  sum100  = interp.run interp.exprs.benchmarks.sum100;
  sum1000 = interp.run interp.exprs.benchmarks.sum1000;
  sum5000 = interp.run interp.exprs.benchmarks.sum5000;

  countdown1000  = interp.run interp.exprs.benchmarks.countdown1000;
  countdown10000 = interp.run interp.exprs.benchmarks.countdown10000;

  ack32 = interp.run interp.exprs.benchmarks.ack32;
  ack33 = interp.run interp.exprs.benchmarks.ack33;
}
