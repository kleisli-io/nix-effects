# Workload registry. Pure expressions keyed by the dotted path the runner uses
# to address them (`effects.interp.fib15`, `effects.stress.rawGC.s10k`,
# `tc.conv.identical-deep`, ...).
{ fx }:
{
  effects = import ./effects { inherit fx; };
  tc      = import ./tc      { inherit fx; };
}
