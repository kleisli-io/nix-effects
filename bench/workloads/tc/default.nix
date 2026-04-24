# Type-checking-kernel workloads. Microbenchmarks group by the kernel
# function they dominate (`conv`, `quote`, `check`, `infer`,
# `elaborate`); `e2e` carries whole-pipeline workloads through the
# user-facing surface.
{ fx }:
{
  conv      = import ./conv.nix      { inherit fx; };
  quote     = import ./quote.nix     { inherit fx; };
  check     = import ./check.nix     { inherit fx; };
  infer     = import ./infer.nix     { inherit fx; };
  elaborate = import ./elaborate.nix { inherit fx; };
  e2e       = import ./e2e.nix       { inherit fx; };
  diag      = import ./diag.nix      { inherit fx; };
  bindP     = import ./bindP.nix     { inherit fx; };
}
