# fx.tc.kernel — kernel-internalized typecheck surface module head.
#
# Public export assembly for the flat predicate-stack internalization of
# `validate`. `self` is the cross-part fixpoint over the sibling parts;
# `partTests` is the aggregated nix-unit map.
{ self, partTests, api, ... }:

api.mk {
  description = "fx.tc.kernel: kernel-internalized `validate` via the flat predicate-stack KType / El family (base-and-predicate factoring).";
  doc = ''
    # fx.tc.kernel — KType Internalization

    Kernel-internal `validate` for the internalizable fragment of
    `mkType`-buildable types. A code is a base carrier type (any `U_0`
    type — a mu-encoded inductive or a primitive) paired with a finite
    stack of predicates over that carrier; the decider is the conjunction
    of the stack.

    ## Surface (`ktype`)

    - `KType : U_1` — a base carrier type paired with a predicate stack
    - `beta t : U_0` — the base carrier of a code (constant along refinement)
    - `psi t : beta t -> Bool` — the accumulated membership predicate
    - `El t` — the derived refinement subtype `Sigma x:beta t. P (psi t x)`
    - `P` — the `Bool -> U_0` membership decoder (`P true ~> Unit`, `P false ~> Void`)
    - `betaFn`/`decideFn`/`ElFn` — the same functions as closed kernel terms
    - `andB`, `iota`/`refine` constructor helpers

    ## Decision (`decide`)

    - `decide t : beta t -> Bool` — membership in `El t`; `decide = psi`
  '';
  value = {
    inherit (self) ktype decide reflect failure validate handlers;
  };
  tests = partTests;
}
