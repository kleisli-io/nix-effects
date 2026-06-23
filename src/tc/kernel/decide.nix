# decide = psi : (t : KType) -> beta t -> Bool, the membership decision procedure
# for El t. The accumulated predicate-stack fold IS the decider, so decide ships
# no new recursion. Reductions:
#   decide (iota D)    x  ~> true
#   decide (refine t p) x ~> decide t x AND p x
{ self, api, ... }:

let
  inherit (self.ktype) decide;
in
{
  scope = {
    decide = api.leaf {
      description = "fx.tc.kernel.decide: the membership decision procedure decide = psi : (t:KType) -> beta t -> Bool.";
      value = decide;
    };
  };
}
