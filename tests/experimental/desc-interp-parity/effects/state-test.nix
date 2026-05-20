# Run the same observable computation through `fx.handle` and the
# descInterp bridge `T.handle`, then compare extracted Nix scalars.
#
# The two sides do not share value representations — prod state is
# raw Nix data, desc state is a kernel `Val`. Parity is on the
# extracted Nix view: `Elab.extract H.nat finalStateVal` turns the
# Val back into a Nix int for `==` against prod.
#
# `Elab.embedVal` is the Val→HOAS lift: a leaf body composing the
# handler's response Val (e.g. the current counter) with fresh HOAS
# (`H.succ …`) must wrap the Val first, otherwise the next
# `H.elab op` trips the non-HOAS-attrset guard at `tc/hoas/
# elaborate.nix:486-492`. NB: write `H.succ x`, not `H.app H.succ x`;
# `H.succ` is a Nix-level wrapper for `H.app NatDT.succ`, so the
# latter would put a bare Nix lambda in an `app.fn` slot.
{ lib, fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) state;

  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  Elab = fx.tc.elaborate;

  stateMod = fx.experimental.descInterp.effects.state;
  stateAtNat = stateMod.atType H.nat H.nat;
  pureD = K.pure stateAtNat.eff stateAtNat.resp H.nat;
  bindD = K.bind stateAtNat.eff stateAtNat.resp H.nat H.nat;

  # get; put(state+1); get. Initial 0 → final 1.
  stateCounter = {
    prod =
      let
        comp = bind state.get (n:
          bind (state.put (n + 1)) (_:
            bind state.get (n2:
              pure n2)));
        result = handle { handlers = state.handler; state = 0; } comp;
      in
      result.value;
    desc =
      let
        comp = bindD stateAtNat.get (n:
          bindD (stateAtNat.put (H.succ (Elab.embedVal n))) (_:
            bindD stateAtNat.get (n2:
              pureD n2)));
        result = T.handle stateAtNat.eff stateAtNat.resp H.nat
          {
            inherit (stateAtNat) handler dispatch;
            state = H.zero;
          }
          comp;
      in
      Elab.extract H.nat result.value;
  };

  parityOf = name: t: { inherit name; expr = t.desc; expected = t.prod; };

  testCases = {
    stateCounterParity = parityOf "stateCounter" stateCounter;
  };

in
testCases
