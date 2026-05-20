# Kernel-resident bridge state chain: N iterations of
# `bind get (s: put (succ s))`. Per-Impure: `eval [] (H.elab op)` + two
# `vApp`s on `handlerCore` + Nix-side `dispatch` on the kernel-eval'd Sum.
#
# A/B variants: `s{N}` baselines measure `{handler; dispatch; evalOp}`
# (no per-op shortcut); `s{N}Short` enables `handlerShortcut` for the
# canonical `state-get`/`state-put` fast path. Bench is descriptive —
# the soundness gate is the H.refl-discharged shortcut lemma.
#
# `Elab.embedVal` reflects the response Val back into HOAS via the
# two-level-TT splice (`H.litVal`) — O(1) reflection, no `quote` walk.
{ fx }:

let
  H = fx.tc.hoas;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  Elab = fx.tc.elaborate;

  stateMod = fx.experimental.descInterp.effects.state;
  stateAtNat = stateMod.atType H.nat H.nat;

  pureD = K.pure stateAtNat.eff stateAtNat.resp H.nat;
  bindD = K.bind stateAtNat.eff stateAtNat.resp H.nat H.nat;

  prog = n: builtins.foldl'
    (acc: _: bindD acc (_:
      bindD stateAtNat.get (s:
        stateAtNat.put (H.succ (Elab.embedVal s)))))
    (pureD H.tt)
    (builtins.genList (i: i) n);

  mkBase = n:
    let
      result = T.handle stateAtNat.eff stateAtNat.resp H.nat
        {
          inherit (stateAtNat) handler dispatch evalOp;
          state = H.zero;
        }
        (prog n);
    in
      result.state.tag or "?";

  mkShort = n:
    let
      result = T.handle stateAtNat.eff stateAtNat.resp H.nat
        {
          inherit (stateAtNat) handler dispatch evalOp handlerShortcut;
          state = H.zero;
        }
        (prog n);
    in
      result.state.tag or "?";

in
{
  s1k = mkBase 1000;
  s10k = mkBase 10000;
  s1kShort = mkShort 1000;
  s10kShort = mkShort 10000;
}
