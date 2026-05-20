# Nix-callback state baseline: N iterations of `bind get (s: put (s+1))`.
# Per-Impure, `trampoline.run` does an attrset lookup on `param._opTag`
# and calls the handler directly — no `eval`, no `vApp`.
{ fx }:

let
  inherit (fx) pure bind handle;
  inherit (fx.effects) state;

  mk = n:
    let
      prog = builtins.foldl'
        (acc: _: bind acc (_:
          bind state.get (s:
            state.put (s + 1))))
        (pure 0)
        (builtins.genList (i: i) n);
      result = handle { handlers = state.handler; state = 0; } prog;
    in
    result.state;

in
{
  s1k = mk 1000;
  s10k = mk 10000;
}
