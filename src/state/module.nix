{ self, api, ... }:

api.mk {
  description = "fx.state: deepSeq-safe carrier for arbitrary values in handler state — `mkThunk`/`forceThunk` shield Nix closures from the trampoline per-step deepSeq.";
  doc = ''
    The trampoline deepSeq-forces handler state at each step;
    derivations and other cyclic attrsets hang. `mkThunk` wraps a
    value as `{ _tag = "Thunk"; _force = _: value; }` — Nix never
    recurses into a closure environment, so deepSeq sees only the
    inert tag and closure. Wrap before storing; unwrap with
    `forceThunk` after `fx.run`/`fx.handle` returns.
  '';
  value = {
    inherit (self) thunk;
  };
}
