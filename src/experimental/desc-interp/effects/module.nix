{ self, api, ... }:

api.mk {
  description = "fx.experimental.desc-interp.effects: error and state effects over the description-side kernel — `error` raises, `EffState` is kernel-resident with handle_State.";
  doc = ''
    `error` exposes one op with `strict`/`collecting`/`result`
    handler strategies. `state` declares `EffState : Π(S:U). U` with
    `get`/`put`/`modify` and ships a kernel-term `handle_State`
    head-normalised at run-entry by the trampoline bridge.
  '';
  value = {
    inherit (self) error state;
    "error-shortcut-laws" = self."error-shortcut-laws";
    "error-uniform-shortcut-laws" = self."error-uniform-shortcut-laws";
    "state-shortcut-laws" = self."state-shortcut-laws";
  };
}
