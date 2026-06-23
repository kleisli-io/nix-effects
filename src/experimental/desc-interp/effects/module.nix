{ self, partTests, api, ... }:

api.mk {
  description = "fx.experimental.desc-interp.effects: error, state, and typecheck effects over the description-side kernel — `error` raises, `EffState` is kernel-resident with handle_State, `typecheck` folds membership decisions.";
  doc = ''
    `error` exposes one op with `strict`/`collecting`/`result`
    handler strategies. `state` declares `EffState : Π(S:U). U` with
    `get`/`put`/`modify` and ships a kernel-term `handle_State`
    head-normalised at run-entry by the trampoline bridge.
    `typecheck` declares `EffTypeCheck : Π(R:U). U` with one `report`
    op and six policy handlers: five fold a stream of membership
    decisions, and `strict` throws on the first failure.
  '';
  value = {
    inherit (self) error state typecheck;
    "error-shortcut-laws" = self."error-shortcut-laws";
    "error-uniform-shortcut-laws" = self."error-uniform-shortcut-laws";
    "state-shortcut-laws" = self."state-shortcut-laws";
    "typecheck-shortcut-laws" = self."typecheck-shortcut-laws";
  };
  tests = partTests;
}
