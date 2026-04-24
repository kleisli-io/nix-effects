# Typing contexts and kernel-run handler.
#
# `emptyCtx` / `extend` / `lookupType` form the de Bruijn context used by
# `check` / `infer`: index 0 is the most recent binding, matching eval's
# convention. `runCheck` runs a checking computation through the
# trampoline handler, unwrapping the `typeError` effect's `diag.Error`
# payload into a flat attrset so callers can inspect the failure.
#
# `error` holds the structured `diag.Error` (walkable via `children`
# for position/blame-path inspection). `msg`/`expected`/`got` are
# convenience projections of the leaf fields (`error.msg`,
# `error.detail.expected`, `error.detail.got`).
{ self, fx, ... }:

let
  V = fx.tc.value;
  TR = fx.trampoline;

  emptyCtx = { env = []; types = []; depth = 0; };

  extend = ctx: name: ty: {
    env = [ (V.freshVar ctx.depth) ] ++ ctx.env;
    types = [ ty ] ++ ctx.types;
    depth = ctx.depth + 1;
  };

  lookupType = ctx: i:
    if i >= builtins.length ctx.types
    then throw "tc: unbound variable index ${toString i} in context of depth ${toString ctx.depth}"
    else builtins.elemAt ctx.types i;

  runCheck = comp:
    let result = TR.handle {
      handlers.typeError = { param, state }: {
        abort = {
          error    = param.error;
          msg      = param.error.msg;
          expected = param.error.detail.expected;
          got      = param.error.detail.got;
        };
        state = null;
      };
    } comp;
    in result.value;
in {
  scope = {
    inherit emptyCtx extend lookupType runCheck;
    checkTm = ctx: tm: ty: runCheck (self.check ctx tm ty);
    inferTm = ctx: tm: runCheck (self.infer ctx tm);
  };
  tests = {};
}
