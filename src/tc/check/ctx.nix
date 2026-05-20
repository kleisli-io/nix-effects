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
{ self, fx, api, ... }:

let
  V = fx.tc.value;
  TR = fx.trampoline;
in
{
  scope = {
    emptyCtx = api.leaf {
      description = "emptyCtx: empty typing context `{ env = []; types = []; names = []; depth = 0; }` — the zero of `extend`; starting point for top-level `check`/`infer` invocations.";
      signature = "emptyCtx : Ctx";
      value = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
    };

    extend = api.leaf {
      description = "extend: append a binding to a typing context — pushes a fresh de Bruijn variable at depth `ctx.depth`, the new type at index 0, and the name at index 0 of `names`; depth increments by one.";
      signature = "extend : Ctx -> String -> Val -> Ctx";
      value = ctx: name: ty: {
        env = [ (V.freshVar ctx.depth) ] ++ ctx.env;
        types = [ ty ] ++ ctx.types;
        names = [ name ] ++ (ctx.names or [ ]);
        depth = ctx.depth + 1;
      };
    };

    lookupType = api.leaf {
      description = "lookupType: read a variable's type from a context by de Bruijn index — index 0 is the most recent binding; throws on out-of-range index with a descriptive message.";
      signature = "lookupType : Ctx -> Int -> Val";
      value = ctx: i:
        if i >= builtins.length ctx.types
        then throw "tc: unbound variable index ${toString i} in context of depth ${toString ctx.depth}"
        else builtins.elemAt ctx.types i;
    };

    runCheck = api.leaf {
      description = "runCheck: discharge a checking computation through the trampoline handler — collapses `typeError` into a flat `{ error; msg; expected; got }` record; returns the success value on the happy path.";
      signature = "runCheck : Computation a -> a | { error; msg; expected; got }";
      doc = ''
        Installs a `typeError` handler that aborts the computation on
        the first emission, exposing the structured `diag.Error` as
        `error` plus convenience projections `msg`,
        `expected`, and `got` (the leaf detail fields). The success
        branch returns whatever the computation yielded; only the
        post-handle `result.value` is exposed (state is discarded).

        Pair with `checkTm` / `inferTm` for the unwrapped form, or
        with `fx.tc.check.diag.runCheckD` / `runCheckDLazy` for
        hint-decorated failures.
      '';
      value = comp:
        let
          result = TR.handle
            {
              handlers.typeError = { param, state }: {
                abort = {
                  error = param.error;
                  msg = param.error.msg;
                  expected = param.error.detail.expected;
                  got = param.error.detail.got;
                };
                state = null;
              };
            }
            comp;
        in
        result.value;
    };

    checkTm = api.leaf {
      description = "checkTm: unwrapped variant of `check` — runs `runCheck (self.check ctx tm ty)` so callers get the elaborated term or a flat error record without manual trampoline handling.";
      signature = "checkTm : Ctx -> Tm -> Val -> Tm | { error; msg; expected; got }";
      value = ctx: tm: ty: self.runCheck (self.check ctx tm ty);
    };

    inferTm = api.leaf {
      description = "inferTm: unwrapped variant of `infer` — runs `runCheck (self.infer ctx tm)` so callers get `{ term; type }` or a flat error record without manual trampoline handling.";
      signature = "inferTm : Ctx -> Tm -> { term; type } | { error; msg; expected; got }";
      value = ctx: tm: self.runCheck (self.infer ctx tm);
    };
  };

  tests = { };
}
