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
      description = "emptyCtx: empty typing context `{ env = envNil; types = envNil; names = envNil; depth = 0; }` — the zero of `extend`; starting point for top-level `check`/`infer` invocations. env/types/names are de Bruijn cons-list spines (index 0 = most recent binding) walked iteratively by `envNth`, so deep contexts stay host-stack- and call-depth-flat.";
      signature = "emptyCtx : Ctx";
      value = { env = V.envNil; types = V.envNil; names = V.envNil; depth = 0; };
    };

    extend = api.leaf {
      description = "extend: append a binding to a typing context — pushes a fresh de Bruijn variable at depth `ctx.depth`, the new type at index 0, and the name at index 0 of `names`; depth increments by one. `depth`/`eb` are forced at each extend so the scalar counters stay plain ints, never deferred `+1`/`or`-thunk chains that recurse N-deep on the C-stack when finally forced (cf. value.nix env-spine memo). The entry-yield budget `eb` carries through unchanged (consumed only at `check`/`infer` heads).";
      signature = "extend : Ctx -> String -> Val -> Ctx";
      value = ctx: name: ty:
        let
          d = ctx.depth + 1;
          e = ctx.eb or 0;
        in
        builtins.seq d (builtins.seq e {
          env = V.envCons (V.freshVar ctx.depth) ctx.env;
          types = V.envCons ty ctx.types;
          names = V.envCons name (ctx.names or V.envNil);
          depth = d;
          eb = e;
        });
    };

    lookupType = api.leaf {
      description = "lookupType: read a variable's type from a context by de Bruijn index — index 0 is the most recent binding; throws on out-of-range index with a descriptive message. Indexes the `types` cons-list spine via the iterative `envNth` (host-stack- and call-depth-flat); the bound check uses the O(1) `depth` counter (= spine length) instead of re-walking the spine.";
      signature = "lookupType : Ctx -> Int -> Val";
      value = ctx: i:
        if i >= ctx.depth
        then throw "tc: unbound variable index ${toString i} in context of depth ${toString ctx.depth}"
        else V.envNth ctx.types i;
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
              state = { blame = self._blame.empty; };
              handlers = self._blame.handlers // self._yield.handlers // {
                typeError = { param, state }: {
                  abort =
                    let e = self._blame.fold state.blame param.error; in
                    { error = e; msg = e.msg; expected = e.detail.expected; got = e.detail.got; };
                  state = null;
                };
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
