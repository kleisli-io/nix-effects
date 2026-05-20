# Meta-aware evaluation overlay. Zonks first, then delegates to kernel
# eval on the meta-free result. Unsolved metas surface as a stuck
# `VMeta` value; the kernel evaluator is never invoked on a `meta`-bearing
# Tm.
{ self, fx, api, ... }:

let
  V = fx.tc.value;
  E = fx.tc.eval;
  # `mkMeta` lives in `tc/elaborate/quote.nix` (elaborate-level), not in
  # meta-dir's `self`. Reach it through the public namespace.
  M = fx.tc.elaborate.meta;

  evalElab = state: env: tm:
    let
      zr = self.zonkTm (builtins.length env) state tm;
    in
    if zr ? error
    then M.mkVMeta zr.error.id [ ] { ctx = zr.error.ctx; ty = V.vUnit; }
    else E.eval env zr.value;
in
{
  scope = {
    evalElab = api.leaf {
      value = evalElab;
      description = "evalElab state env tm: zonk tm against state.delta then delegate to kernel eval. Unsolved metas yield a stuck VMeta value.";
      signature = "evalElab : ElabState -> Env -> Tm -> Val";
      tests = {
        "evalElab-meta-free-delegates-to-kernel" = {
          expr = (evalElab { delta = { }; } [ ] fx.tc.term.mkTt).tag;
          expected = "VTt";
        };
        "evalElab-solved-meta-substitutes-then-evals" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "0" = self.mkSolved 0 V.vTt ty; }; };
              tm = M.mkMeta 0 [ ];
            in (evalElab state [ ] tm).tag;
          expected = "VTt";
        };
        "evalElab-unsolved-meta-returns-stuck-VMeta" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "3" = self.mkHole 3 ty; }; };
              tm = M.mkMeta 3 [ ];
            in (evalElab state [ ] tm)._vTag;
          expected = "VMeta";
        };
        "evalElab-unsolved-meta-carries-id" = {
          expr =
            let
              ty = { ctx = fx.tc.check.emptyCtx; ty = V.vUnit; };
              state = { delta = { "3" = self.mkHole 3 ty; }; };
              tm = M.mkMeta 3 [ ];
            in (evalElab state [ ] tm).id;
          expected = 3;
        };
      };
    };
  };
}
