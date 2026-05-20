# Bridge between the elaborator's meta-effects and the descInterp
# trampoline. The Nix-side Δ / 𝒦 / mentions live in a plain attrset
# threaded through `T.handle`'s `state` channel; the kernel handler
# (`self.handle_Meta`) is a ceremonial shell, and the per-op semantics
# live in `dispatchMeta` which reads `ctx.op._opTag` (sidecar from the
# `effects.nix` smart constructors) and `ctx.state`.
#
# Δ stores Hole/Solved metavariable entries. 𝒦 stores normalized
# constraints, and mentions indexes waiting constraints by metavariable id.
{ self, fx, api, ... }:

let
  T = fx.experimental.desc-interp.trampoline;
  Eff = self.metaEff;
  Resp = self.metaResp;

  emptyState = {
    delta = { };
    constraints = [ ];
    mentions = { };
    metaOrder = [ ];
    nextMetaId = 0;
    nextConstraintId = 0;
  };

  # ---- Per-op semantics ----------------------------------------------

  forceStep = v: state:
    {
      action = "resume";
      response = if self.isVMeta v then self.forceMeta v state else v;
      newState = state;
    };

  getMetasStep = state:
    { action = "resume"; response = state.delta; newState = state; };

  assignMetaStep = id: tm: state: {
    action = "resume";
    response = null;
    newState = self.processActiveConstraints (self.solveMeta id tm state);
  };

  emitConstraintStep = c: state:
    let r = self.addAndSimplifyConstraint c state; in {
      action = "resume";
      response = r.id;
      newState = self.processActiveConstraints r.state;
    };

  getConstraintsStep = state:
    { action = "resume"; response = state.constraints; newState = state; };

  freshMetaStep = type: state:
    let r = self.freshMetaInState type state; in
    { action = "resume"; response = r.meta; newState = r.state; };

  # ---- Dispatch ------------------------------------------------------

  dispatchMeta = ctx:
    let op = ctx.op; state = ctx.state; tag = op._opTag or null; in
    if tag == "force" then forceStep op.payload.v state
    else if tag == "getMetas" then getMetasStep state
    else if tag == "assignMeta" then assignMetaStep op.payload.id op.payload.tm state
    else if tag == "emitConstraint" then emitConstraintStep op.payload.c state
    else if tag == "getConstraints" then getConstraintsStep state
    else if tag == "freshMeta" then freshMetaStep op.payload.type state
    else throw "runElab.dispatchMeta: unknown meta-effect tag '${toString tag}'";

  # `runElab A program`: discharge an elaborator computation through
  # the descInterp trampoline. `A` is the program's HOAS result type.
  runElab = A: program:
    T.handle Eff Resp A
      {
        handler = self.handle_Meta;
        dispatch = dispatchMeta;
        state = emptyState;
      }
      program;

  # ---- Test fixtures -------------------------------------------------

  H = fx.tc.hoas;
  K = fx.experimental.desc-interp.kernel;
  bind_ = K.bind Eff Resp H.unit H.unit;
  pure_ = K.pure Eff Resp H.unit;

in
{
  scope = {
    emptyState = api.leaf {
      value = emptyState;
      description = "emptyState: initial `runElab` state — Δ, 𝒦, watcher index, ordered meta ids, and monotone fresh counters.";
      signature = "emptyState : ElabState";
      tests = {
        "emptyState-shape" = {
          expr = builtins.sort builtins.lessThan (builtins.attrNames emptyState);
          expected = [ "constraints" "delta" "mentions" "metaOrder" "nextConstraintId" "nextMetaId" ];
        };
        "emptyState-delta-empty" = { expr = emptyState.delta; expected = { }; };
        "emptyState-constraints-empty" = { expr = emptyState.constraints; expected = [ ]; };
      };
    };
    dispatchMeta = api.leaf {
      value = dispatchMeta;
      description = "dispatchMeta: bridge `dispatch` for the 5 meta-effects — selects the appropriate step on `ctx.op._opTag` and threads `ctx.state` (Nix-side Δ/𝒦/mentions attrset). Throws on unknown tags so accidental effect-set drift fails at build time.";
      signature = "dispatchMeta : { op; outputVal; state } -> { action; newState; response?; }";
      tests = {
        "dispatchMeta-rejects-unknown-op" = {
          expr = (builtins.tryEval (dispatchMeta {
            op = { _opTag = "unknown"; };
            outputVal = null;
            state = emptyState;
          })).success;
          expected = false;
        };
        "dispatchMeta-getMetas-passes-through" = {
          expr = (dispatchMeta {
            op = { _opTag = "getMetas"; };
            outputVal = null;
            state = emptyState;
          }).response;
          expected = { };
        };
      };
    };
    runElab = api.leaf {
      value = runElab;
      description = "runElab A program: discharge an elaborator computation through the descInterp trampoline. Threads `emptyState` Nix-side via the bridge's `state` channel; `handle_Meta` (kernel shell) plus `dispatchMeta` (Nix-side interpreter) discharge the 5 meta-effects.";
      signature = "runElab : Hoas U -> Hoas (μ freeFxApp metaEff metaResp A) -> { value; state : ElabState; }";
      tests = {
        "runElab-getMetas-on-empty-returns-empty-delta" = {
          expr = (runElab H.unit self.getMetas).value;
          expected = { };
        };
        "runElab-getConstraints-on-empty-returns-empty-list" = {
          expr = (runElab H.unit self.getConstraints).value;
          expected = [ ];
        };
        "runElab-assignMeta-then-getMetas" = {
          expr =
            let
              prog = bind_
                (self.assignMeta 0 "tm-stub")
                (_: self.getMetas);
            in
            (runElab H.unit prog).value;
          expected = { "0" = { id = 0; tag = "Solved"; tm = "tm-stub"; type = null; }; };
        };
        "runElab-emitConstraint-returns-id-zero" = {
          expr = (runElab H.unit (self.emitConstraint { lhs = null; rhs = null; })).value;
          expected = 0;
        };
        "runElab-emitConstraint-allocates-monotonically" = {
          expr =
            let
              prog = bind_
                (self.emitConstraint { lhs = null; rhs = "a"; })
                (id0: bind_
                  (self.emitConstraint { lhs = null; rhs = "b"; })
                  (id1: pure_ { inherit id0 id1; }));
            in
            (runElab H.unit prog).value;
          expected = { id0 = 0; id1 = 1; };
        };
        "runElab-emitConstraint-then-getConstraints" = {
          expr =
            let
              prog = bind_
                (self.emitConstraint { lhs = null; rhs = null; tag = "test"; })
                (_: self.getConstraints);
            in
            (runElab H.unit prog).value;
          expected = [
            {
              id = 0;
              lhs = null;
              rhs = null;
              tag = "test";
              position = null;
              mentions = [ ];
              status = "postponed";
            }
          ];
        };
        "runElab-force-kernel-val-passes-through" = {
          expr = (runElab H.unit (self.force fx.tc.value.vTt)).value == fx.tc.value.vTt;
          expected = true;
        };
        "runElab-force-unsolved-VMeta-returns-VMeta" = {
          expr =
            let
              m = self.mkVMeta 0 [ ] {
                ctx = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
                ty = fx.tc.value.vUnit;
              };
            in
            (runElab H.unit (self.force m)).value._vTag;
          expected = "VMeta";
        };
        "runElab-force-solved-VMeta-returns-bound-tm" = {
          # First assignMeta 0 "tm-stub", then force a VMeta with id=0:
          # dispatch consults Δ and resumes with the bound tm.
          expr =
            let
              m = self.mkVMeta 0 [ ] {
                ctx = { env = [ ]; types = [ ]; names = [ ]; depth = 0; };
                ty = fx.tc.value.vUnit;
              };
              prog = bind_
                (self.assignMeta 0 "tm-stub")
                (_: self.force m);
            in
            (runElab H.unit prog).value;
          expected = "tm-stub";
        };
        "runElab-final-state-carries-allocations" = {
          expr =
            let
              prog = bind_
                (self.assignMeta 7 "tm-seven")
                (_: bind_
                  (self.emitConstraint { lhs = "a"; rhs = "b"; })
                  (_: self.getConstraints));
              r = runElab H.unit prog;
            in
            {
              deltaHas7 = r.state.delta ? "7";
              nConstraints = builtins.length r.state.constraints;
              nextCid = r.state.nextConstraintId;
            };
          expected = { deltaHas7 = true; nConstraints = 1; nextCid = 1; };
        };
      };
    };
  };

}
