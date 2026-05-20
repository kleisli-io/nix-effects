# Composed state+error parity through the descInterp bridge.
#
# Effect = `Sum (EffState S) (EffError E)`; state = `Σ S (List E)`.
# Handler = `composeHandlers handle_State uniformOf_collecting` → UniRet
# shape `Sum (Σ Resp S) (Σ A S)`. Test program: `get; raise; put(n+1); get`.
# Parity: `(finalCounter, errorCount) == (1, 1)`.
#
# `Elab.embedVal` lifts the get-response Val into HOAS so the leaf can
# compose it under `H.succ` directly (not `H.app H.succ x` — that puts
# a bare Nix lambda in an `app.fn` slot and trips the elaborator).
{ lib, fx }:

let
  inherit (fx) bind handle;

  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  C = fx.experimental.descInterp.compose;
  Elab = fx.tc.elaborate;

  stateMod = fx.experimental.descInterp.effects.state;
  errorMod = fx.experimental.descInterp.effects.error;

  inherit (stateMod) EffState Resp_State handle_State;
  inherit (errorMod) EffError Resp_collecting uniformOf_collecting;

  S = H.nat;
  E = H.string;
  A = H.nat;

  EffStateAtS = H.app EffState.T S;
  EffErrorAtE = H.app EffError.T E;

  composedEff = H.sum EffStateAtS EffErrorAtE;

  Resp_Composed = C.composedRespAt EffStateAtS EffErrorAtE
    (H.app Resp_State S)
    (H.app Resp_collecting E);

  composedHandler =
    let
      S_B = H.listOf E;
      H_A = H.app (H.app handle_State S) A;
      H_B = H.app (H.app uniformOf_collecting E) A;
    in
    H.app
      (H.app
        (H.app
          (H.app
            (H.app
              (H.app
                (H.app
                  (H.app (H.app C.composeHandlers S) S_B)
                  EffStateAtS)
                EffErrorAtE)
              (H.app Resp_State S))
            (H.app Resp_collecting E))
          A)
        H_A)
      H_B;

  # `outputVal` is `Sum (Σ Resp S) (Σ A S)`; tag chooses resume/abort,
  # payload sits at `.d.val.fst`. Mirrors `state.atType.dispatch`.
  composedDispatch = ctx:
    let
      outputVal = ctx.outputVal;
      side = outputVal.d.tag;
      pair = outputVal.d.val.fst;
    in
    if side == "VBootInl" then {
      action = "resume";
      response = pair.fst;
      newState = pair.snd;
    }
    else if side == "VBootInr" then {
      action = "abort";
      value = pair.fst;
      newState = pair.snd;
    }
    else throw "experimental.descInterp.composed-test.dispatch: expected VBootInl/VBootInr at outputVal.d.tag, got '${side}'";

  # Smart constructors over the composed effect.
  send_ = K.send composedEff Resp_Composed;
  liftState = effStateOp:
    HI.inlAtExplicit H.levelZero EffStateAtS EffErrorAtE effStateOp;
  liftError = effErrorOp:
    HI.inrAtExplicit H.levelZero EffStateAtS EffErrorAtE effErrorOp;

  composedGet = send_ (liftState (H.app EffState.get S));
  composedPut = s: send_ (liftState (H.app (H.app EffState.put S) s));
  composedRaise = e: send_ (liftError (H.app (H.app EffError.error E) e));

  # Memoise per-A bind partials for the chain.
  bindNN = K.bind composedEff Resp_Composed H.nat H.nat;
  bindUN = K.bind composedEff Resp_Composed H.unit H.nat;

  # ----- Prod-side mirror -----
  #
  # Custom handler attrset over packed state `{counter; errors;}`. The
  # stock `state.handler` replaces the whole state on `put`, which
  # would clobber `errors`; the stock `error.collecting` puts the
  # error list directly in state, leaving no room for the counter.
  prodHandlers = {
    get = { state, ... }: { resume = state.counter; inherit state; };
    put = { param, state, ... }: {
      resume = null;
      state = state // { counter = param; };
    };
    modify = { param, state, ... }: {
      resume = null;
      state = state // { counter = param state.counter; };
    };
    error = { param, state, ... }: {
      resume = null;
      state = state // { errors = state.errors ++ [ param ]; };
    };
  };

  mixedProgram = {
    prod =
      let
        comp = bind fx.effects.state.get (n:
          bind (fx.effects.error.raise "warn") (_:
            bind (fx.effects.state.put (n + 1)) (_:
              fx.effects.state.get)));
        result = handle
          {
            handlers = prodHandlers;
            state = { counter = 0; errors = [ ]; };
          }
          comp;
      in
      {
        value = result.value;
        errorCount = builtins.length result.state.errors;
      };
    desc =
      let
        comp = bindNN composedGet (n:
          bindUN (composedRaise (H.stringLit "warn")) (_:
            bindUN (composedPut (H.succ (Elab.embedVal n))) (_:
              composedGet)));
        result = T.run composedEff Resp_Composed H.nat
          { handler = composedHandler; dispatch = composedDispatch; }
          comp
          (H.pair H.zero (HI.nilAtExplicit E));
      in
      {
        value = Elab.extract H.nat result.value;
        # `result.state` is a kernel sigma Val (`pair counter errors`);
        # `.snd` is the errors list Val directly — no re-embed needed.
        errorCount = builtins.length
          (Elab.extract (H.listOf E) result.state.snd);
      };
  };

  parityOf = name: t: {
    inherit name;
    expr = t.desc;
    expected = t.prod;
  };

  testCases = {
    mixedStateErrorParity = parityOf "mixedStateError" mixedProgram;
  };

in
testCases
