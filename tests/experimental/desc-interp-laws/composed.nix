# State's get-get law under `composeHandlers handle_State uniformOf_collecting`.
# Same structural-proof strategy as `state.nix`: both sides drive through
# `T.run` with the composed handler; `deepEqualDesc` discharges `.value`
# and the composed `.state` (Σ S (List E)). Operational witness that
# per-effect state laws transfer through the composed handler.
#
#   bind composedGet (λ_. bind composedGet (λn. pure n))
#     ≡  bind composedGet (λn. pure n)
{ lib, fx }:

let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.descInterp.kernel;
  T = fx.experimental.descInterp.trampoline;
  C = fx.experimental.descInterp.compose;
  G = fx.tc.generic.desc;
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
    else throw "experimental.descInterp.composed-laws.dispatch: expected VBootInl/VBootInr at outputVal.d.tag, got '${side}'";

  liftState = effStateOp:
    HI.inlAtExplicit H.levelZero EffStateAtS EffErrorAtE effStateOp;
  send_ = K.send composedEff Resp_Composed;
  composedGet = send_ (liftState (H.app EffState.get S));

  pureD = K.pure composedEff Resp_Composed H.nat;
  bindNN = K.bind composedEff Resp_Composed H.nat H.nat;

  asHoas = x: if x ? _htag then x else Elab.embedVal x;
  lawEq = lhs: rhs: G.deepEqualDesc (asHoas lhs) (asHoas rhs);

  runProg = prog: initS:
    T.run composedEff Resp_Composed H.nat
      { handler = composedHandler; dispatch = composedDispatch; }
      prog
      initS;

  getGetLhs = bindNN composedGet (_:
    bindNN composedGet (n: pureD n));
  getGetRhs = bindNN composedGet (n: pureD n);

  getGet = {
    initS = H.pair (H.succ (H.succ H.zero)) (HI.nilAtExplicit E);
    lhs = getGetLhs;
    rhs = getGetRhs;
  };

  proveLaw = law:
    let
      rL = runProg law.lhs law.initS;
      rR = runProg law.rhs law.initS;
    in
    lawEq rL.value rR.value && lawEq rL.state rR.state;

  testCases = {
    "composed-law-get-get" = { expr = proveLaw getGet; expected = true; };
  };

in
testCases
