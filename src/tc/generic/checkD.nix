# Generic checker for payloads described by Desc.
{ self, fx, api, ... }:

let
  T = fx.tc.term;
  V = fx.tc.value;
  E = fx.tc.eval;
  C = fx.tc.check;
  K = fx.kernel;
  P = fx.diag.positions;

  inherit (K) pure bind;

  applyDescFn = fn: arg:
    if builtins.isAttrs fn && (fn.tag or null) == "VDescViewFn"
    then fn.apply arg
    else E.vApp fn arg;

  interpTy = spec:
    E.vInterpD spec.level spec.I spec.D spec.X spec.i;

  withD = spec: D: spec // { inherit D; };

  fallback = ctx: spec: tm:
    C.check ctx tm (interpTy spec);

  reverseList = xs:
    let n = builtins.length xs;
    in builtins.genList (i: builtins.elemAt xs (n - 1 - i)) n;

  rulePos = P.withRule "checkD";

  tailPositions = frames:
    reverseList (map (frame: rulePos frame.sndPos) frames);

  rebuildPairs = frames: leaf:
    builtins.foldl'
      (acc: frame: T.mkPair frame.fstTm acc)
      leaf
      frames;

  unaryInfo = spec: view:
    if view.idx == 1 then {
      fstPos = P.DArgSort;
      sndPos = P.DArgBody;
      fstTy = view.sTy;
      nextSpec = fstVal: withD spec (applyDescFn view.tFn fstVal);
    }
    else if view.idx == 2 then {
      fstPos = P.DRecIndex;
      sndPos = P.DRecTail;
      fstTy = E.vApp spec.X view.j;
      nextSpec = _: withD spec view.sub;
    }
    else if view.idx == 3 then {
      fstPos = P.DPiFn;
      sndPos = P.DPiBody;
      fstTy = V.vPi "s" view.sTy (V.mkClosure [ spec.X view.fn ]
        (T.mkApp (T.mkVar 1) (T.mkApp (T.mkVar 2) (T.mkVar 0))));
      nextSpec = _: withD spec view.sub;
    }
    else null;

  finishLeaf = path: ctx: frames: spec: tm:
    C.bindPChain (tailPositions frames) (checkDLeaf path ctx spec tm) (leafTm:
      pure (rebuildPairs frames leafTm));

  continueLoop = path: ctx: frames: spec: tm:
    checkDLoop {
      key = 0;
      inherit path ctx frames spec tm;
    };

  checkDLoop = start:
    let
      chain = builtins.genericClosure {
        startSet = [ start ];
        operator = item:
          if item ? done then [ ]
          else
            let
              view = self.descView item.spec.D;
              info = unaryInfo item.spec view;
            in
            if info == null || item.tm.tag != "pair" then
              [
                (item // {
                  key = item.key + 1;
                  done = "leaf";
                })
              ]
            else
              let
                comp = C.check item.ctx item.tm.fst info.fstTy;
                positions = tailPositions item.frames ++ [ (rulePos info.fstPos) ];
              in
              if fx.comp.isPure comp then
                let
                  fstTm = comp.value;
                  fstVal = E.eval item.ctx.env fstTm;
                  nextSpec = info.nextSpec fstVal;
                in
                [{
                  key = item.key + 1;
                  inherit (item) path ctx;
                  spec = nextSpec;
                  tm = item.tm.snd;
                  frames = [{
                    inherit fstTm;
                    sndPos = info.sndPos;
                  }] ++ item.frames;
                }]
              else
                [
                  (item // {
                    key = item.key + 1;
                    done = "suspended";
                    inherit comp positions info;
                  })
                ];
      };
      last = builtins.elemAt chain ((builtins.length chain) - 1);
    in
    if last.done == "leaf" then
      finishLeaf last.path last.ctx last.frames last.spec last.tm
    else
      C.bindPChain last.positions last.comp (fstTm:
        let
          fstVal = E.eval last.ctx.env fstTm;
          nextSpec = last.info.nextSpec fstVal;
        in
        continueLoop last.path last.ctx
          ([{ inherit fstTm; sndPos = last.info.sndPos; }] ++ last.frames)
          nextSpec
          last.tm.snd);

  checkDLeaf = path: ctx: spec: tm:
    let view = self.descView spec.D; in
    if view.idx == 0 then
      fallback ctx spec tm
    else if view.idx == 4 then
      let
        sv = E.sumPayloadTmView tm;
        go = pos: subSpec: subTm: k:
          C.bindPR pos "checkD" (checkDWithPath (path ++ [ pos ]) ctx subSpec subTm) k;
      in
      if sv == null then fallback ctx spec tm
      else if sv.side == "inl" then
        go P.DPlusL (withD spec view.A) sv.value
          (payload:
            pure (sv.rebuild payload))
      else
        go P.DPlusR (withD spec view.B) sv.value (payload:
          pure (sv.rebuild payload))
    else
      fallback ctx spec tm;

  checkDWithPath = path: ctx: spec: tm:
    continueLoop path ctx [ ] spec tm;

  checkDAt = ctx: spec: tm:
    checkDWithPath [ ] ctx spec tm;

  checkD = ctx: level: I: D: X: i: tm:
    checkDAt ctx { inherit level I D X i; } tm;

  inferDAt = ctx: spec: tm:
    bind (checkDAt ctx spec tm) (term:
      pure { inherit term; type = interpTy spec; });

  inferD = ctx: level: I: D: X: i: tm:
    inferDAt ctx { inherit level I D X i; } tm;
in
{
  scope = {
    checkD = api.leaf {
      value = checkD;
      description = "checkD: check a payload term against the interpretation of a description at a concrete index and recursive family.";
      signature = "checkD : Ctx -> Level -> I -> D -> X -> i -> Tm -> Computation Tm";
    };
    checkDAt = api.leaf {
      value = checkDAt;
      description = "checkDAt: spec-record variant of checkD; spec contains `{ level; I; D; X; i; }`.";
      signature = "checkDAt : Ctx -> { level; I; D; X; i; } -> Tm -> Computation Tm";
    };
    inferD = api.leaf {
      value = inferD;
      description = "inferD: synthesize the checked payload and its `interpD level I D X i` type.";
      signature = "inferD : Ctx -> Level -> I -> D -> X -> i -> Tm -> Computation { term; type; }";
    };
    inferDAt = api.leaf {
      value = inferDAt;
      description = "inferDAt: spec-record variant of inferD; spec contains `{ level; I; D; X; i; }`.";
      signature = "inferDAt : Ctx -> { level; I; D; X; i; } -> Tm -> Computation { term; type; }";
    };
  };

  tests =
    let
      T = fx.tc.term;
      V = fx.tc.value;
      E = fx.tc.eval;
      H = fx.tc.hoas;
      HI = H._internal._indexed;
      C = fx.tc.check;

      ctx0 = C.emptyCtx;
      evalDesc = h: E.eval [ ] (H.elab h);

      retUnit = H.retI H.unit 0 H.tt;
      Dret = evalDesc retUnit;
      Darg = evalDesc (H.descArg H.unit 0 H.unit (_: retUnit));
      Drec = evalDesc (HI.recI H.unit 0 H.tt retUnit);
      Dpi = evalDesc (HI.piI H.unit 0 H.unit (H.lam "_" H.unit (_: H.tt)) retUnit);
      Dplus = evalDesc (HI.plusI H.unit 0 retUnit retUnit);

      X_unit = V.vLam "_" V.vUnit (V.mkClosure [ ] T.mkUnit);
      spec = D: {
        level = V.vLevelZero;
        I = V.vUnit;
        inherit D;
        X = X_unit;
        i = V.vTt;
      };

      interp = D: E.vInterpD V.vLevelZero V.vUnit D X_unit V.vTt;
      plusLeft = T.mkBootInl
        (fx.tc.quote.quote 0 (interp Dret))
        (fx.tc.quote.quote 0 (interp Dret))
        T.mkBootRefl;
      plusRight = T.mkBootInr
        (fx.tc.quote.quote 0 (interp Dret))
        (fx.tc.quote.quote 0 (interp Dret))
        T.mkBootRefl;

      errorPathTags = err:
        if err.children == [ ] then [ ]
        else
          let edge = builtins.elemAt err.children 0;
          in [ edge.position.tag ] ++ errorPathTags edge.error;

      runErr = comp: (C.runCheck comp).error;
    in
    {
      "checkD-ret-accepts-refl" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dret) T.mkBootRefl)).tag;
        expected = "boot-refl";
      };

      "checkD-arg-accepts-pair" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Darg)
          (T.mkPair T.mkTt T.mkBootRefl))).tag;
        expected = "pair";
      };

      "checkD-rec-accepts-recursive-head-and-tail" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Drec)
          (T.mkPair T.mkTt T.mkBootRefl))).tag;
        expected = "pair";
      };

      "checkD-pi-accepts-function-head-and-tail" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dpi)
          (T.mkPair (T.mkLam "x" T.mkUnit T.mkTt) T.mkBootRefl))).tag;
        expected = "pair";
      };

      "checkD-plus-accepts-left-branch" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dplus) plusLeft)).tag;
        expected = "boot-inl";
      };

      "checkD-plus-accepts-right-branch" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dplus) plusRight)).tag;
        expected = "boot-inr";
      };

      "checkD-arg-rejects-bad-head" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Darg)
          (T.mkPair T.mkUnit T.mkBootRefl))) ? error;
        expected = true;
      };

      "checkD-arg-rejects-bad-tail" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Darg)
          (T.mkPair T.mkTt T.mkTt))) ? error;
        expected = true;
      };

      "checkD-rec-rejects-bad-head" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Drec)
          (T.mkPair T.mkUnit T.mkBootRefl))) ? error;
        expected = true;
      };

      "checkD-rec-rejects-bad-tail" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Drec)
          (T.mkPair T.mkTt T.mkTt))) ? error;
        expected = true;
      };

      "checkD-pi-rejects-bad-head" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dpi)
          (T.mkPair T.mkTt T.mkBootRefl))) ? error;
        expected = true;
      };

      "checkD-pi-rejects-bad-tail" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dpi)
          (T.mkPair (T.mkLam "x" T.mkUnit T.mkTt) T.mkTt))) ? error;
        expected = true;
      };

      "checkD-plus-left-rejects-bad-payload" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dplus)
          (T.mkBootInl
            (fx.tc.quote.quote 0 (interp Dret))
            (fx.tc.quote.quote 0 (interp Dret))
            T.mkTt))) ? error;
        expected = true;
      };

      "checkD-plus-right-rejects-bad-payload" = {
        expr = (C.runCheck (checkDAt ctx0 (spec Dplus)
          (T.mkBootInr
            (fx.tc.quote.quote 0 (interp Dret))
            (fx.tc.quote.quote 0 (interp Dret))
            T.mkTt))) ? error;
        expected = true;
      };

      "checkD-arg-head-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Darg)
          (T.mkPair T.mkUnit T.mkBootRefl)));
        expected = [ "DArgSort" ];
      };

      "checkD-arg-tail-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Darg)
          (T.mkPair T.mkTt T.mkTt)));
        expected = [ "DArgBody" "Sub" ];
      };

      "checkD-rec-head-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Drec)
          (T.mkPair T.mkUnit T.mkBootRefl)));
        expected = [ "DRecIndex" ];
      };

      "checkD-rec-tail-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Drec)
          (T.mkPair T.mkTt T.mkTt)));
        expected = [ "DRecTail" "Sub" ];
      };

      "checkD-pi-head-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Dpi)
          (T.mkPair T.mkTt T.mkBootRefl)));
        expected = [ "DPiFn" "Sub" ];
      };

      "checkD-pi-tail-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Dpi)
          (T.mkPair (T.mkLam "x" T.mkUnit T.mkTt) T.mkTt)));
        expected = [ "DPiBody" "Sub" ];
      };

      "checkD-plus-left-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Dplus)
          (T.mkBootInl
            (fx.tc.quote.quote 0 (interp Dret))
            (fx.tc.quote.quote 0 (interp Dret))
            T.mkTt)));
        expected = [ "DPlusL" "Sub" ];
      };

      "checkD-plus-right-error-position" = {
        expr = errorPathTags (runErr (checkDAt ctx0 (spec Dplus)
          (T.mkBootInr
            (fx.tc.quote.quote 0 (interp Dret))
            (fx.tc.quote.quote 0 (interp Dret))
            T.mkTt)));
        expected = [ "DPlusR" "Sub" ];
      };

      "inferD-returns-interp-type" = {
        expr = (C.runCheck (inferDAt ctx0 (spec Dret) T.mkBootRefl)).type.tag;
        expected = "VBootEq";
      };

      "inferD-arg-returns-sigma-type" = {
        expr = (C.runCheck (inferDAt ctx0 (spec Darg)
          (T.mkPair T.mkTt T.mkBootRefl))).type.tag;
        expected = "VSigma";
      };

      "inferD-plus-returns-sum-type" = {
        expr = (C.runCheck (inferDAt ctx0 (spec Dplus) plusRight)).type.tag;
        expected = "VBootSum";
      };
    };

}
