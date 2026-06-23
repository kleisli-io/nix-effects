# Typecheck-policy handlers over the description-side kernel. A producer folds
# a stream of membership decisions; each decision is one `report` op carrying a
# diagnostic reason (a closed enum), a structural blame path (a list of value-side
# positions), an opaque host-rendered residue `R`, and the host-precomputed
# boolean outcome. `reason` and `path` are internalized diagnostic coordinates; the
# residue is never inspected — there is no kernel string introspection, so an `R`
# carrier is opaque by construction, and a structured `R` (e.g. `DiagError`) is
# ferried by the resume handlers exactly as opaquely as a bare string.
#
#   EffTypeCheck : Π(R:U). U    one op `report(reason, path, carrier, passed)`
#   Resp report  ≡ Unit         every op resumes; the decision rides in the op
#
# Each strategy is a kernel-term handler returning a bare `Σ State Unit`, paired
# with a Nix-side `dispatch` that resumes with the pair's components:
#
#   collecting → Σ (List R) Unit             fail conses the residue, pass keeps
#   logging    → Σ (List (Σ Bool R)) Unit    always records the outcome + residue
#   firstN     → Σ (Σ (List R) Nat) Unit     down-counter; record while it lasts
#   summarize  → Σ (Σ ByReason (Σ Nat Nat)) Unit  group by the reason enum
#   pretty     → Σ (List R) Unit             cons the host-rendered line on fail
#
# `firstN` carries a down-counter rather than re-measuring the collected list,
# so its abort test is O(1); the abort flag is recovered as `remaining = 0`.
# `summarize` groups by the five-token reason enum via its eliminator — no string
# comparison; the host renders the line and keys its own attrset.
{ fx, api, lib, ... }:

let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  K = fx.experimental.desc-interp.kernel;
  T = fx.experimental.desc-interp.trampoline;

  app = H.app;
  lam = H.lam;
  forall = H.forall;
  sigma = H.sigma;
  ann = H.ann;
  con = H.con;
  field = H.field;
  pair = H.pair;
  fst_ = H.fst_;
  snd_ = H.snd_;
  cons = H.cons;
  nil = H.nil;
  succ = H.succ;
  zero = H.zero;
  boolElim = H.boolElim;
  ind = H.ind;
  nat = H.nat;
  bool = H.bool;
  unit = H.unit;
  tt = H.tt;
  listOf = H.listOf;
  listElim = H.listElim;
  string = H.string;
  strEq = H.strEq;
  sl = H.stringLit;
  nlit = H.natLit;
  u0 = H.u 0;

  # ---- Closed diagnostic reason enum ----
  ReasonDT = H.datatype "Reason" [
    (con "shapeMismatch" [ ])
    (con "missingField" [ ])
    (con "extraField" [ ])
    (con "predicateFailed" [ ])
    (con "deferredPi" [ ])
  ];
  Reason = ReasonDT.T;
  # ReasonDT.elim 0 motive b0 b1 b2 b3 b4 scrut.
  reasonElim = motive: b0: b1: b2: b3: b4: scrut:
    app (app (app (app (app (app (app (ReasonDT.elim 0) motive) b0) b1) b2) b3) b4) scrut;

  # ---- Structural descent path ----
  # A path names the descent from a validation root to the failure site. Its
  # alphabet is exactly what a value-side walk emits: a record field, a list
  # element, a variant arm, a tuple component. `name` rides as a strEq-comparable
  # carrier and `idx` is a kernel Nat; the rendered segment text stays host-side,
  # having no description-language analogue.
  PositionDT = H.datatype "Position" [
    (con "Field" [ (field "name" string) ])
    (con "Elem" [ (field "idx" nat) ])
    (con "Tag" [ (field "name" string) ])
    (con "Tuple" [ (field "idx" nat) ])
  ];
  Position = PositionDT.T;
  Path = listOf Position;
  # PositionDT.elim 0 motive bField bElem bTag bTuple scrut.
  positionElim = motive: bF: bE: bT: bU: scrut:
    app (app (app (app (app (app (PositionDT.elim 0) motive) bF) bE) bT) bU) scrut;

  # ---- Effect: one op carrying reason, path, residue, and the host decision ----
  # `reason` and `path` are the internalized diagnostic coordinates (the failure
  # intent and the structural blame site); `carrier` is the opaque host-rendered
  # residue; `passed` is the host-precomputed decision. They mirror the producer's
  # typeCheck payload `{ reason, path, value, … }`.
  EffTC = H.datatypeP "EffTypeCheck" [{ name = "R"; kind = u0; }] (ps:
    let R = builtins.elemAt ps 0; in [
      (con "report" [
        (field "reason" Reason)
        (field "path" Path)
        (field "carrier" R)
        (field "passed" bool)
      ])
    ]);
  EffTCTy = forall "R" u0 (_: u0);
  reportAt = R: reason: path: carrier: passed:
    app (app (app (app (app EffTC.report R) reason) path) carrier) passed;

  # ---- Response: every op resumes with Unit ----
  RespTy = forall "R" u0 (R: forall "_op" (app EffTC.T R) (_op: u0));
  Resp = ann
    (lam "R" u0 (R:
      let Et = app EffTC.T R; in
      lam "op" Et (op:
        app
          (app
            (app
              (app (EffTC.elim 1) R)
              (lam "_op" Et (_op: u0)))
            (lam "_r" Reason (_: lam "_pth" Path (_: lam "_c" R (_: lam "_p" bool (_: unit))))))
          op)))
    RespTy;

  # ---- State shapes ----
  collState = R: listOf R;
  LogRec = R: sigma "_" bool (_: R);
  logState = R: listOf (LogRec R);
  firstNState = R: sigma "_" (listOf R) (_: nat);
  ByReason = sigma "_" nat (_: sigma "_" nat (_: sigma "_" nat (_: sigma "_" nat (_: nat))));
  pfTy = sigma "_" nat (_: nat);
  summState = sigma "_" ByReason (_: pfTy);

  # ByReason holds the per-reason counters in constructor order, plus the
  # (passed, failed) totals alongside.
  mkByReason = c0: c1: c2: c3: c4: pair c0 (pair c1 (pair c2 (pair c3 c4)));
  byReasonZero = mkByReason zero zero zero zero zero;
  cShape = b: fst_ b;
  cMissing = b: fst_ (snd_ b);
  cExtra = b: fst_ (snd_ (snd_ b));
  cPred = b: fst_ (snd_ (snd_ (snd_ b)));
  cDeferred = b: snd_ (snd_ (snd_ (snd_ b)));
  bumpReason = r: b:
    reasonElim (lam "_" Reason (_: ByReason))
      (mkByReason (succ (cShape b)) (cMissing b) (cExtra b) (cPred b) (cDeferred b))
      (mkByReason (cShape b) (succ (cMissing b)) (cExtra b) (cPred b) (cDeferred b))
      (mkByReason (cShape b) (cMissing b) (succ (cExtra b)) (cPred b) (cDeferred b))
      (mkByReason (cShape b) (cMissing b) (cExtra b) (succ (cPred b)) (cDeferred b))
      (mkByReason (cShape b) (cMissing b) (cExtra b) (cPred b) (succ (cDeferred b)))
      r;

  # ---- Assoc-list byReason (alongside the closed-enum ByReason) ----
  # The production handler keys a `byReason` attrset by the reason token; the
  # internalized counterpart is an association list `List (Σ String Nat)` keyed
  # by the same tokens. The closed-enum `ByReason` bump is O(1); this assoc list
  # is the `assocListToAttrs` shape that matches production order-insensitively.
  Entry = sigma "_" string (_: nat);
  Assoc = listOf Entry;
  summAssocState = R: sigma "_" Assoc (_: pfTy);

  # Each enum constructor renders to its production `byReason` key token.
  reasonName = reasonElim (lam "_" Reason (_: string))
    (sl "shape-mismatch")
    (sl "missing-field")
    (sl "extra-field")
    (sl "predicate-failed")
    (sl "deferred-pi");

  # One structural fold returning the updated assoc list. Reaching `onNil` means
  # no entry matched, so it emits the new `(key, 1)`. On a match the head count
  # is bumped and the original tail `t` is kept (the speculative `(key, 1)` that
  # `onNil` appends lives only in the recursion `ih`, discarded here); on a miss
  # the head is kept and `ih` carries the rest. The branch is chosen by `strEq`
  # on the key. Reusing a projected bound var is fine, but reusing a projected
  # compound across branches would introduce an un-inferable `let`, so a
  # found-flag carrier is deliberately avoided.
  insertOrIncrement = key: assoc:
    listElim 0 Entry
      (lam "_" Assoc (_: Assoc))
      (HI.consAtExplicit Entry (pair key (nlit 1)) (HI.nilAtExplicit Entry))
      (lam "h" Entry (h:
        lam "t" Assoc (t:
          lam "ih" Assoc (ih:
            boolElim 0 (lam "_" bool (_: Assoc))
              (HI.consAtExplicit Entry (pair (fst_ h) (succ (snd_ h))) t)
              (HI.consAtExplicit Entry h ih)
              (strEq (fst_ h) key)))))
      assoc;

  # ---- Handler builder ----
  # handle_X : Π R. Π op. Π _s:State. Σ State Unit. `stepOf` is the state
  # transition; the payload is always `tt` (every strategy resumes).
  mkHandleTy = stateOf:
    forall "R" u0 (R:
      forall "op" (app EffTC.T R) (_op:
        forall "_s" (stateOf R) (_s:
          sigma "_st" (stateOf R) (_: unit))));

  mkHandle = stateOf: stepOf:
    ann
      (lam "R" u0 (R:
        let
          Et = app EffTC.T R;
          State = stateOf R;
          motive = lam "_op" Et (_op:
            forall "_s" State (_s: sigma "_st" State (_: unit)));
          onReport = lam "_reason" Reason (reason:
            lam "_path" Path (path:
              lam "_carrier" R (carrier:
                lam "_passed" bool (passed:
                  lam "_s" State (s:
                    pair (stepOf R reason path carrier passed s) tt)))));
        in
        lam "op" Et (op:
          app (app (app (app (EffTC.elim 0) R) motive) onReport) op)))
      (mkHandleTy stateOf);

  # A pass keeps the accumulator; a fail conses the residue.
  collStep = R: _reason: _path: carrier: passed: s:
    boolElim 0 (lam "_" bool (_: collState R)) s (cons carrier s) passed;

  # Every decision is recorded with its outcome. The element type is supplied
  # explicitly because a bare pair does not synthesize its Σ type.
  logStep = R: _reason: _path: carrier: passed: s:
    HI.consAtExplicit (LogRec R) (pair passed carrier) s;

  # A down-counter. A pass holds; a fail at `rem = suc rp` records and
  # decrements; a fail at `rem = 0` drops and holds (the abort state). The
  # recorded list in the suc branch is annotated because the `ind` step body is
  # synthesized, not checked, so a bare cons would carry no element type.
  firstNStep = R: _reason: _path: carrier: passed: s:
    let
      coll = fst_ s;
      rem = snd_ s;
    in
    boolElim 0 (lam "_" bool (_: firstNState R))
      s
      (ind 0 (lam "_" nat (_: firstNState R))
        (pair coll zero)
        (lam "rp" nat (rp:
          lam "_ih" (firstNState R) (_:
            pair (ann (cons carrier coll) (listOf R)) rp)))
        rem)
      passed;

  # A pass bumps the passed total; a fail bumps the failed total and the
  # per-reason counter. Per-failure data is dropped, so state is bounded.
  summStep = R: reason: _path: _carrier: passed: s:
    let
      br = fst_ s;
      pf = snd_ s;
      pt = fst_ pf;
      ft = snd_ pf;
    in
    boolElim 0 (lam "_" bool (_: summState))
      (pair br (pair (succ pt) ft))
      (pair (bumpReason reason br) (pair pt (succ ft)))
      passed;

  # The assoc-list summarize: same totals as `summStep`, but a fail inserts or
  # increments the reason's entry in the `List (Σ String Nat)` byReason instead
  # of bumping a fixed enum counter.
  summAssocStep = R: reason: _path: _carrier: passed: s:
    let
      br = fst_ s;
      pf = snd_ s;
      pt = fst_ pf;
      ft = snd_ pf;
    in
    boolElim 0 (lam "_" bool (_: summAssocState R))
      (pair br (pair (succ pt) ft))
      (pair (insertOrIncrement (reasonName reason) br) (pair pt (succ ft)))
      passed;

  # The host renders the failure line; the kernel conses it opaquely on a fail.
  prettyStep = collStep;

  collHandleTy = mkHandleTy collState;
  logHandleTy = mkHandleTy logState;
  firstNHandleTy = mkHandleTy firstNState;
  summHandleTy = mkHandleTy (R: summState);
  prettyHandleTy = mkHandleTy collState;

  handle_collecting = mkHandle collState collStep;
  handle_logging = mkHandle logState logStep;
  handle_firstN = mkHandle firstNState firstNStep;
  handle_summarize = mkHandle (R: summState) summStep;
  handle_pretty = mkHandle collState prettyStep;

  summAssocHandleTy = mkHandleTy summAssocState;
  handle_summarizeAssoc = mkHandle summAssocState summAssocStep;

  # ---- Strict handler: conditional throw via a UniRet Sum ----
  # No accumulator. A pass resumes with tt down the left summand; a fail
  # surrenders the residue down the right summand for the dispatcher to
  # throw on. The decision is the host-precomputed `passed`, so the choice
  # is a `boolElim`, not an unconditional abort.
  strictLeft = sigma "_r" unit (_: unit);
  strictRight = R: sigma "_a" R (_: unit);
  strictSum = R: H.sum strictLeft (strictRight R);

  mkStrictHandleTy = forall "R" u0 (R:
    forall "op" (app EffTC.T R) (_op:
      forall "_s" unit (_s: strictSum R)));

  handle_strict = ann
    (lam "R" u0 (R:
      let
        Et = app EffTC.T R;
        motive = lam "_op" Et (_op: forall "_s" unit (_s: strictSum R));
        onReport = lam "_reason" Reason (_reason:
          lam "_path" Path (_path:
            lam "_carrier" R (carrier:
              lam "_passed" bool (passed:
                lam "_s" unit (s:
                  boolElim 0 (lam "_" bool (_: strictSum R))
                    (HI.inlAtExplicit H.levelZero strictLeft (strictRight R) (pair tt s))
                    (HI.inrAtExplicit H.levelZero strictLeft (strictRight R) (pair carrier s))
                    passed)))));
      in
      lam "op" Et (op:
        app (app (app (app (EffTC.elim 0) R) motive) onReport) op)))
    mkStrictHandleTy;

  # ---- atType factory ----
  # The bare `Σ State Unit` output is read as resume: `.fst` new state,
  # `.snd` the resume payload (`tt`).
  dispatchResume = ctx:
    let o = ctx.outputVal; in {
      action = "resume";
      newState = o.fst or null;
      response = o.snd or null;
    };

  # Reads the UniRet Sum: a left (resume) carries `(tt, state)`, a right
  # (throw) carries `(residue, state)` — the dispatcher raises on the right.
  dispatchStrict = ctx:
    let
      outputVal = ctx.outputVal;
      side = outputVal.d.tag;
      p = outputVal.d.val.fst;
    in
    if side == "VBootInl" then {
      action = "resume";
      response = p.fst;
      newState = p.snd;
    }
    else if side == "VBootInr" then {
      action = "throw";
      error = p.fst;
      newState = p.snd;
    }
    else throw "experimental.descInterp.effects.typecheck.dispatchStrict: expected VBootInl/VBootInr at outputVal.d.tag, got '${side}'";

  # ---- Shortcut fast-path plumbing ----
  # A tagged `report` op carries its field Vals as lazy sidecars, so the
  # trampoline's per-Impure step can bypass the kernel handler: `handlerShortcut`
  # rebuilds the handler's residual Val directly (certified by
  # `typecheck-shortcut-laws.nix` + `extract.nix`), and `evalOp` reuses the cached
  # `report R` prefix. The sidecars are inert to `lower`/`conv` (host channel).
  evalH = h: fx.tc.eval.eval [ ] (H.elab h);
  vApp = fx.tc.eval.vApp;
  Extract = fx.experimental.desc-interp.extract;
  ttVal = evalH tt;
  # `passed` is bool, Sum-encoded: true → VBootInl, false → VBootInr.
  isPass = op: op._passedVal.d.tag == "VBootInl";

  mkReport = R: send_:
    reason: path: carrier: passed:
      send_ ((reportAt R reason path carrier passed) // {
        _opTag = "typecheck-report";
        _reasonVal = evalH reason;
        _pathVal = evalH path;
        _carrierVal = evalH carrier;
        _passedVal = evalH passed;
      });

  mkEvalOp = R:
    let reportPrefixVal = evalH (app EffTC.report R); in
    op:
      if (op._opTag or null) == "typecheck-report"
      then vApp (vApp (vApp (vApp reportPrefixVal op._reasonVal) op._pathVal) op._carrierVal) op._passedVal
      else fx.tc.eval.eval [ ] (H.elab op);

  # Per-handler post-step state Vals: rebuild the kernel step's output state by
  # branching on the host-precomputed `passed` and applying a precomputed branch
  # closure (the partial-evaluation residual the shortcut laws certify).
  collNewState = R:
    let consClosure = evalH (lam "p" R (p: lam "t" (collState R) (t: HI.consAtExplicit R p t))); in
    op: stateVal: if isPass op then stateVal else vApp (vApp consClosure op._carrierVal) stateVal;

  logNewState = R:
    let logConsClosure = evalH (lam "p" bool (p: lam "c" R (c: lam "t" (logState R) (t:
      HI.consAtExplicit (LogRec R) (pair p c) t)))); in
    op: stateVal: vApp (vApp (vApp logConsClosure op._passedVal) op._carrierVal) stateVal;

  firstNNewState = R:
    let failClosure = evalH (lam "carrier" R (carrier: lam "s" (firstNState R) (s:
      let coll = fst_ s; rem = snd_ s; in
      ind 0 (lam "_" nat (_: firstNState R))
        (pair coll zero)
        (lam "rp" nat (rp: lam "_ih" (firstNState R) (_:
          pair (ann (cons carrier coll) (listOf R)) rp)))
        rem))); in
    op: stateVal: if isPass op then stateVal else vApp (vApp failClosure op._carrierVal) stateVal;

  summNewState = R:
    let
      passClosure = evalH (lam "s" summState (s:
        let br = fst_ s; pf = snd_ s; pt = fst_ pf; ft = snd_ pf; in
        pair br (pair (succ pt) ft)));
      failClosure = evalH (lam "_reason" Reason (reason: lam "s" summState (s:
        let br = fst_ s; pf = snd_ s; pt = fst_ pf; ft = snd_ pf; in
        pair (bumpReason reason br) (pair pt (succ ft)))));
    in
    op: stateVal: if isPass op then vApp passClosure stateVal else vApp (vApp failClosure op._reasonVal) stateVal;

  summAssocNewState = R:
    let
      passClosure = evalH (lam "s" (summAssocState R) (s:
        let br = fst_ s; pf = snd_ s; pt = fst_ pf; ft = snd_ pf; in
        pair br (pair (succ pt) ft)));
      failClosure = evalH (lam "_reason" Reason (reason: lam "s" (summAssocState R) (s:
        let br = fst_ s; pf = snd_ s; pt = fst_ pf; ft = snd_ pf; in
        pair (insertOrIncrement (reasonName reason) br) (pair pt (succ ft)))));
    in
    op: stateVal: if isPass op then vApp passClosure stateVal else vApp (vApp failClosure op._reasonVal) stateVal;

  # The resume `Σ State Unit` output is rebuilt as a bare pair; the kernel
  # handler is bypassed when `handlerShortcut` fires (tagged report ops).
  mkAtType = handler_: newStateFn: R:
    let
      eff = app EffTC.T R;
      resp = app Resp R;
      handler = app handler_ R;
      send_ = K.send eff resp;
      newStateVal = newStateFn R;
    in
    {
      inherit eff resp handler;
      dispatch = dispatchResume;
      evalOp = mkEvalOp R;
      handlerShortcut = op: stateVal:
        if (op._opTag or null) == "typecheck-report"
        then Extract.extract (Extract.PairRaw (newStateVal op stateVal) ttVal)
        else null;
      report = mkReport R send_;
    };

  atType_collecting = mkAtType handle_collecting collNewState;
  atType_logging = mkAtType handle_logging logNewState;
  atType_firstN = mkAtType handle_firstN firstNNewState;
  atType_summarize = mkAtType handle_summarize summNewState;
  atType_summarizeAssoc = mkAtType handle_summarizeAssoc summAssocNewState;
  atType_pretty = mkAtType handle_pretty collNewState;

  # Strict ships its own dispatch (conditional throw), so it does not use
  # `mkAtType` (which always resumes). Its shortcut emits the Sum directly: a
  # pass resumes down the left summand (`Resume`), a fail surrenders the residue
  # down the right (`Abort`) for the dispatcher to throw on.
  atType_strict = R:
    let
      eff = app EffTC.T R;
      resp = app Resp R;
      handler = app handle_strict R;
      send_ = K.send eff resp;
      leftSigV = evalH strictLeft;
      rightSigV = evalH (strictRight R);
      sumDescV = Extract.sumDescValOf strictLeft (strictRight R);
    in
    {
      inherit eff resp handler;
      dispatch = dispatchStrict;
      evalOp = mkEvalOp R;
      handlerShortcut = op: stateVal:
        if (op._opTag or null) == "typecheck-report"
        then
          (if isPass op
          then Extract.extract (Extract.Resume sumDescV leftSigV rightSigV ttVal stateVal)
          else Extract.extract (Extract.Abort sumDescV leftSigV rightSigV op._carrierVal stateVal))
        else null;
      report = mkReport R send_;
    };

  rShape = ReasonDT.shapeMismatch;
  rPred = ReasonDT.predicateFailed;

in
{
  scope = {
    typecheck = api.namespace {
      description = "typecheck-policy handlers over descInterp's FreeFx kernel — EffTypeCheck datatype (one `report(reason, path, carrier, passed)` op) + six kernel-term handlers: five resume strategies (collecting/logging/firstN/summarize/pretty), each a bare `Σ State Unit` with a resume dispatch, plus `strict` (a UniRet `Sum` with a conditional-throw dispatch). The carrier `R` is opaque to every handler, so a structured diagnostic (`fx.tc.kernel.failure.DiagError`) is ferried exactly as a bare string is. Each is monomorphised via `atType_* R`.";
      doc = ''
        Pair with `experimental.desc-interp.trampoline.run`:

        ```nix
        let tc = typecheck.atType_collecting fx.tc.kernel.failure.DiagError;
        in run tc.eff tc.resp H.unit
             { inherit (tc) handler dispatch; }
             program initialState
        ```

        A program is a `bind` chain of `tc.report reason path carrier passed`
        ops; `reason` is the closed five-token enum, `path` the internalized
        structural blame site (a `Path = List Position` over the value-side
        alphabet `Field`/`Elem`/`Tag`/`Tuple`), `carrier` the opaque host
        residue, `passed` the host-precomputed decision. Every op resumes with
        `tt`; the handler folds the decision into its state and never inspects
        the carrier.
      '';

      value = {
        EffTypeCheck = api.leaf {
          value = EffTC;
          description = "EffTypeCheck : Π(R:U₀). U₀ — one constructor `report(reason:Reason, path:Path, carrier:R, passed:Bool)`.";
        };
        EffTypeCheckTy = api.leaf {
          value = EffTCTy;
          description = "Π-type of the op-identity family: `Π(R:U₀). U₀`.";
        };
        Resp = api.leaf {
          value = Resp;
          description = "Response family: every `report` op resumes with Unit (the decision rides in the op, not the resume).";
        };
        Reason = api.leaf {
          value = Reason;
          description = "Closed five-token diagnostic enum (shapeMismatch/missingField/extraField/predicateFailed/deferredPi).";
        };
        Position = api.leaf {
          value = Position;
          description = "Value-side descent position: `Field name` / `Elem idx` / `Tag name` / `Tuple idx`. The internalized core of `fx.diag.positions` for value-validation paths (`name` a strEq-comparable carrier, `idx` a Nat); rendered segment text stays host-side.";
        };
        Path = api.leaf {
          value = Path;
          description = "`Path = List Position` — the structural blame site carried by `report`, mirroring the producer's typeCheck `path`.";
        };
        ByReason = api.leaf {
          value = ByReason;
          description = "Per-reason counter tuple in constructor order (a five-Nat Σ-chain).";
        };
        bumpReason = api.leaf {
          value = bumpReason;
          description = "bumpReason r b — increment the counter for reason `r` via the Reason eliminator (no string comparison).";
        };
        reasonName = api.leaf {
          value = reasonName;
          description = "reasonName r — render the reason enum to its production `byReason` key token (shape-mismatch/missing-field/extra-field/predicate-failed/deferred-pi) via the Reason eliminator.";
        };
        insertOrIncrement = api.leaf {
          value = insertOrIncrement;
          description = "insertOrIncrement key assoc — a `listElim` fold over a `List (Σ String Nat)` byReason assoc list: a `strEq` key match bumps the entry's count in place, otherwise a new `(key, 1)` is appended.";
        };
        handle_collecting = api.leaf {
          value = handle_collecting;
          description = "Collecting handler: a fail conses the residue, a pass keeps the list. Returns `Σ (List R) Unit`.";
        };
        handle_logging = api.leaf {
          value = handle_logging;
          description = "Logging handler: every decision is recorded as `(passed, residue)`. Returns `Σ (List (Σ Bool R)) Unit`.";
        };
        handle_firstN = api.leaf {
          value = handle_firstN;
          description = "First-N handler: an O(1) down-counter records failures until it reaches zero, then drops. Returns `Σ (Σ (List R) Nat) Unit`.";
        };
        handle_summarize = api.leaf {
          value = handle_summarize;
          description = "Summarize handler: groups failures by the reason enum, tracking (passed, failed) totals. Returns `Σ (Σ ByReason (Σ Nat Nat)) Unit`.";
        };
        handle_summarizeAssoc = api.leaf {
          value = handle_summarizeAssoc;
          description = "Summarize-assoc handler: groups failures into a `List (Σ String Nat)` byReason assoc list via `insertOrIncrement` (a `listElim`+`strEq` fold), tracking (passed, failed) totals. Returns `Σ (Σ (List (Σ String Nat)) (Σ Nat Nat)) Unit`. The production-faithful `byReason` attrset shape, alongside the O(1) closed-enum variant.";
        };
        handle_pretty = api.leaf {
          value = handle_pretty;
          description = "Pretty handler: conses the host-rendered failure line (carried opaquely) on a fail. Same shape as collecting.";
        };
        handle_strict = api.leaf {
          value = handle_strict;
          description = "Strict handler: a pass resumes (left summand), a fail surrenders the residue (right summand). Returns `Sum (Σ Unit Unit) (Σ R Unit)`; the right summand drives a `throw`.";
        };
        atType_collecting = api.leaf {
          value = atType_collecting;
          description = "`atType_collecting R` — monomorphises the collecting handler and ships `{ eff; resp; handler; dispatch; report; evalOp; handlerShortcut }`. The shortcut rebuilds the resume residual directly (certified by `typecheck-shortcut-laws.nix`).";
        };
        atType_logging = api.leaf {
          value = atType_logging;
          description = "`atType_logging R` — monomorphised logging bridge record.";
        };
        atType_firstN = api.leaf {
          value = atType_firstN;
          description = "`atType_firstN R` — monomorphised first-N bridge record.";
        };
        atType_summarize = api.leaf {
          value = atType_summarize;
          description = "`atType_summarize R` — monomorphised summarize bridge record.";
        };
        atType_summarizeAssoc = api.leaf {
          value = atType_summarizeAssoc;
          description = "`atType_summarizeAssoc R` — monomorphised summarize-assoc bridge record (assoc-list byReason).";
        };
        atType_pretty = api.leaf {
          value = atType_pretty;
          description = "`atType_pretty R` — monomorphised pretty bridge record.";
        };
        atType_strict = api.leaf {
          value = atType_strict;
          description = "`atType_strict R` — monomorphises the strict handler and ships `{ eff; resp; handler; dispatch; report; evalOp; handlerShortcut }` with a conditional-throw dispatch (resume on pass, throw on fail); the shortcut emits the Sum directly (`Resume`/`Abort`).";
        };
      };
    };
  };

  tests =
    let
      ev = h: fx.tc.eval.eval [ ] (H.elab h);
      conv = a: b: fx.tc.conv.conv 0 (ev a) (ev b);
      chk = ty: h: !((H.checkHoas ty h) ? error);
      string = H.string;
      sl = H.stringLit;
      nlit = H.natLit;
      true_ = H.true_;
      false_ = H.false_;

      # The carrier is the structured kernel diagnostic; the resume handlers
      # ferry it without inspection. Distinct values differ only in opaque msg.
      F = fx.tc.kernel.failure;
      DiagError = F.DiagError;
      genDetail = fx.tc.verified.makeRecord F.GenericDetail {
        type = H.nothing H.any;
        desc = H.nothing H.any;
        value = H.nothing H.any;
        context = H.nothing string;
        index = H.nothing H.any;
        guard = H.nothing H.any;
      };
      diag = m: F.mkDiag {
        layer = F.layerOf "Generic";
        detail = F.detailOf "Generic" genDetail;
        msg = sl m;
        hint = H.nothing F.Hint;
        children = tt;
      };

      # Value-side path constructors and a couple of concrete blame sites.
      pField = n: app PositionDT.Field (sl n);
      pElem = i: app PositionDT.Elem (nlit i);
      pTag = n: app PositionDT.Tag (sl n);
      pTuple = i: app PositionDT.Tuple (nlit i);
      pathField = ann (cons (pField "user") (cons (pField "age") nil)) Path;
      pathElem = ann (cons (pField "xs") (cons (pElem 1) nil)) Path;

      # The path is eliminable, not merely carried: its eliminator maps each
      # constructor to its tag index and reads the field-name carrier back.
      posTagNat = scrut: positionElim (lam "_" Position (_: nat))
        (lam "_n" string (_: nlit 0))
        (lam "_i" nat (_: nlit 1))
        (lam "_n" string (_: nlit 2))
        (lam "_i" nat (_: nlit 3))
        scrut;
      posName = scrut: positionElim (lam "_" Position (_: string))
        (lam "n" string (n: n))
        (lam "_i" nat (_: sl ""))
        (lam "n" string (n: n))
        (lam "_i" nat (_: sl ""))
        scrut;

      runTC = st: prog: init:
        T.run st.eff st.resp unit { inherit (st) handler dispatch; } prog init;
      # Same run, but wired with the tag-keyed `evalOp` + `handlerShortcut` fast
      # path: every Impure step bypasses the kernel handler. The final state must
      # match the kernel-path run (the shortcut laws certify this per step).
      runTCShort = st: prog: init:
        T.run st.eff st.resp unit { inherit (st) handler dispatch evalOp handlerShortcut; } prog init;
      stateConv = run: expected: fx.tc.conv.conv 0 run.state (ev expected);

      mkProg = st: decisions:
        let b = K.bind st.eff st.resp unit unit; in
        lib.foldr
          (d: acc: b (st.report d.reason d.path d.carrier d.passed) (_: acc))
          (K.pure st.eff st.resp unit tt)
          decisions;

      # ---- collecting ----
      collSt = atType_collecting DiagError;
      collDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c0"; passed = true_; }
        { reason = rShape; path = pathField; carrier = diag "c1"; passed = false_; }
        { reason = rShape; path = pathElem; carrier = diag "c2"; passed = false_; }
      ];
      collRun = runTC collSt (mkProg collSt collDecisions) (ann nil (collState DiagError));
      collExpected = ann (cons (diag "c2") (cons (diag "c1") nil)) (collState DiagError);

      # ---- logging ----
      logSt = atType_logging DiagError;
      logDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c0"; passed = true_; }
        { reason = rShape; path = pathElem; carrier = diag "c1"; passed = false_; }
      ];
      logRun = runTC logSt (mkProg logSt logDecisions) (ann nil (logState DiagError));
      logExpected = ann
        (cons (pair false_ (diag "c1")) (cons (pair true_ (diag "c0")) nil))
        (logState DiagError);

      # ---- firstN (N = 2) ----
      firstNSt = atType_firstN DiagError;
      firstNDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c1"; passed = false_; }
        { reason = rShape; path = pathField; carrier = diag "c2"; passed = false_; }
        { reason = rShape; path = pathElem; carrier = diag "c3"; passed = false_; }
      ];
      firstNInit = ann (pair (ann nil (listOf DiagError)) (nlit 2)) (firstNState DiagError);
      firstNRun = runTC firstNSt (mkProg firstNSt firstNDecisions) firstNInit;
      firstNExpected = ann
        (pair (ann (cons (diag "c2") (cons (diag "c1") nil)) (listOf DiagError)) zero)
        (firstNState DiagError);

      # ---- summarize ----
      summSt = atType_summarize DiagError;
      summDecisions = [
        { reason = rShape; path = pathField; carrier = diag "x"; passed = false_; }
        { reason = rShape; path = pathField; carrier = diag "y"; passed = false_; }
        { reason = rPred; path = pathElem; carrier = diag "z"; passed = false_; }
        { reason = rShape; path = pathField; carrier = diag "w"; passed = true_; }
      ];
      summInit = ann (pair byReasonZero (pair zero zero)) summState;
      summRun = runTC summSt (mkProg summSt summDecisions) summInit;
      summExpected = ann
        (pair (mkByReason (nlit 2) zero zero (nlit 1) zero) (pair (nlit 1) (nlit 3)))
        summState;

      # ---- summarize-assoc (same stream as summarize) ----
      mkEntry = k: c: ann (pair (sl k) (nlit c)) Entry;
      summAssocSt = atType_summarizeAssoc DiagError;
      summAssocInit = ann (pair (ann nil Assoc) (pair zero zero)) (summAssocState DiagError);
      summAssocRun = runTC summAssocSt (mkProg summAssocSt summDecisions) summAssocInit;
      # shape is bumped to 2 in place, predicate-failed is appended after it.
      summAssocExpected = ann
        (pair
          (ann (cons (mkEntry "shape-mismatch" 2) (cons (mkEntry "predicate-failed" 1) nil)) Assoc)
          (pair (nlit 1) (nlit 3)))
        (summAssocState DiagError);

      # ---- pretty ----
      prettySt = atType_pretty DiagError;
      prettyDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c0"; passed = true_; }
        { reason = rShape; path = pathField; carrier = diag "c1"; passed = false_; }
      ];
      prettyRun = runTC prettySt (mkProg prettySt prettyDecisions) (ann nil (collState DiagError));
      prettyExpected = ann (cons (diag "c1") nil) (collState DiagError);

      # ---- strict ----
      strictSt = atType_strict DiagError;
      strictInit = ann tt unit;
      strictHandlerCore = ev strictSt.handler;
      strictEvalAt = passed:
        let op = reportAt DiagError rShape pathField (diag "x") passed; in
        fx.tc.eval.vApp (fx.tc.eval.vApp strictHandlerCore (ev op)) (ev strictInit);
      strictPassDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c0"; passed = true_; }
        { reason = rShape; path = pathField; carrier = diag "c1"; passed = true_; }
      ];
      strictPassRun = runTC strictSt (mkProg strictSt strictPassDecisions) strictInit;
      strictFailDecisions = [
        { reason = rShape; path = pathField; carrier = diag "c0"; passed = true_; }
        { reason = rShape; path = pathElem; carrier = diag "c1"; passed = false_; }
      ];
      strictFailRun = runTC strictSt (mkProg strictSt strictFailDecisions) strictInit;
      strictThrew = run:
        !(builtins.tryEval (builtins.seq (run.state.tag or "?") true)).success;

      # ---- production handlers (host parity reference) ----
      IntT = { name = "Int"; check = builtins.isInt; };
      mkParam = reason: value: { type = IntT; context = "Int"; inherit value reason; path = [ ]; };
      strictH = fx.effects.typecheck.policy.strict;
      collectingH = fx.effects.typecheck.policy.collecting;
      loggingH = fx.effects.typecheck.policy.logging;
      firstNH = fx.effects.typecheck.policy.firstN;
      summarizeH = fx.effects.typecheck.policy.summarize;
      prettyH = fx.effects.typecheck.policy.pretty;

      # ---- shortcut-path runs (same programs, fast path wired) ----
      collRunShort = runTCShort collSt (mkProg collSt collDecisions) (ann nil (collState DiagError));
      logRunShort = runTCShort logSt (mkProg logSt logDecisions) (ann nil (logState DiagError));
      firstNRunShort = runTCShort firstNSt (mkProg firstNSt firstNDecisions) firstNInit;
      summRunShort = runTCShort summSt (mkProg summSt summDecisions) summInit;
      summAssocRunShort = runTCShort summAssocSt (mkProg summAssocSt summDecisions) summAssocInit;
      prettyRunShort = runTCShort prettySt (mkProg prettySt prettyDecisions) (ann nil (collState DiagError));
      strictPassRunShort = runTCShort strictSt (mkProg strictSt strictPassDecisions) strictInit;
      strictFailRunShort = runTCShort strictSt (mkProg strictSt strictFailDecisions) strictInit;
    in
    {
      # Datatype + response + enum are well-formed.
      "typecheck-eff-T-wf" = { expr = chk EffTCTy EffTC.T; expected = true; };
      "typecheck-report-checks" = {
        expr = chk (app EffTC.T DiagError) (reportAt DiagError rShape pathField (diag "x") true_);
        expected = true;
      };
      "typecheck-resp-wf" = { expr = chk RespTy Resp; expected = true; };
      "typecheck-reason-wf" = { expr = chk u0 Reason; expected = true; };
      "typecheck-byreason-wf" = { expr = chk u0 ByReason; expected = true; };

      # The internalized path: type, its four value-side constructors, and a
      # path literal are well-formed; the structured carrier checks.
      "typecheck-position-wf" = { expr = chk u0 Position; expected = true; };
      "typecheck-position-field-wf" = { expr = chk Position (pField "age"); expected = true; };
      "typecheck-position-elem-wf" = { expr = chk Position (pElem 3); expected = true; };
      "typecheck-position-tag-wf" = { expr = chk Position (pTag "Some"); expected = true; };
      "typecheck-position-tuple-wf" = { expr = chk Position (pTuple 1); expected = true; };
      "typecheck-path-wf" = { expr = chk Path pathField; expected = true; };
      "typecheck-diagerror-carrier-checks" = { expr = chk DiagError (diag "c0"); expected = true; };

      # The path is eliminable: the Position eliminator computes the tag index
      # for each constructor and reads the field-name carrier back via strEq.
      "typecheck-position-tagnat-field" = { expr = conv (posTagNat (pField "x")) (nlit 0); expected = true; };
      "typecheck-position-tagnat-elem" = { expr = conv (posTagNat (pElem 3)) (nlit 1); expected = true; };
      "typecheck-position-tagnat-tag" = { expr = conv (posTagNat (pTag "X")) (nlit 2); expected = true; };
      "typecheck-position-tagnat-tuple" = { expr = conv (posTagNat (pTuple 2)) (nlit 3); expected = true; };
      "typecheck-position-name-streq" = { expr = conv (H.strEq (posName (pField "age")) (sl "age")) true_; expected = true; };
      "typecheck-position-name-streq-neg" = { expr = conv (H.strEq (posName (pField "age")) (sl "zip")) false_; expected = true; };

      # Each handler checks at its declared Π-type.
      "typecheck-collecting-handler-checks" = { expr = chk collHandleTy handle_collecting; expected = true; };
      "typecheck-logging-handler-checks" = { expr = chk logHandleTy handle_logging; expected = true; };
      "typecheck-firstn-handler-checks" = { expr = chk firstNHandleTy handle_firstN; expected = true; };
      "typecheck-summarize-handler-checks" = { expr = chk summHandleTy handle_summarize; expected = true; };
      "typecheck-pretty-handler-checks" = { expr = chk prettyHandleTy handle_pretty; expected = true; };
      "typecheck-strict-handler-checks" = { expr = chk mkStrictHandleTy handle_strict; expected = true; };
      "typecheck-summarize-assoc-handler-checks" = { expr = chk summAssocHandleTy handle_summarizeAssoc; expected = true; };

      # Strict's handler picks the resume summand on a pass and the throw
      # summand on a fail.
      "typecheck-strict-pass-is-inl" = { expr = (strictEvalAt true_).d.tag; expected = "VBootInl"; };
      "typecheck-strict-fail-is-inr" = { expr = (strictEvalAt false_).d.tag; expected = "VBootInr"; };

      # bumpReason selects the right counter and accumulates.
      "typecheck-bump-shape" = {
        expr = conv (bumpReason rShape byReasonZero) (mkByReason (nlit 1) zero zero zero zero);
        expected = true;
      };
      "typecheck-bump-pred" = {
        expr = conv (bumpReason rPred byReasonZero) (mkByReason zero zero zero (nlit 1) zero);
        expected = true;
      };
      "typecheck-bump-accumulates" = {
        expr = conv (bumpReason rShape (bumpReason rShape byReasonZero)) (mkByReason (nlit 2) zero zero zero zero);
        expected = true;
      };

      # The assoc-list summarize variant: shapes are well-formed, the reason
      # enum renders to its production token, and the listElim+strEq insert /
      # increment reduces (append a new key, bump an existing one in place).
      "typecheck-entry-wf" = { expr = chk u0 Entry; expected = true; };
      "typecheck-assoc-wf" = { expr = chk u0 Assoc; expected = true; };
      "typecheck-reasonname-shape" = { expr = conv (reasonName rShape) (sl "shape-mismatch"); expected = true; };
      "typecheck-reasonname-missing" = { expr = conv (reasonName ReasonDT.missingField) (sl "missing-field"); expected = true; };
      "typecheck-reasonname-extra" = { expr = conv (reasonName ReasonDT.extraField) (sl "extra-field"); expected = true; };
      "typecheck-reasonname-pred" = { expr = conv (reasonName rPred) (sl "predicate-failed"); expected = true; };
      "typecheck-reasonname-deferred" = { expr = conv (reasonName ReasonDT.deferredPi) (sl "deferred-pi"); expected = true; };
      "typecheck-insert-empty" = {
        expr = conv (insertOrIncrement (sl "a") (ann nil Assoc)) (ann (cons (mkEntry "a" 1) nil) Assoc);
        expected = true;
      };
      "typecheck-insert-append" = {
        expr = conv (insertOrIncrement (sl "a") (ann (cons (mkEntry "b" 2) nil) Assoc))
          (ann (cons (mkEntry "b" 2) (cons (mkEntry "a" 1) nil)) Assoc);
        expected = true;
      };
      "typecheck-insert-increment-head" = {
        expr = conv (insertOrIncrement (sl "a") (ann (cons (mkEntry "a" 3) nil) Assoc))
          (ann (cons (mkEntry "a" 4) nil) Assoc);
        expected = true;
      };
      "typecheck-insert-increment-tail" = {
        expr = conv (insertOrIncrement (sl "a") (ann (cons (mkEntry "b" 1) (cons (mkEntry "a" 2) nil)) Assoc))
          (ann (cons (mkEntry "b" 1) (cons (mkEntry "a" 3) nil)) Assoc);
        expected = true;
      };

      # Driven through the trampoline, each handler's final state matches the
      # explicit fold result.
      "typecheck-collecting-run" = { expr = stateConv collRun collExpected; expected = true; };
      "typecheck-logging-run" = { expr = stateConv logRun logExpected; expected = true; };
      "typecheck-firstn-run" = { expr = stateConv firstNRun firstNExpected; expected = true; };
      "typecheck-summarize-run" = { expr = stateConv summRun summExpected; expected = true; };
      "typecheck-summarize-assoc-run" = { expr = stateConv summAssocRun summAssocExpected; expected = true; };
      "typecheck-pretty-run" = { expr = stateConv prettyRun prettyExpected; expected = true; };

      # An all-pass stream resumes to completion (state untouched); a stream
      # with a fail makes the trampoline throw.
      "typecheck-strict-run-allpass" = { expr = stateConv strictPassRun strictInit; expected = true; };
      "typecheck-strict-run-throws-on-fail" = { expr = strictThrew strictFailRun; expected = true; };

      # Shortcut-path parity: with `evalOp` + `handlerShortcut` wired, every
      # Impure step bypasses the kernel handler, yet the final state is identical
      # to the kernel-path run — the per-step shortcut laws hold end-to-end.
      "typecheck-collecting-run-shortcut" = { expr = stateConv collRunShort collExpected; expected = true; };
      "typecheck-logging-run-shortcut" = { expr = stateConv logRunShort logExpected; expected = true; };
      "typecheck-firstn-run-shortcut" = { expr = stateConv firstNRunShort firstNExpected; expected = true; };
      "typecheck-summarize-run-shortcut" = { expr = stateConv summRunShort summExpected; expected = true; };
      "typecheck-summarize-assoc-run-shortcut" = { expr = stateConv summAssocRunShort summAssocExpected; expected = true; };
      "typecheck-pretty-run-shortcut" = { expr = stateConv prettyRunShort prettyExpected; expected = true; };
      "typecheck-strict-run-allpass-shortcut" = { expr = stateConv strictPassRunShort strictInit; expected = true; };
      "typecheck-strict-run-throws-on-fail-shortcut" = { expr = strictThrew strictFailRunShort; expected = true; };

      # Host parity: the kernel model agrees with the production handler over the
      # same decision stream (up to list reversal).
      "typecheck-parity-collecting" = {
        expr =
          let
            s1 = (collectingH.typeCheck { param = mkParam "shape-mismatch" 7; state = [ ]; }).state;
            s2 = (collectingH.typeCheck { param = mkParam "shape-mismatch" "x"; state = s1; }).state;
            s3 = (collectingH.typeCheck { param = mkParam "shape-mismatch" "y"; state = s2; }).state;
          in
          builtins.length s3;
        expected = 2;
      };
      "typecheck-parity-logging" = {
        expr = builtins.map (p: (loggingH.typeCheck { param = mkParam "shape-mismatch" p; state = [ ]; }).resume) [ 7 "x" ];
        expected = [ true false ];
      };
      "typecheck-parity-firstn" = {
        expr =
          let
            h = (firstNH 2).typeCheck;
            s0 = { collected = [ ]; aborted = false; };
            s1 = (h { param = mkParam "shape-mismatch" "a"; state = s0; }).state;
            s2 = (h { param = mkParam "shape-mismatch" "b"; state = s1; }).state;
            s3 = (h { param = mkParam "shape-mismatch" "c"; state = s2; }).state;
          in
          { len = builtins.length s3.collected; aborted = s3.aborted; };
        expected = { len = 2; aborted = true; };
      };
      "typecheck-parity-summarize" = {
        expr =
          let
            h = summarizeH.typeCheck;
            s0 = { byReason = { }; passed = 0; failed = 0; };
            s1 = (h { param = mkParam "shape-mismatch" "x"; state = s0; }).state;
            s2 = (h { param = mkParam "shape-mismatch" "y"; state = s1; }).state;
            s3 = (h { param = mkParam "predicate-failed" "z"; state = s2; }).state;
            s4 = (h { param = mkParam "shape-mismatch" 7; state = s3; }).state;
          in
          { inherit (s4) byReason passed failed; };
        expected = { byReason = { shape-mismatch = 2; predicate-failed = 1; }; passed = 1; failed = 3; };
      };
      "typecheck-parity-pretty" = {
        expr = builtins.length ((prettyH { }).typeCheck { param = mkParam "shape-mismatch" "x"; state = [ ]; }).state;
        expected = 1;
      };

      # The production strict handler resumes on a pass and throws on a fail.
      "typecheck-parity-strict-pass" = {
        expr = (strictH.typeCheck { param = mkParam "shape-mismatch" 7; state = null; }).resume;
        expected = true;
      };
      "typecheck-parity-strict-throws" = {
        expr = (builtins.tryEval (strictH.typeCheck { param = mkParam "shape-mismatch" "x"; state = null; }).resume).success;
        expected = false;
      };
    };
}
