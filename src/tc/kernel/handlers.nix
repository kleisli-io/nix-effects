# The six typecheck-policy handlers as kernel step terms.
#
# Each handler folds a stream of membership decisions into an accumulated state.
# A decision arrives as a host-known boolean `passed` together with an opaque
# diagnostic residue `Rec` (a host-rendered token the kernel never inspects —
# there is no kernel string introspection, so a String carrier is opaque by
# construction). Each handler's step is a closed kernel term
#
#   step : ... -> Σ State payload
#
# whose reduction is the handler's state transition. The kernel decides the
# transition by ι (on the eliminator) and β (on the bound payload); a `conv`
# against the expected pair is the reduction proof.
#
#   strict     : Π rec. Σ Unit Rec                 carry the residue; the host
#                                                  throws on the false decision
#   collecting : Π passed rec s. Σ (List Rec) Unit pass keeps s, fail conses rec
#   logging    : Π passed rec s. Σ (List LogRec) Unit  always conses (passed,rec)
#   firstN     : Π passed rec s rem. Σ (List Rec) Nat  down-counter `rem`: fail
#                                                  records and decrements until
#                                                  rem = 0, then drops
#   summarize  : Π passed reason br pf. Σ Assoc (Σ Nat Nat)  group by reason
#                                                  (Assoc = List (Σ String Nat))
#   pretty     : Π line s. Σ (List Rec) Unit       cons the host-rendered line
#
# These mirror the host handlers (the membership-decision arm sends `typeCheck`
# only on a false decision; the producer pre-computes the boolean). `firstN`
# carries a down-counter `remaining` rather than re-measuring the collected
# list each step, so the abort test is O(1); the abort flag is recovered as
# `remaining = 0`.
#
# `reason` is the closed five-token diagnostic enum; `reasonName` renders it to
# its production key token, and `summarize` groups failures into a
# `List (Σ String Nat)` assoc list keyed by those tokens, comparing keys with
# `strEq`. The host renders the diagnostic line; the kernel groups by the
# rendered reason token.
{ fx, api, ... }:

let
  H = fx.tc.hoas;

  app = H.app;
  lam = H.lam;
  forall = H.forall;
  ann = H.ann;
  con = H.con;
  nat = H.nat;
  zero = H.zero;
  succ = H.succ;
  bool = H.bool;
  unit = H.unit;
  tt = H.tt;
  string = H.string;
  listOf = H.listOf;
  cons = H.cons;
  nil = H.nil;
  sigma = H.sigma;
  pair = H.pair;
  fst_ = H.fst_;
  snd_ = H.snd_;
  boolElim = H.boolElim;
  ind = H.ind;
  listElim = H.listElim;
  strEq = H.strEq;
  sl = H.stringLit;
  nlit = H.natLit;
  HI = H._internal._indexed;

  # The opaque host-rendered diagnostic residue. The kernel stores and threads
  # it without inspection.
  Rec = string;

  # A logging entry pairs the decision outcome with the residue, so a trace
  # records passes and failures alike.
  LogRec = sigma "_" bool (_: Rec);

  # ---- Result shapes (Σ State payload) ----
  collResultTy = sigma "_" (listOf Rec) (_: unit);
  logResultTy = sigma "_" (listOf LogRec) (_: unit);
  firstNResultTy = sigma "_" (listOf Rec) (_: nat);
  strictResultTy = sigma "_" unit (_: Rec);
  prettyResultTy = sigma "_" (listOf Rec) (_: unit);

  # ---- Step Π-types ----
  collStepTy = forall "_" bool (_: forall "_" Rec (_: forall "_" (listOf Rec) (_: collResultTy)));
  logStepTy = forall "_" bool (_: forall "_" Rec (_: forall "_" (listOf LogRec) (_: logResultTy)));
  firstNStepTy = forall "_" bool (_: forall "_" Rec (_: forall "_" (listOf Rec) (_: forall "_" nat (_: firstNResultTy))));
  strictStepTy = forall "_" Rec (_: strictResultTy);
  prettyStepTy = forall "_" Rec (_: forall "_" (listOf Rec) (_: prettyResultTy));

  # collecting: a passing decision leaves the accumulator untouched; a failing
  # one conses the residue. The payload is Unit (the handler always resumes).
  collectingStep = ann
    (lam "passed" bool (passed: lam "rec" Rec (rv: lam "s" (listOf Rec) (s:
      pair
        (boolElim 0 (lam "_" bool (_: listOf Rec)) s (cons rv s) passed)
        tt))))
    collStepTy;

  # logging: every decision is recorded with its outcome, so the step always
  # conses; the outcome rides in the entry.
  loggingStep = ann
    (lam "passed" bool (passed: lam "rec" Rec (rv: lam "s" (listOf LogRec) (s:
      pair (cons (pair passed rv) s) tt))))
    logStepTy;

  # firstN: a down-counter. A pass leaves state and counter alone. A fail at
  # `rem = suc rp` records the residue and decrements to `rp`; a fail at
  # `rem = 0` drops the residue and holds at 0 (the abort state). The counter
  # case is `ind` on `rem`, so the abort test is O(1) per step. The recorded
  # list in the suc branch is annotated because the `ind` step body is
  # synthesized, not checked, so a bare cons would carry no element type.
  firstNStep = ann
    (lam "passed" bool (passed: lam "rec" Rec (rv: lam "s" (listOf Rec) (s: lam "rem" nat (rem:
      boolElim 0 (lam "_" bool (_: firstNResultTy))
        (pair s rem)
        (ind 0 (lam "_" nat (_: firstNResultTy))
          (pair s zero)
          (lam "rp" nat (rp: lam "_ih" firstNResultTy (_: pair (ann (cons rv s) (listOf Rec)) rp)))
          rem)
        passed)))))
    firstNStepTy;

  # strict: carry the residue; the host raises on a false decision, so the
  # kernel state is Unit and the step is a constant pair.
  strictStep = ann (lam "rec" Rec (rv: pair tt rv)) strictStepTy;

  # pretty: the host renders the failure line; the kernel conses it opaquely.
  prettyStep = ann
    (lam "line" Rec (line: lam "s" (listOf Rec) (s: pair (cons line s) tt)))
    prettyStepTy;

  # ---- summarize: group by reason into an assoc list ----
  #
  # The five diagnostic reasons are a closed enum, so `Reason` is a datatype and
  # `reasonName` renders each to its production `byReason` key token. Grouping
  # accumulates an assoc list `List (Σ String Nat)` keyed by those tokens — the
  # `assocListToAttrs` shape the production handler builds, matched
  # order-insensitively. Keys are compared by `strEq`.
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

  # reasonName r: render the reason constructor to its production key token.
  reasonName = reasonElim (lam "_" Reason (_: string))
    (sl "shape-mismatch")
    (sl "missing-field")
    (sl "extra-field")
    (sl "predicate-failed")
    (sl "deferred-pi");

  Entry = sigma "_" string (_: nat);
  Assoc = listOf Entry;

  # insertOrIncrement key assoc: one structural fold. Reaching `onNil` means no
  # key matched, so a fresh `(key, 1)` is emitted. On a `strEq` head match the
  # head count is bumped and the original tail is kept (the speculative append
  # in `ih` is discarded); on a miss the head is kept and `ih` carries the rest.
  # The branch bodies sit in a synthesized `listElim` step, so the conses are
  # explicit (a bare cons would leave the element type unresolved).
  insertOrIncrement = key: assoc:
    listElim 0 Entry
      (lam "_" Assoc (_: Assoc))
      (HI.consAtExplicit H.levelZero Entry (pair key (nlit 1)) (HI.nilAtExplicit H.levelZero Entry))
      (lam "h" Entry (h:
        lam "t" Assoc (t:
          lam "ih" Assoc (ih:
            boolElim 0 (lam "_" bool (_: Assoc))
              (HI.consAtExplicit H.levelZero Entry (pair (fst_ h) (succ (snd_ h))) t)
              (HI.consAtExplicit H.levelZero Entry h ih)
              (strEq (fst_ h) key)))))
      assoc;

  # (passed, failed) totals ride alongside the assoc list.
  pfTy = sigma "_" nat (_: nat);
  summResultTy = sigma "_" Assoc (_: pfTy);
  summStepTy = forall "_" bool (_: forall "_" Reason (_: forall "_" Assoc (_: forall "_" pfTy (_: summResultTy))));

  # summarize: a pass bumps the passed total; a fail inserts/increments the
  # reason's assoc entry and bumps the failed total. Per-failure data is dropped,
  # so state is bounded by the distinct reasons plus two totals.
  summarizeStep = ann
    (lam "passed" bool (passed: lam "reason" Reason (reason: lam "br" Assoc (b: lam "pf" pfTy (pf:
      boolElim 0 (lam "_" bool (_: summResultTy))
        (pair b (pair (succ (fst_ pf)) (snd_ pf)))
        (pair (insertOrIncrement (reasonName reason) b) (pair (fst_ pf) (succ (snd_ pf))))
        passed)))))
    summStepTy;
in
{
  scope = {
    handlers = api.namespace {
      description = "fx.tc.kernel.handlers: the six typecheck-policy handlers (strict/collecting/logging/firstN/summarize/pretty) as closed kernel step terms folding a stream of membership decisions into accumulated state. A decision is a host-known boolean `passed` plus an opaque host-rendered residue Rec; each step is `... -> Σ State payload` whose reduction is the state transition. firstN carries an O(1) down-counter; summarize renders the reason enum to its production key token via `reasonName` and groups failures into a `List (Σ String Nat)` assoc list via `insertOrIncrement` (a `listElim`+`strEq` fold). Exports the step terms, their result shapes, and the Reason/assoc grouping vocabulary.";
      value = {
        inherit
          Rec LogRec
          collResultTy logResultTy firstNResultTy strictResultTy prettyResultTy summResultTy
          collectingStep loggingStep firstNStep strictStep prettyStep summarizeStep
          Reason Entry Assoc reasonName insertOrIncrement;
        reasonShapeMismatch = ReasonDT.shapeMismatch;
        reasonMissingField = ReasonDT.missingField;
        reasonExtraField = ReasonDT.extraField;
        reasonPredicateFailed = ReasonDT.predicateFailed;
        reasonDeferredPi = ReasonDT.deferredPi;
      };
    };
  };

  tests =
    let
      ev = h: fx.tc.eval.eval [ ] (H.elab h);
      conv = a: b: fx.tc.conv.conv 0 (ev a) (ev b);
      chk = ty: h: !((H.checkHoas ty h) ? error);
      true_ = H.true_;
      false_ = H.false_;

      r0 = H.stringLit "e0";
      r1 = H.stringLit "e1";
      noRecs = ann nil (listOf Rec);
      oneRec = ann (cons r0 nil) (listOf Rec);
      twoRecs = ann (cons r1 (cons r0 nil)) (listOf Rec);
      noLog = ann nil (listOf LogRec);
      pf0 = pair zero zero;
      emptyAssoc = ann nil Assoc;
      mkEntry = k: c: ann (pair (sl k) (nlit c)) Entry;

      rShape = ReasonDT.shapeMismatch;
      rPred = ReasonDT.predicateFailed;
      rDeferred = ReasonDT.deferredPi;

      # Production handlers — the host parity reference.
      IntT = { name = "Int"; check = builtins.isInt; };
      mkParam = reason: value: { type = IntT; context = "Int"; inherit value reason; path = [ ]; };
      collecting = fx.effects.typecheck.policy.collecting;
      logging = fx.effects.typecheck.policy.logging;
      firstNH = fx.effects.typecheck.policy.firstN;
      summarizeH = fx.effects.typecheck.policy.summarize;
      prettyH = fx.effects.typecheck.policy.pretty;
    in
    {
      # Result shapes are well-formed U_0 types.
      "handlers-coll-result-wf" = { expr = chk (H.u 0) collResultTy; expected = true; };
      "handlers-log-result-wf" = { expr = chk (H.u 0) logResultTy; expected = true; };
      "handlers-firstn-result-wf" = { expr = chk (H.u 0) firstNResultTy; expected = true; };
      "handlers-strict-result-wf" = { expr = chk (H.u 0) strictResultTy; expected = true; };
      "handlers-pretty-result-wf" = { expr = chk (H.u 0) prettyResultTy; expected = true; };
      "handlers-reason-wf" = { expr = chk (H.u 0) Reason; expected = true; };
      "handlers-entry-wf" = { expr = chk (H.u 0) Entry; expected = true; };
      "handlers-assoc-wf" = { expr = chk (H.u 0) Assoc; expected = true; };
      "handlers-summ-result-wf" = { expr = chk (H.u 0) summResultTy; expected = true; };

      # Each step term checks at its declared Π-type.
      "handlers-collecting-step-checks" = { expr = chk collStepTy collectingStep; expected = true; };
      "handlers-logging-step-checks" = { expr = chk logStepTy loggingStep; expected = true; };
      "handlers-firstn-step-checks" = { expr = chk firstNStepTy firstNStep; expected = true; };
      "handlers-strict-step-checks" = { expr = chk strictStepTy strictStep; expected = true; };
      "handlers-pretty-step-checks" = { expr = chk prettyStepTy prettyStep; expected = true; };
      "handlers-summarize-step-checks" = { expr = chk summStepTy summarizeStep; expected = true; };

      # collecting: a pass leaves the accumulator; a fail conses the residue.
      "handlers-collecting-pass" = {
        expr = conv (app (app (app collectingStep true_) r0) noRecs) (pair noRecs tt);
        expected = true;
      };
      "handlers-collecting-fail" = {
        expr = conv (app (app (app collectingStep false_) r0) noRecs) (pair oneRec tt);
        expected = true;
      };

      # logging: every decision is recorded with its outcome.
      "handlers-logging-pass" = {
        expr = conv (app (app (app loggingStep true_) r0) noLog) (pair (ann (cons (pair true_ r0) nil) (listOf LogRec)) tt);
        expected = true;
      };
      "handlers-logging-fail" = {
        expr = conv (app (app (app loggingStep false_) r0) noLog) (pair (ann (cons (pair false_ r0) nil) (listOf LogRec)) tt);
        expected = true;
      };

      # firstN: a pass holds; a fail at rem>0 records and decrements; a fail at
      # rem=0 drops and holds (abort).
      "handlers-firstn-pass" = {
        expr = conv (app (app (app (app firstNStep true_) r1) oneRec) (nlit 2)) (pair oneRec (nlit 2));
        expected = true;
      };
      "handlers-firstn-fail-records-and-decrements" = {
        expr = conv (app (app (app (app firstNStep false_) r1) oneRec) (nlit 2)) (pair twoRecs (nlit 1));
        expected = true;
      };
      "handlers-firstn-fail-at-zero-drops" = {
        expr = conv (app (app (app (app firstNStep false_) r1) oneRec) zero) (pair oneRec zero);
        expected = true;
      };

      # strict / pretty.
      "handlers-strict-carries-residue" = {
        expr = conv (app strictStep r0) (pair tt r0);
        expected = true;
      };
      "handlers-pretty-conses-line" = {
        expr = conv (app (app prettyStep r0) noRecs) (pair oneRec tt);
        expected = true;
      };

      # reasonName renders each reason constructor to its production key token.
      "handlers-reasonname-shape" = {
        expr = conv (reasonName rShape) (sl "shape-mismatch");
        expected = true;
      };
      "handlers-reasonname-pred" = {
        expr = conv (reasonName rPred) (sl "predicate-failed");
        expected = true;
      };
      "handlers-reasonname-deferred" = {
        expr = conv (reasonName rDeferred) (sl "deferred-pi");
        expected = true;
      };

      # insertOrIncrement: a fresh key appends `(key, 1)`; a present key bumps its
      # count in place; a distinct key is appended after the kept head.
      "handlers-insert-empty" = {
        expr = conv (insertOrIncrement (sl "shape-mismatch") emptyAssoc)
          (ann (cons (mkEntry "shape-mismatch" 1) nil) Assoc);
        expected = true;
      };
      "handlers-insert-increment-head" = {
        expr = conv (insertOrIncrement (sl "shape-mismatch") (ann (cons (mkEntry "shape-mismatch" 1) nil) Assoc))
          (ann (cons (mkEntry "shape-mismatch" 2) nil) Assoc);
        expected = true;
      };
      "handlers-insert-append-distinct" = {
        expr = conv (insertOrIncrement (sl "predicate-failed") (ann (cons (mkEntry "shape-mismatch" 1) nil) Assoc))
          (ann (cons (mkEntry "shape-mismatch" 1) (cons (mkEntry "predicate-failed" 1) nil)) Assoc);
        expected = true;
      };

      # summarize: a pass bumps the passed total; a fail inserts the reason's
      # entry and bumps the failed total.
      "handlers-summarize-pass" = {
        expr = conv (app (app (app (app summarizeStep true_) rShape) emptyAssoc) pf0) (pair emptyAssoc (pair (nlit 1) zero));
        expected = true;
      };
      "handlers-summarize-fail-shape" = {
        expr = conv (app (app (app (app summarizeStep false_) rShape) emptyAssoc) pf0)
          (pair (ann (cons (mkEntry "shape-mismatch" 1) nil) Assoc) (pair zero (nlit 1)));
        expected = true;
      };
      "handlers-summarize-fail-pred" = {
        expr = conv (app (app (app (app summarizeStep false_) rPred) emptyAssoc) pf0)
          (pair (ann (cons (mkEntry "predicate-failed" 1) nil) Assoc) (pair zero (nlit 1)));
        expected = true;
      };

      # Host parity: the kernel model agrees with the production handler's
      # observable state transition on the same decision stream.
      "handlers-parity-collecting-fail-conses-one" = {
        expr = builtins.length (collecting.typeCheck { param = mkParam "shape-mismatch" "x"; state = [ ]; }).state;
        expected = 1;
      };
      "handlers-parity-collecting-pass-keeps" = {
        expr = (collecting.typeCheck { param = mkParam "shape-mismatch" 7; state = [ ]; }).state;
        expected = [ ];
      };
      "handlers-parity-logging-records-both" = {
        expr = builtins.map (p: (logging.typeCheck { param = mkParam "shape-mismatch" p; state = [ ]; }).resume) [ 7 "x" ];
        expected = [ true false ];
      };
      "handlers-parity-firstn-caps-and-aborts" = {
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
      "handlers-parity-summarize-groups-by-reason" = {
        expr =
          let
            h = summarizeH.typeCheck;
            s0 = { byReason = { }; passed = 0; failed = 0; };
            s1 = (h { param = mkParam "shape-mismatch" "x"; state = s0; }).state;
            s2 = (h { param = mkParam "shape-mismatch" "y"; state = s1; }).state;
            s3 = (h { param = mkParam "predicate-failed" "z"; state = s2; }).state;
          in
          s3.byReason;
        expected = { shape-mismatch = 2; predicate-failed = 1; };
      };
      "handlers-parity-pretty-one-line-per-failure" = {
        expr = builtins.length ((prettyH { }).typeCheck { param = mkParam "shape-mismatch" "x"; state = [ ]; }).state;
        expected = 1;
      };
    };
}
