# Kernel-checked one-shot lemmas certifying that each typecheck handler on the
# canonical `report` op reduces to the bare residual its shortcut emitter targets.
# Every lemma discharges by `H.refl` — kernel conv decides the reduction:
#
#   ι on `EffTypeCheck.elim` selects the (single) `report` constructor branch
#   β binds the four fields (reason, path, carrier, passed) + the prior state
#   ι on the step's `boolElim` at a CONCRETE `passed` selects the pass/fail arm
#
# The resume strategies reduce to a bare `H.pair newState tt` (the `extract.PairRaw`
# residual); `strict` reduces to a `Sum` inl/inr (the `extract.Resume`/`Abort`
# residual). For a CONCRETE `passed`, the RHS is the emitter's explicit output
# shape, so emitter conv + these H.refl lemmas chain into:
#
#   vApp (vApp handlerCore opVal) stateVal ≡_Val <shortcut Val>
#
# at every canonical report. Notes on the stuck-eliminator structure:
#
#   * collecting / logging / pretty: clean bare-output resume; pass + fail.
#   * firstN: the fail branch's down-counter `ind` is stuck on a bound `remaining`,
#     so the fail law splits into `remaining = suc rp` (record + decrement) and
#     `remaining = zero` (drop + hold); pass needs no `ind` (it returns the state).
#   * summarize / summarize-assoc: the fail branch's `bumpReason` /
#     `insertOrIncrement` stays neutral on a bound reason, so a SYMBOLIC reason
#     suffices — the same neutral term appears on both sides and refl holds. One
#     fail lemma certifies the shape for every reason token.
#   * strict: pass = inl (resume), fail = inr (throw channel).
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  TC = fx.experimental.desc-interp.effects.typecheck;

  u0 = H.u 0;
  app = H.app;
  lam = H.lam;
  forall = H.forall;
  sigma = H.sigma;
  pair = H.pair;
  ann = H.ann;
  cons = H.cons;
  nat = H.nat;
  unit = H.unit;
  tt = H.tt;
  listOf = H.listOf;
  succ = H.succ;
  zero = H.zero;
  string = H.string;
  eq = H.eq;
  refl = H.refl;

  # Real surfaced effect pieces — the lemmas certify THESE handlers.
  Reason = TC.Reason;
  Path = TC.Path;
  EffTC = TC.EffTypeCheck;
  bumpReason = TC.bumpReason;
  reasonName = TC.reasonName;
  insertOrIncrement = TC.insertOrIncrement;
  handle_collecting = TC.handle_collecting;
  handle_logging = TC.handle_logging;
  handle_firstN = TC.handle_firstN;
  handle_summarize = TC.handle_summarize;
  handle_summarizeAssoc = TC.handle_summarizeAssoc;
  handle_pretty = TC.handle_pretty;
  handle_strict = TC.handle_strict;

  reportAt = R: reason: path: carrier: passed:
    app (app (app (app (app EffTC.report R) reason) path) carrier) passed;

  # State shapes — reconstructed structurally (List/Σ are conv-structural, so
  # these match the handler's own shapes by construction).
  collState = R: listOf R;
  LogRec = R: sigma "_" H.bool (_: R);
  logState = R: listOf (LogRec R);
  firstNState = R: sigma "_" (listOf R) (_: nat);
  ByReason = sigma "_" nat (_: sigma "_" nat (_: sigma "_" nat (_: sigma "_" nat (_: nat))));
  pfTy = sigma "_" nat (_: nat);
  summState = sigma "_" ByReason (_: pfTy);
  Entry = sigma "_" string (_: nat);
  Assoc = listOf Entry;
  summAssocState = R: sigma "_" Assoc (_: pfTy);
  strictLeft = sigma "_r" unit (_: unit);
  strictRight = R: sigma "_a" R (_: unit);
  strictSum = R: H.sum strictLeft (strictRight R);

  handleAt = h: R: op: s: app (app (app h R) op) s;
  outTy = stateOf: R: sigma "_st" (stateOf R) (_: unit);

  # ---- resume telescope: R/reason/path/carrier/s, proof = 5 lams + refl ----
  resumeLemmaTy = handler: stateOf: passed: rhsOf:
    forall "R" u0 (R: forall "reason" Reason (reason: forall "path" Path (path:
      forall "carrier" R (carrier: forall "s" (stateOf R) (s:
        eq (outTy stateOf R)
          (handleAt handler R (reportAt R reason path carrier passed) s)
          (rhsOf R reason path carrier s))))));
  resumeLemmaPrf = stateOf:
    lam "R" u0 (R: lam "reason" Reason (_: lam "path" Path (_:
      lam "carrier" R (_: lam "s" (stateOf R) (_: refl)))));

  # ---- collecting ----
  # Fail conses via `HI.consAtExplicit`: in the eq-RHS checking position a bare
  # `cons` leaves its element type unresolved (the boolElim-checked branch in the
  # handler can use a bare cons because its motive supplies the type).
  collectingPassTy = resumeLemmaTy handle_collecting collState H.true_
    (R: _reason: _path: _carrier: s: pair s tt);
  collectingFailTy = resumeLemmaTy handle_collecting collState H.false_
    (R: _reason: _path: carrier: s: pair (HI.consAtExplicit R carrier s) tt);
  collectingPassPrf = resumeLemmaPrf collState;
  collectingFailPrf = resumeLemmaPrf collState;

  # ---- logging (always cons; the outcome rides in the record) ----
  loggingPassTy = resumeLemmaTy handle_logging logState H.true_
    (R: _reason: _path: carrier: s: pair (HI.consAtExplicit (LogRec R) (pair H.true_ carrier) s) tt);
  loggingFailTy = resumeLemmaTy handle_logging logState H.false_
    (R: _reason: _path: carrier: s: pair (HI.consAtExplicit (LogRec R) (pair H.false_ carrier) s) tt);
  loggingPassPrf = resumeLemmaPrf logState;
  loggingFailPrf = resumeLemmaPrf logState;

  # ---- pretty (same shape as collecting; the host-rendered line rides in R) ----
  prettyPassTy = resumeLemmaTy handle_pretty collState H.true_
    (R: _reason: _path: _carrier: s: pair s tt);
  prettyFailTy = resumeLemmaTy handle_pretty collState H.false_
    (R: _reason: _path: carrier: s: pair (HI.consAtExplicit R carrier s) tt);
  prettyPassPrf = resumeLemmaPrf collState;
  prettyFailPrf = resumeLemmaPrf collState;

  # ---- firstN (down-counter) ----
  # Pass returns the state (no `ind`). Fail's `ind` is stuck on the bound
  # remaining count, so it splits: `suc rp` records + decrements, `zero` drops.
  firstNPassTy = resumeLemmaTy handle_firstN firstNState H.true_
    (R: _reason: _path: _carrier: s: pair s tt);
  firstNPassPrf = resumeLemmaPrf firstNState;

  firstNFailSucTy =
    forall "R" u0 (R: forall "reason" Reason (reason: forall "path" Path (path:
      forall "carrier" R (carrier: forall "coll" (listOf R) (coll: forall "rp" nat (rp:
        eq (outTy firstNState R)
          (handleAt handle_firstN R (reportAt R reason path carrier H.false_) (pair coll (succ rp)))
          (pair (pair (ann (cons carrier coll) (listOf R)) rp) tt)))))));
  firstNFailSucPrf =
    lam "R" u0 (R: lam "reason" Reason (_: lam "path" Path (_:
      lam "carrier" R (_: lam "coll" (listOf R) (_: lam "rp" nat (_: refl))))));

  firstNFailZeroTy =
    forall "R" u0 (R: forall "reason" Reason (reason: forall "path" Path (path:
      forall "carrier" R (carrier: forall "coll" (listOf R) (coll:
        eq (outTy firstNState R)
          (handleAt handle_firstN R (reportAt R reason path carrier H.false_) (pair coll zero))
          (pair (pair coll zero) tt))))));
  firstNFailZeroPrf =
    lam "R" u0 (R: lam "reason" Reason (_: lam "path" Path (_:
      lam "carrier" R (_: lam "coll" (listOf R) (_: refl)))));

  # ---- summarize telescope: R/reason/path/carrier/br/pt/ft, state = (br,(pt,ft)) ----
  summLemmaTy = handler: stateOf: brTy: passed: rhsOf:
    forall "R" u0 (R: forall "reason" Reason (reason: forall "path" Path (path:
      forall "carrier" R (carrier: forall "br" brTy (br: forall "pt" nat (pt: forall "ft" nat (ft:
        eq (outTy stateOf R)
          (handleAt handler R (reportAt R reason path carrier passed) (pair br (pair pt ft)))
          (rhsOf reason br pt ft))))))));
  summLemmaPrf = brTy:
    lam "R" u0 (R: lam "reason" Reason (_: lam "path" Path (_:
      lam "carrier" R (_: lam "br" brTy (_: lam "pt" nat (_: lam "ft" nat (_: refl)))))));

  # ---- summarize (closed-enum byReason) ----
  summarizePassTy = summLemmaTy handle_summarize (_R: summState) ByReason H.true_
    (_reason: br: pt: ft: pair (pair br (pair (succ pt) ft)) tt);
  summarizeFailTy = summLemmaTy handle_summarize (_R: summState) ByReason H.false_
    (reason: br: pt: ft: pair (pair (bumpReason reason br) (pair pt (succ ft))) tt);
  summarizePassPrf = summLemmaPrf ByReason;
  summarizeFailPrf = summLemmaPrf ByReason;

  # ---- summarize-assoc (assoc-list byReason) ----
  summarizeAssocPassTy = summLemmaTy handle_summarizeAssoc summAssocState Assoc H.true_
    (_reason: br: pt: ft: pair (pair br (pair (succ pt) ft)) tt);
  summarizeAssocFailTy = summLemmaTy handle_summarizeAssoc summAssocState Assoc H.false_
    (reason: br: pt: ft: pair (pair (insertOrIncrement (reasonName reason) br) (pair pt (succ ft))) tt);
  summarizeAssocPassPrf = summLemmaPrf Assoc;
  summarizeAssocFailPrf = summLemmaPrf Assoc;

  # ---- strict (conditional throw via a Sum) ----
  strictLemmaTy = passed: rhsOf:
    forall "R" u0 (R: forall "reason" Reason (reason: forall "path" Path (path:
      forall "carrier" R (carrier: forall "s" unit (s:
        eq (strictSum R)
          (handleAt handle_strict R (reportAt R reason path carrier passed) s)
          (rhsOf R carrier s))))));
  strictLemmaPrf =
    lam "R" u0 (R: lam "reason" Reason (_: lam "path" Path (_:
      lam "carrier" R (_: lam "s" unit (_: refl)))));

  strictPassTy = strictLemmaTy H.true_
    (R: _carrier: s: HI.inlAtExplicit H.levelZero strictLeft (strictRight R) (pair tt s));
  strictFailTy = strictLemmaTy H.false_
    (R: carrier: s: HI.inrAtExplicit H.levelZero strictLeft (strictRight R) (pair carrier s));
  strictPassPrf = strictLemmaPrf;
  strictFailPrf = strictLemmaPrf;

  # Surface each lemma as a (type, proof) leaf pair with a well-formedness test
  # on the type and a checks-against test on the proof.
  lemmaLeaves = name: ty: prf: tyDesc: prfDesc: {
    "${name}Ty" = api.leaf {
      value = ty;
      description = tyDesc;
      tests."${name}Ty-well-formed" = {
        expr = !((H.inferHoas ty) ? error);
        expected = true;
      };
    };
    "${name}" = api.leaf {
      value = prf;
      description = prfDesc;
      tests."${name}-checks-against-${name}Ty" = {
        expr = !((H.checkHoas ty prf) ? error);
        expected = true;
      };
    };
  };

in
{
  scope = {
    "typecheck-shortcut-laws" = api.namespace {
      description = "fx.experimental.desc-interp.effects.typecheck-shortcut-laws: kernel-checked one-shot lemmas certifying each typecheck handler on the canonical `report` op reduces to its shortcut residual (`pair newState tt` for the resume strategies; a `Sum` inl/inr for strict). Each discharges by `H.refl` — ι on EffTypeCheck.elim fires the single `report` branch, β binds the four fields + state, and the step's `boolElim` at a concrete `passed` selects the arm. RHSes match the `extract.PairRaw`/`Resume`/`Abort` emitter outputs, anchoring per-strategy shortcut soundness at the kernel layer. firstN-fail splits on the stuck down-counter (`suc`/`zero`); summarize/summarize-assoc fail keep the reason symbolic (one lemma per variant covers all tokens).";

      value =
        (lemmaLeaves "collectingPass" collectingPassTy collectingPassPrf
          "Π-type of collecting-pass: `Π R reason path carrier. Π s:List R. handle_collecting R (report reason path carrier true) s ≡ H.pair s tt`."
          "Proof of collecting-pass: 5 lams + H.refl. A pass keeps the accumulator.")
        // (lemmaLeaves "collectingFail" collectingFailTy collectingFailPrf
          "Π-type of collecting-fail: `… (report … false) s ≡ H.pair (cons carrier s) tt`."
          "Proof of collecting-fail: 5 lams + H.refl. A fail conses the residue (RHS via consAtExplicit).")
        // (lemmaLeaves "loggingPass" loggingPassTy loggingPassPrf
          "Π-type of logging-pass: `… handle_logging R (report … true) s ≡ H.pair (cons (pair true carrier) s) tt`."
          "Proof of logging-pass: 5 lams + H.refl. Every decision is recorded; the outcome rides in the record.")
        // (lemmaLeaves "loggingFail" loggingFailTy loggingFailPrf
          "Π-type of logging-fail: `… (report … false) s ≡ H.pair (cons (pair false carrier) s) tt`."
          "Proof of logging-fail: 5 lams + H.refl.")
        // (lemmaLeaves "prettyPass" prettyPassTy prettyPassPrf
          "Π-type of pretty-pass: same shape as collecting-pass (`H.pair s tt`)."
          "Proof of pretty-pass: 5 lams + H.refl.")
        // (lemmaLeaves "prettyFail" prettyFailTy prettyFailPrf
          "Π-type of pretty-fail: `… (report … false) s ≡ H.pair (cons carrier s) tt` (the host-rendered line rides in carrier)."
          "Proof of pretty-fail: 5 lams + H.refl.")
        // (lemmaLeaves "firstNPass" firstNPassTy firstNPassPrf
          "Π-type of firstN-pass: `… handle_firstN R (report … true) s ≡ H.pair s tt` (no `ind`; the state is returned)."
          "Proof of firstN-pass: 5 lams + H.refl.")
        // (lemmaLeaves "firstNFailSuc" firstNFailSucTy firstNFailSucPrf
          "Π-type of firstN-fail at `remaining = suc rp`: `… (report … false) (pair coll (suc rp)) ≡ H.pair (pair (cons carrier coll) rp) tt` — record and decrement."
          "Proof of firstN-fail-suc: 6 lams + H.refl. The recorded list is annotated (the `ind` step body is synthesized, so a bare cons carries no element type).")
        // (lemmaLeaves "firstNFailZero" firstNFailZeroTy firstNFailZeroPrf
          "Π-type of firstN-fail at `remaining = zero`: `… (report … false) (pair coll zero) ≡ H.pair (pair coll zero) tt` — drop and hold (the abort state)."
          "Proof of firstN-fail-zero: 5 lams + H.refl.")
        // (lemmaLeaves "summarizePass" summarizePassTy summarizePassPrf
          "Π-type of summarize-pass: `… handle_summarize R (report … true) (pair br (pair pt ft)) ≡ H.pair (pair br (pair (suc pt) ft)) tt` — bump the passed total."
          "Proof of summarize-pass: 7 lams + H.refl.")
        // (lemmaLeaves "summarizeFail" summarizeFailTy summarizeFailPrf
          "Π-type of summarize-fail (reason symbolic): `… (report reason … false) (pair br (pair pt ft)) ≡ H.pair (pair (bumpReason reason br) (pair pt (suc ft))) tt`. `bumpReason reason br` stays neutral on both sides, so one lemma covers every reason."
          "Proof of summarize-fail: 7 lams + H.refl.")
        // (lemmaLeaves "summarizeAssocPass" summarizeAssocPassTy summarizeAssocPassPrf
          "Π-type of summarize-assoc-pass: `… handle_summarizeAssoc R (report … true) (pair br (pair pt ft)) ≡ H.pair (pair br (pair (suc pt) ft)) tt`."
          "Proof of summarize-assoc-pass: 7 lams + H.refl.")
        // (lemmaLeaves "summarizeAssocFail" summarizeAssocFailTy summarizeAssocFailPrf
          "Π-type of summarize-assoc-fail (reason symbolic): `… (report reason … false) (pair br (pair pt ft)) ≡ H.pair (pair (insertOrIncrement (reasonName reason) br) (pair pt (suc ft))) tt`."
          "Proof of summarize-assoc-fail: 7 lams + H.refl.")
        // (lemmaLeaves "strictPass" strictPassTy strictPassPrf
          "Π-type of strict-pass: `… handle_strict R (report … true) s ≡ inl strictLeft (strictRight R) (pair tt s)` — resume down the left summand."
          "Proof of strict-pass: 5 lams + H.refl.")
        // (lemmaLeaves "strictFail" strictFailTy strictFailPrf
          "Π-type of strict-fail: `… (report … false) s ≡ inr strictLeft (strictRight R) (pair carrier s)` — surrender the residue down the right summand (the throw channel)."
          "Proof of strict-fail: 5 lams + H.refl.");
    };
  };
}
