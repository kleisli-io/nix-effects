# Generic typed walker — one polymorphic monadic fold over the HOAS type
# algebra, parameterised by `Algebra A`.
#
#   unitAlg (A=Unit): validation via collecting handler — emits typeCheck
#                     effects on failure, constructs nothing.
#   hoasAlg (A=Hoas): elaboration via strict handler — failures throw,
#                     `.value` is the elaborated HOAS tree.
#
# New interpretations (size, depth, decidable bridges) add algebras
# against the unchanged walker.
#
# Public surface:
#   deriveCheck    : ty → path → value → Computation Unit
#   deriveElaborate: ty → path → value → Computation Hoas
#   checkWithGuard : ty → path → value → Computation Unit
#
# Fold owns: shape inspection, `_htag` dispatch, effect emissions, path
# threading, `builtins.foldl'` iteration (avoids the construction-time
# stack growth of `bind (pure x) k`), and the dependent-Σ snd-type
# derivation via a strict-handler hoasAlg walk on fst.
#
# Algebra owns: per-shape success-case construction at carrier A.
# `walkFields` is delegated (unitAlg discards the carrier; hoasAlg builds
# the constructor app spine); both resolve dependent field types through
# `D.fieldType field prev`.
#
# Failure `reason` tags routed by `fx.effects.typecheck.*`:
#   shape-mismatch    — primitive leaf disagreement, non-attrset where a
#                       constructor record was expected, or unrecognised
#                       `_con`/`_tag`.
#   missing-field     — constructor field absent.
#   extra-field       — record carries undeclared fields.
#   predicate-failed  — refinement guard rejected after shape passed.
#   deferred-pi       — reserved for proof-bearing kernel terms.
{ self, fx, api, ... }:

let
  inherit (fx.kernel) pure bind send;

  G = fx.tc.generic;
  P = G.path;
  Pos = fx.diag.positions;
  D = G.datatype;
  H = fx.tc.hoas;
  HI = H._internal._indexed;
  E = fx.tc.eval;
  # Val→HOAS rebuild for the carrier of a normalized El. Referenced lazily;
  # `fx.tc.elaborate` bridges back through `deriveElaborate`, so the cycle is
  # broken by Nix thunk laziness (both sides are leaf values, not module-eval).
  reifyType = fx.tc.elaborate.reifyType;

  # Host-stack fuel for the walker. Each structural level consumes one unit;
  # native recursion runs up to `nativeWalkBudget` levels per trampoline
  # segment, then `descend` defers re-entry via the `deriveBounce` effect so
  # host stack stays O(1) per segment regardless of value depth.
  nativeWalkBudget = 512;

  # Emit a typeCheck effect, then continue with the algebra's failure
  # carrier. Strict throws before bind runs; collecting resumes.
  emit = alg: ty: path: reason: context: value:
    bind
      (send "typeCheck" {
        type = ty;
        inherit context value path reason;
      })
      (_: pure alg.onFailure);

  tryDatatypeInfo = hoasTy:
    builtins.tryEval (D.datatypeInfo hoasTy);

  # Shim HOAS types into the `{ name; check }` shape handlers expect.
  # `check = _: false` since every emission is a failure. For μ/app-form
  # datatypes use the datatype's name (e.g. `MetaBuilderFinalizedTool`)
  # instead of the bare `"mu"` htag.
  wrapType = ty:
    if builtins.isAttrs ty && ty ? name && ty ? check
    then ty
    else
      let
        tag = ty._htag or null;
        muName =
          if tag == "mu" || tag == "app" then
            let infoTry = tryDatatypeInfo ty; in
            if infoTry.success then infoTry.value.name or null else null
          else null;
        name =
          if muName != null then muName
          else if tag != null then tag
          else ty.name or "<unknown>";
      in
      { inherit name; check = _: false; };

  # Native-Nix primitive registry — leaf bridge from Nix values to the
  # kernel. Each row binds the validation predicate, the diagnostic
  # expectation string, and the HOAS literal constructor for a primitive
  # `htag`. Adding a primitive = one row.
  primitives = {
    bool       = { pred = builtins.isBool;                                          expectation = "bool";                                            lit = v: if v then H.true_ else H.false_; };
    nat        = { pred = v: builtins.isInt v && v >= 0;                            expectation = "non-negative integer";                            lit = H.natLit; };
    unit       = { pred = v: v == null;                                             expectation = "null (unit)";                                     lit = _: H.tt; };
    string     = { pred = builtins.isString;                                        expectation = "string";                                          lit = H.stringLit; };
    int        = { pred = builtins.isInt;                                           expectation = "integer";                                         lit = H.intLit; };
    float      = { pred = builtins.isFloat;                                         expectation = "float";                                           lit = H.floatLit; };
    attrs      = { pred = builtins.isAttrs;                                         expectation = "attrset";                                         lit = _: H.attrsLit; };
    path       = { pred = builtins.isPath;                                          expectation = "path";                                            lit = _: H.pathLit; };
    derivation = { pred = v: builtins.isAttrs v && (v.type or null) == "derivation"; expectation = "derivation (attrset with type=\"derivation\")"; lit = _: H.derivationLit; };
    function   = { pred = builtins.isFunction;                                      expectation = "function";                                        lit = _: H.fnLit; };
    any        = { pred = _: true;                                                  expectation = "<native>";                                        lit = _: H.anyLit; };
    U          = { pred = v: builtins.isAttrs v && v ? _kernel;                     expectation = "Type with _kernel";                               lit = v: v._kernel; };
  };

  nativePred        = htag: primitives.${htag}.pred or null;
  nativeExpectation = htag: primitives.${htag}.expectation or "<native>";

  # List-shape: two constructors, nullary then `[data, recAt]`. Surface
  # form is a Nix list rather than a constructor record.
  isListShape = info:
    let cs = info.constructors; in
    builtins.length cs == 2
    && (builtins.head cs).fields == [ ]
    && (
      let
        cons = builtins.elemAt cs 1;
        ks = map (f: f.kind) cons.fields;
      in
      ks == [ "data" "recAt" ]
    );

  listElemType = info:
    let
      cons = builtins.elemAt info.constructors 1;
      elemField = builtins.head cons.fields;
    in
    elemField.type;

  # Resolve a constructor for an attrset. Dispatch: (1) `_con`/`_tag`
  # present → exact lookup, null on miss; (2) no tag, cardinality 1 →
  # η-rule, sole constructor applies; (3) no tag, cardinality > 1 → null.
  # An explicit unknown tag is never shadowed by the η-rule.
  resolveCon = info: value:
    if !builtins.isAttrs value then null
    else
      let
        cs = info.constructors;
        n = builtins.length cs;
        tag = value._con or value._tag or null;
        findByName = name:
          let
            go = i:
              if i >= n then null
              else
                let c = builtins.elemAt cs i;
                in if c.name == name then c else go (i + 1);
          in
          go 0;
      in
      if tag != null then findByName tag
      else if n == 1 then builtins.head cs
      else null;

  elaborateHoasStrict = ty: path: value:
    builtins.tryEval (
      (fx.trampoline.handle
        {
          handlers = fx.effects.typecheck.strict;
          state = null;
        }
        (deriveGo hoasAlg nativeWalkBudget ty path value)).value
    );

  # Elaborate fst via a strict-handler hoasAlg walk; tryEval for failure.
  # walkSigma needs fst's HOAS regardless of the outer algebra's carrier.
  elaborateFstHoas = elaborateHoasStrict;

  # Π: accept functions and `_hoasImpl`-bearing records; reject anything
  # else as shape-mismatch — the walker can't inspect a function's body.
  walkPi = alg: ty: path: value:
    if (builtins.isAttrs value && value ? _hoasImpl) || builtins.isFunction value
    then pure (alg.onPi ty value)
    else
      emit alg (wrapType ty) path "shape-mismatch"
        "expected function, got ${builtins.typeOf value}"
        value;

  # Σ: walk fst, then derive snd's type by substituting fst's HOAS into
  # `ty.body`. fst HOAS comes from a strict trampoline even when
  # validating — snd needs it dependently. Blame uses
  # `Pos.SigmaFst`/`Pos.SigmaSnd`, matching SourceMap and Sigma's
  # surface `verify=` so paths stay invariant under encoding.
  walkSigma = alg: fuel: ty: path: value:
    if !(builtins.isAttrs value && value ? fst && value ? snd) then
      emit alg (wrapType ty) path "shape-mismatch"
        "expected { fst; snd; }, got ${builtins.typeOf value}"
        value
    else
      let
        fstPath = P.extend path Pos.SigmaFst;
        sndPath = P.extend path Pos.SigmaSnd;
      in
      bind (descend alg fuel ty.fst fstPath value.fst) (fstA:
        let fstHoasTry = elaborateFstHoas ty.fst fstPath value.fst; in
        if !fstHoasTry.success then pure alg.onFailure
        else
          let
            sndTyTry = builtins.tryEval (ty.body fstHoasTry.value);
          in
          if !sndTyTry.success then pure alg.onFailure
          else
            bind (descend alg fuel sndTyTry.value sndPath value.snd) (sndA:
              pure (alg.onSigma ty fstA sndA)));

  # Decidable-`Certified` membership `El t` (`= app ElFn t`, ktype.nix:74)
  # embeds in compounds with head `app`, which `datatypeInfo` cannot unfold.
  # Normalize-before-dispatch: `El t` WHNF-reduces to `VSigma` (Σ x:β(t).
  # P(decide t x)). Walk it structurally — the carrier `β(t)` is reified back
  # to HOAS for the fst descent, and the codomain is decided by instantiating
  # the kernel closure at the concrete carrier value: `P true ↝ VUnit`
  # (accept), `P false ↝ VEmpty` (reject). This is the normalizing membership
  # decision the syntactic walker otherwise lacks; the kernel `decide`-fold runs
  # exactly once per value, at the closure instantiation.
  #
  # `tyOrig` (the original `El t`) is a closed, re-elaboratable term and is what
  # `onSigma` annotates the witness pair with — the reified sigma is NOT
  # re-elaboratable (its codomain splice resolves only under concrete args, not
  # the symbolic binder a re-`elab` would supply), so it is used for structure
  # only, never embedded in an emitted term.
  walkEl = alg: fuel: tyOrig: elV: path: value:
    if !(builtins.isAttrs value && value ? fst && value ? snd) then
      emit alg (wrapType tyOrig) path "shape-mismatch"
        "expected { fst; snd; }, got ${builtins.typeOf value}"
        value
    else
      let
        carrierHoas = reifyType elV.fst;
        fstPath = P.extend path Pos.SigmaFst;
        sndPath = P.extend path Pos.SigmaSnd;
        # The witness pair's type annotation. `El` is a closed type whose
        # lowering is value-independent, so carry its pre-lowered `Tm` through
        # `embedTm` — `elaborate` returns it verbatim (O(1), no per-value
        # re-lowering), and it stays a `Tm` so the desc-* CHECK rules retarget it
        # in tandem with the pair payload (a pre-evaluated Val spliced via
        # `litVal` cannot be retargeted and conv-mismatches). The lowered `Tm` is
        # read from the per-type `_elTm` cache when present (computed once at
        # `Certified` construction), else lowered here.
        witnessTy = H.embedTm (tyOrig._elTm or (H.elab tyOrig));
      in
      bind (descend alg fuel carrierHoas fstPath value.fst) (fstA:
        let fstHoasTry = elaborateFstHoas carrierHoas fstPath value.fst; in
        if !fstHoasTry.success then pure alg.onFailure
        else
          let
            sndTyV = E.forceVal
              (E.instantiate elV.closure (E.eval [ ] (H.elab fstHoasTry.value)));
            sndTag = sndTyV.tag or null;
          in
          if sndTag == "VUnit" then
            bind (descend alg fuel H.unit sndPath value.snd) (sndA:
              pure (alg.onSigma witnessTy fstA sndA))
          else if sndTag == "VEmpty" then
            emit alg (wrapType tyOrig) path "predicate-failed"
              "value does not satisfy the certified predicate"
              value
          else
          # Genuinely open (neutral) predicate — no decision; fail closed.
            emit alg (wrapType tyOrig) path "predicate-failed"
              "certified predicate did not reduce to a decision"
              value);

  walkMaybe = alg: fuel: ty: path: value:
    if value == null then pure (alg.onMaybeNull ty)
    else
      bind (descend alg fuel ty.inner path value) (innerA:
        pure (alg.onMaybeJust ty innerA));

  # Thunk — deepSeq-safe carrier. Check the carrier shape only; never
  # invoke `_force` (forcing defeats the deepSeq shielding). Inner-type
  # validation happens post-forget at the consumer.
  walkThunk = alg: ty: path: value:
    if !(builtins.isAttrs value
      && value ? _force
      && builtins.isFunction value._force) then
      emit alg (wrapType ty) path "shape-mismatch"
        "expected Thunk carrier with _force closure, got ${builtins.typeOf value}"
        value
    else
      pure (alg.onThunk ty value);

  # Variant — primitive kernel sum. Dispatch on `value._tag`, descend
  # into the matching branch's type with `Pos.Tag tag`. No synthetic
  # `Pos.Field "value"` appears in any path; constructor tags at the
  # surface preserve Wadler-Findler blame-label source-invariance.
  walkVariant = alg: fuel: ty: path: value:
    if !(builtins.isAttrs value && value ? _tag && value ? value) then
      emit alg (wrapType ty) path "shape-mismatch"
        "expected { _tag; value; }, got ${builtins.typeOf value}"
        value
    else
      let
        tag = value._tag;
        branches = ty.branches or [ ];
        n = builtins.length branches;
        findBranch = i:
          if i >= n then null
          else
            let b = builtins.elemAt branches i;
            in if b.tag == tag then b else findBranch (i + 1);
        branch = findBranch 0;
      in
      if branch == null then
        emit alg (wrapType ty) path "shape-mismatch"
          "unknown variant tag '${toString tag}'"
          value
      else
        let branchPath = P.extend path (Pos.Tag tag); in
        bind (descend alg fuel branch.type branchPath value.value)
          (innerA: pure (alg.onVariant ty tag innerA));

  # Walk a list at element type. Accumulator is algebra-specific
  # (`alg.listAcc`): null for unitAlg, a cons-chain continuation for
  # hoasAlg. `foldl'` (not recursive `go`) avoids the construction-time
  # N-deep stack from eager `bind (pure x) k`.
  walkElems = alg: fuel: ty: path: elemTy: value:
    if !builtins.isList value then
      emit alg (wrapType ty) path "shape-mismatch"
        "expected list, got ${builtins.typeOf value}"
        value
    else
      let
        n = builtins.length value;
        indices = builtins.genList (i: i) n;
        step = acc: i:
          let
            v = builtins.elemAt value i;
            childPath = P.extend path (Pos.Elem i);
          in
          bind acc (accB:
            bind (descend alg fuel elemTy childPath v) (elemA:
              pure (alg.listAcc.step ty elemTy accB elemA)));
      in
      bind (builtins.foldl' step (pure (alg.listAcc.init ty elemTy)) indices)
        (accB: pure (alg.listAcc.finish ty elemTy accB));

  walkPrim = alg: htag: ty: path: value:
    let pred = nativePred htag; in
    if pred == null then
      emit alg (wrapType ty) path "shape-mismatch"
        "unknown native type tag '${toString htag}'"
        value
    else if pred value then
      pure (alg.onPrim htag ty value)
    else
      emit alg (wrapType ty) path "shape-mismatch"
        "expected ${nativeExpectation htag}, got ${builtins.typeOf value}"
        value;

  # μ/app datatypes. List-shape → walkElems. Attrset values dispatch on
  # `_con`/`_tag` via `resolveCon`, then through `alg.walkFields`.
  # μ-encoded Bool (`[[],[]]`) and Nat (`[[],["recAt"]]`) route back
  # through walkPrim.
  walkDatatype = alg: fuel: ty: path: value:
    let infoTry = tryDatatypeInfo ty; in
    if !infoTry.success then
    # An `app`/`mu` head with no datatype metadata is not necessarily a dead
    # end: a decidable-`Certified` field embeds `El t`, which `datatypeInfo`
    # cannot unfold but which WHNF-reduces to a `VSigma`. Normalize and, on a
    # Σ head, walk it via `walkEl`; otherwise fail closed as before. The WHNF is
    # read from a `_elWhnf` cache on the type node when present (computed once
    # per distinct `El` type at construction), else evaluated here — so a
    # collection of N values pays the `El` elaboration once, not N times.
      let
        cached = ty._elWhnf or null;
        whnfTry =
          if cached != null then { success = true; value = cached; }
          else builtins.tryEval (E.forceVal (E.eval [ ] (H.elab ty)));
      in
      if whnfTry.success && (whnfTry.value.tag or null) == "VSigma"
      then walkEl alg fuel ty whnfTry.value path value
      else
        emit alg (wrapType ty) path "shape-mismatch"
          "type carries no datatype metadata"
          value
    else
      let
        info = infoTry.value;
        cs = info.constructors;
        sigs = map (c: map (f: f.kind) c.fields) cs;
        isBoolSig = sigs == [ [ ] [ ] ];
        isNatSig = sigs == [ [ ] [ "recAt" ] ];
      in
      if isListShape info then
        walkElems alg fuel ty path (listElemType info) value
      else if builtins.isAttrs value then
        let con = resolveCon info value; in
        if con == null then
          let
            tag = value._con or value._tag or null;
            reason =
              if tag != null
              then "unknown constructor '${toString tag}'"
              else "missing _con/_tag for multi-constructor type";
          in
          emit alg (wrapType ty) path "shape-mismatch" reason value
        else
          let
            multiCon = builtins.length cs > 1;
            walkPath =
              if multiCon
              then P.extend path (Pos.Tag con.name)
              else path;
          in
          alg.walkFields fuel ty walkPath info con value
      else if isBoolSig then walkPrim alg "bool" ty path value
      else if isNatSig then walkPrim alg "nat" ty path value
      else
        emit alg (wrapType ty) path "shape-mismatch"
          "expected attrset (constructor signatures = ${builtins.toJSON sigs})"
          value;

  # Bounce gate for structural re-entry. Within `fuel`, recurse natively (the
  # fast shallow path). At zero, defer re-entry via the `deriveBounce` effect:
  # the handler forces the deferred sub-walk and the trampoline splices it as a
  # fresh segment (resumeCompOrValue), so host stack stays O(1) per segment
  # while DFS effect order and the bottom-up carrier are preserved.
  descend = alg: fuel: ty: path: value:
    if fuel <= 0
    then send "deriveBounce" { run = _: deriveGo alg nativeWalkBudget ty path value; }
    else deriveGo alg (fuel - 1) ty path value;

  # Polymorphic fold. Routes on `ty._htag`, threading `alg` and the
  # host-stack `fuel` through every recursive call (via `descend`).
  # unitAlg → validation; hoasAlg → elaboration.
  deriveGo = alg: fuel: ty: path: value:
    let t = ty._htag or null; in
    if t == "pi" then walkPi alg ty path value
    else if t == "sigma" then walkSigma alg fuel ty path value
    else if t == "maybe" then walkMaybe alg fuel ty path value
    else if t == "thunk" then walkThunk alg ty path value
    else if t == "variant" then walkVariant alg fuel ty path value
    else if t == "mu" || t == "app" then walkDatatype alg fuel ty path value
    else if nativePred t != null then walkPrim alg t ty path value
    else
    # Fallback: some construction paths attach `_dtypeMeta` without
    # `_htag`; try datatypeInfo before emitting unknown-tag.
      let infoTry = tryDatatypeInfo ty; in
      if infoTry.success then walkDatatype alg fuel ty path value
      else
        emit alg (wrapType ty) path "shape-mismatch"
          "unknown type tag '${toString t}'"
          value;

  # unitAlg's walkFields. Validates each field and threads passing
  # data/dataD as HOAS in `prev` for dependent `typeFn` resolution —
  # same record hoasAlg sees.
  unitWalkFields = fuel: ty: path: info: con: value:
    let
      unknownType = { _htag = "<unknown>"; };
      fieldTyAt = f: prev:
        if f.kind == "recAt"
        then
          let t = D.fieldType f prev; in
          if builtins.isAttrs t && (t._htag or null) == "mu"
          then t // { _dtypeMeta = info; }
          else t
        else D.fieldType f prev;
      fieldComp = prev: f:
        let
          lbl = f.name;
          childPath = P.extend path (Pos.Field lbl);
          hasIt = builtins.hasAttr lbl value;
          fv = if hasIt then builtins.getAttr lbl value else null;
          tyTry = builtins.tryEval (fieldTyAt f prev);
          tyAtF = if tyTry.success then tyTry.value else unknownType;
        in
        if !hasIt then
          bind
            (send "typeCheck" {
              type = wrapType tyAtF;
              context = lbl;
              value = null;
              path = childPath;
              reason = "missing-field";
            })
            (_: pure prev)
        else if !tyTry.success then
          bind
            (send "typeCheck" {
              type = wrapType unknownType;
              context = "could not resolve type for field `${lbl}`";
              value = fv;
              path = childPath;
              reason = "shape-mismatch";
            })
            (_: pure prev)
        else if f.kind == "recAt" then
          bind (descend unitAlg fuel tyAtF childPath fv) (_: pure prev)
        else if f.kind == "data" || f.kind == "dataD" then
          bind (descend unitAlg fuel tyAtF childPath fv)
            (_:
              let fieldHoasTry = elaborateHoasStrict tyAtF childPath fv; in
              pure (
                if fieldHoasTry.success
                then prev // { ${lbl} = fieldHoasTry.value; }
                else prev
              ))
        else
          bind (descend unitAlg fuel tyAtF childPath fv) (_: pure prev);
      step = acc: f: bind acc (prev: fieldComp prev f);
    in
    bind (builtins.foldl' step (pure { }) con.fields) (_: pure null);

  # hoasAlg's walkFields. Threads `prev` through `D.fieldType` for
  # dependent fields and accumulates an `H.app` chain rooted at
  # `con.ctor`.
  hoasWalkFields = fuel: ty: path: info: con: value:
    let
      fields = con.fields or [ ];
      openExtras = info.openExtras or false;
      fieldNames = map (f: f.name) fields;
      extraFields =
        if openExtras then [ ]
        else
          builtins.filter
            (n: n != "_con" && n != "_tag" && !(builtins.elem n fieldNames))
            (builtins.attrNames value);
      # recAt fields recurse on the parent type, decorated with
      # `_dtypeMeta` so a bare `mu` keeps its info on the inner descent.
      fieldTyAt = f: prev:
        if f.kind == "recAt"
        then
          let t = D.fieldType f prev; in
          if builtins.isAttrs t && (t._htag or null) == "mu"
          then t // { _dtypeMeta = info; }
          else t
        else D.fieldType f prev;
      go = remaining: prev: acc:
        if remaining == [ ] then pure acc
        else
          let
            f = builtins.head remaining;
            rest = builtins.tail remaining;
            childPath = P.extend path (Pos.Field f.name);
            tyAtF = fieldTyAt f prev;
            hasIt = builtins.hasAttr f.name value;
            fv = if hasIt then builtins.getAttr f.name value else null;
          in
          if !hasIt then
          # Strict aborts here; collecting accumulates and produces a
          # partial HOAS chain (see `hoasAlg.onFailure` for the read).
            bind
              (send "typeCheck" {
                type = wrapType (f.type or { _htag = "<unknown>"; });
                context = f.name;
                value = null;
                path = childPath;
                reason = "missing-field";
              })
              (_: go rest prev acc)
          else
            bind (descend hoasAlg fuel tyAtF childPath fv) (fieldHoas:
              let
                prev' =
                  if f.kind == "data" || f.kind == "dataD"
                  then prev // { ${f.name} = fieldHoas; }
                  else prev;
                acc' = H.app acc fieldHoas;
              in
              go rest prev' acc');
    in
    if extraFields != [ ]
    then
      bind
        (send "typeCheck" {
          type = wrapType ty;
          context = "extra fields: ${builtins.concatStringsSep ", " extraFields}";
          inherit value path;
          reason = "extra-field";
        })
        (_: go fields { } con.ctor)
    else go fields { } con.ctor;

  unitAlg = {
    onPi = _: _: null;
    onMaybeNull = _: null;
    onMaybeJust = _: _: null;
    onThunk = _: _: null;
    onSigma = _: _: _: null;
    onVariant = _: _: _: null;
    onPrim = _: _: _: null;
    fromHoas = _: null;
    onFailure = null;
    listAcc = {
      init = _: _: null;
      step = _: _: _: _: null;
      finish = _: _: _: null;
    };
    walkFields = unitWalkFields;
  };

  hoasAlg = {
    onPi = ty: v:
      if builtins.isAttrs v && v ? _hoasImpl then v._hoasImpl
      else if builtins.isFunction v then H.opaqueLam v ty
      else throw "hoasAlg.onPi: walker shape-check should have rejected this";
    onMaybeNull = ty: H.nothing ty.inner;
    onMaybeJust = ty: inner: H.just ty.inner inner;
    # Thunk's kernel type is `Record { _tag : string; _force : function_ }`
    # (inner type is HOAS-surface only). Apply the record's `mk` to
    # `stringLit` + `fnLit`; `_force` is opaque so never invoked.
    onThunk = ty: v:
      let
        info = D.datatypeInfo ty._unfold;
        ctor = (builtins.head info.constructors).ctor;
      in
      H.app (H.app ctor (H.stringLit (v._tag or "Thunk"))) H.fnLit;
    onSigma = ty: fstA: sndA: H.ann (H.pair fstA sndA) ty;
    onVariant = ty: tag: inner: H.variantInject ty tag inner;
    onPrim = htag: _ty: v:
      let p = primitives.${htag} or null; in
      if p == null then throw "hoasAlg.onPrim: unknown htag '${toString htag}'"
      else p.lit v;
    fromHoas = h: h;
    # Unreachable under strict. Collecting + hoasAlg is incoherent —
    # fire loudly when forced rather than propagate garbage HOAS.
    onFailure = throw ''
      hoasAlg.onFailure forced: deriveElaborate ran under the collecting
      handler, which produces meaningless HOAS for failed subtrees. Use
      runStrict for elaboration, or unitAlg to collect errors without
      elaborating.
    '';
    listAcc = {
      # CPS accumulator: O(1) per step, O(N) finalise. Direct snoc would
      # be O(N²) because Nix `++` copies the left operand.
      init = _: _: (rest: rest);
      step = _: elemTy: acc: elem: (rest: acc (HI.consAtExplicit elemTy elem rest));
      finish = _: elemTy: acc: acc (HI.nilAtExplicit elemTy);
    };
    walkFields = hoasWalkFields;
  };

  deriveCheckGo = ty: path: value: deriveGo unitAlg nativeWalkBudget ty path value;
  deriveElaborateGo = ty: path: value: deriveGo hoasAlg nativeWalkBudget ty path value;

  # Refinement: shape first, then predicate (Σ-type sequencing — the
  # predicate's domain is shape-passing values). `mkType` composes the
  # guard into `.check` (= `kernelCheck ∧ guard`); we reconstruct the
  # guard's verdict by comparing the two. `_kernelSufficient = false`
  # flags refined types; non-refined fast-path through.
  checkWithGuardGo = ty: path: value:
    let
      kernelTy = ty._kernel or null;
      hasGuard = !(ty._kernelSufficient or true);
      kernelOk = ty.kernelCheck or (_: true);
      fullOk = ty.check or (_: true);
    in
    if kernelTy == null then deriveCheckGo ty path value
    else
      bind (deriveCheckGo kernelTy path value) (_:
        if !hasGuard then pure null
        else if !(kernelOk value) then pure null
        else if fullOk value then pure null
        else
          send "typeCheck" {
            type = wrapType ty;
            context = "<predicate>";
            inherit value;
            inherit path;
            reason = "predicate-failed";
          });

  runCollecting = comp:
    (fx.trampoline.handle
      {
        handlers = fx.effects.typecheck.collecting;
        state = [ ];
      }
      comp).state;

  runStrict = comp:
    (fx.trampoline.handle
      {
        handlers = fx.effects.typecheck.strict;
        state = null;
      }
      comp).value;
in
{
  scope = {
    deriveCheck = api.leaf {
      value = deriveCheckGo;
      description = "deriveCheck: canonical typed walker over the HOAS algebra threading `unitAlg` — emits `fx.effects.typecheck` failures with structured `reason` (shape-mismatch, missing-field, extra-field, predicate-failed, deferred-pi) and `path` (a `fx.diag.positions` chain).";
      signature = "deriveCheck : Type -> Path -> Value -> Computation Null";
    };
    deriveElaborate = api.leaf {
      value = deriveElaborateGo;
      description = "deriveElaborate: canonical typed walker over the HOAS algebra threading `hoasAlg` — reconstructs the corresponding HOAS term at every successfully-checked node; shares path threading and dispatch with `deriveCheck`.";
      signature = "deriveElaborate : Type -> Path -> Value -> Computation Hoas";
    };
    checkWithGuard = api.leaf {
      value = checkWithGuardGo;
      description = "checkWithGuard: refinement-predicate-aware variant of `deriveCheck` — runs shape check first via `unitAlg`, then composes the type's refinement predicate when present; required while refined types are encoded outside the canonical Σ-with-Decide-snd form.";
      signature = "checkWithGuard : Type -> Path -> Value -> Computation Null";
    };
  };

  tests =
    let
      FP = fx.types.primitives;
      FC = fx.types.constructors;
      FD = fx.types.dependent;
      FR = fx.types.refinement;
      H = fx.tc.hoas;
    in
    {
      "deriveCheck-thunk-accepts-carrier" = {
        expr =
          let
            T = H.thunk H.derivation;
            carrier = fx.state.thunk.mkThunk { type = "derivation"; name = "x"; outPath = "/nix/store/x"; };
            errs = runCollecting (deriveCheckGo T P.empty carrier);
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-thunk-accepts-non-derivation-carrier" = {
        expr =
          let
            T = H.thunk H.string;
            carrier = fx.state.thunk.mkThunk "hello";
            errs = runCollecting (deriveCheckGo T P.empty carrier);
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-thunk-rejects-non-carrier" = {
        expr =
          let
            T = H.thunk H.derivation;
            errs = runCollecting (deriveCheckGo T P.empty { not_a_thunk = true; });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
          };
        expected = { count = 1; reason = "shape-mismatch"; };
      };

      "deriveCheck-thunk-is-lazy" = {
        expr =
          let
            T = H.thunk H.derivation;
            # `_force` throws on invocation — if validation forced it the
            # whole test would crash.
            bomb = { _tag = "Thunk"; _force = _: throw "force was invoked during validation"; };
            errs = runCollecting (deriveCheckGo T P.empty bomb);
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-record-2field-passes" = {
        expr =
          let
            R = FC.Record { a = FP.Int; b = FP.Bool; };
            errs = runCollecting (deriveCheckGo R._kernel P.empty {
              a = 1;
              b = true;
            });
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-record-missing-field-emits" = {
        expr =
          let
            R = FC.Record { a = FP.Int; b = FP.Bool; };
            errs = runCollecting (deriveCheckGo R._kernel P.empty { a = 1; });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "missing-field";
          path = [ (Pos.Field "b") ];
        };
      };

      "deriveCheck-listOf-int-passes" = {
        expr =
          let
            L = FC.ListOf FP.Int;
            errs = runCollecting (deriveCheckGo L._kernel P.empty [ 1 2 3 ]);
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-listOf-int-rejects-elem1" = {
        expr =
          let
            L = FC.ListOf FP.Int;
            errs = runCollecting (deriveCheckGo L._kernel P.empty [ 1 "x" 3 ]);
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          path = [ (Pos.Elem 1) ];
        };
      };

      "deriveCheck-nested-listof-record" = {
        expr =
          let
            Inner = FC.Record {
              name = FP.String;
              age = FP.Int;
            };
            Outer = FC.ListOf Inner;
            errs = runCollecting (deriveCheckGo Outer._kernel P.empty [
              { name = "a"; age = 1; }
              "wrong"
            ]);
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            firstPathSeg = builtins.head (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          firstPathSeg = Pos.Elem 1;
        };
      };

      "deriveCheck-record-with-listof-field" = {
        expr =
          let
            R = FC.Record { xs = FC.ListOf FP.Int; };
            errs = runCollecting (deriveCheckGo R._kernel P.empty {
              xs = [ 1 "x" ];
            });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          path = [
            (Pos.Field "xs")
            (Pos.Elem 1)
          ];
        };
      };

      "deriveCheck-dependent-dataD-field-uses-prev" = {
        expr =
          let
            Dep = {
              _htag = "mu";
              name = "Dep";
              _dtypeMeta = {
                name = "Dep";
                indexed = false;
                constructors = [
                  {
                    name = "mk";
                    fields = [
                      { name = "tag"; kind = "data"; type = H.unit; }
                      {
                        name = "payload";
                        kind = "dataD";
                        typeFn = prev:
                          if prev.tag._htag == "tt" then H.string else H.int_;
                      }
                    ];
                  }
                ];
              };
            };
            errs = runCollecting (deriveCheckGo Dep P.empty {
              tag = null;
              payload = "ok";
            });
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-dependent-dataD-field-rejects-resolved-type" = {
        expr =
          let
            Dep = {
              _htag = "mu";
              name = "Dep";
              _dtypeMeta = {
                name = "Dep";
                indexed = false;
                constructors = [
                  {
                    name = "mk";
                    fields = [
                      { name = "tag"; kind = "data"; type = H.unit; }
                      {
                        name = "payload";
                        kind = "dataD";
                        typeFn = prev:
                          if prev.tag._htag == "tt" then H.string else H.int_;
                      }
                    ];
                  }
                ];
              };
            };
            errs = runCollecting (deriveCheckGo Dep P.empty {
              tag = null;
              payload = 42;
            });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          path = [
            (Pos.Field "payload")
          ];
        };
      };

      "deriveCheck-either-left-int-passes" = {
        expr =
          let
            E2 = FC.Either FP.Int FP.String;
            errs = runCollecting (deriveCheckGo E2._kernel P.empty {
              _tag = "Left";
              value = 1;
            });
          in
          builtins.length errs;
        expected = 0;
      };

      "deriveCheck-either-left-string-fails" = {
        expr =
          let
            E2 = FC.Either FP.Int FP.String;
            errs = runCollecting (deriveCheckGo E2._kernel P.empty {
              _tag = "Left";
              value = "x";
            });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            firstPathSeg = builtins.head (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          firstPathSeg = Pos.Tag "Left";
        };
      };

      "checkWithGuard-refinement-passes" = {
        expr =
          let
            Pos = FR.refined "Pos" FP.Int (x: x >= 0);
            errs = runCollecting (checkWithGuardGo Pos P.empty 1);
          in
          builtins.length errs;
        expected = 0;
      };

      "checkWithGuard-refinement-rejects-predicate" = {
        expr =
          let
            Pos = FR.refined "Pos" FP.Int (x: x >= 0);
            errs = runCollecting (checkWithGuardGo Pos P.empty (-1));
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "predicate-failed";
          path = [ ];
        };
      };

      "deriveCheck-list-of-record-of-list-of-int" = {
        expr =
          let
            R = FC.Record { xs = FC.ListOf FP.Int; };
            L = FC.ListOf R;
            errs = runCollecting (deriveCheckGo L._kernel P.empty [
              { xs = [ 1 2 ]; }
              { xs = [ 3 "bad" 5 ]; }
            ]);
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          path = [
            (Pos.Elem 1)
            (Pos.Field "xs")
            (Pos.Elem 1)
          ];
        };
      };

      "deriveCheck-record-of-sum-of-product" = {
        expr =
          let
            Prod = FD.Sigma {
              fst = FP.Int;
              snd = _: FP.String;
              universe = 0;
              kernelType = H.sigma "x" FP.Int._kernel (_: FP.String._kernel);
            };
            Sum = FC.Either Prod FP.Bool;
            R = FC.Record { choice = Sum; };
            errs = runCollecting (deriveCheckGo R._kernel P.empty {
              choice = { _tag = "Left"; value = { fst = 1; snd = 42; }; };
            });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          # No synthetic `Pos.Field "value"` between tag and payload.
          path = [
            (Pos.Field "choice")
            (Pos.Tag "Left")
            Pos.SigmaSnd
          ];
        };
      };

      "deriveCheck-variant-with-nested-refinement" = {
        expr =
          let
            PosT = FR.refined "Pos" FP.Int (x: x >= 0);
            V = FC.Variant { Some = PosT; None = FP.Unit; };
            errs = runCollecting (deriveCheckGo V._kernel P.empty {
              _tag = "Some";
              value = "not-an-int";
            });
          in
          {
            count = builtins.length errs;
            reason = (builtins.head errs).reason;
            path = (builtins.head errs).path;
          };
        expected = {
          count = 1;
          reason = "shape-mismatch";
          path = [
            (Pos.Tag "Some")
          ];
        };
      };

      "deriveCheck-firstN-bounds-multi-error" = {
        expr =
          let
            R = FC.Record { a = FP.Int; b = FP.Bool; };
            comp = deriveCheckGo R._kernel P.empty {
              a = "wrong";
              b = "wrong";
            };
            result = fx.trampoline.handle
              {
                handlers = (fx.effects.typecheck.firstN 1);
                state = { collected = [ ]; aborted = false; };
              }
              comp;
          in
          {
            collected = builtins.length result.state.collected;
            aborted = result.state.aborted;
          };
        expected = { collected = 1; aborted = true; };
      };

      "deriveCheck-summarize-buckets-by-reason" = {
        expr =
          let
            R = FC.Record { a = FP.Int; b = FP.Bool; };
            comp = deriveCheckGo R._kernel P.empty {
              a = "wrong";
            };
            result = fx.trampoline.handle
              {
                handlers = fx.effects.typecheck.summarize;
                state = { byReason = { }; passed = 0; failed = 0; };
              }
              comp;
          in
          result.state.byReason;
        expected = { shape-mismatch = 1; missing-field = 1; };
      };

      "deriveElaborate-int-yields-intLit" = {
        expr = (H.elab (runStrict (deriveElaborateGo H.int_ P.empty 42))).tag;
        expected = "int-lit";
      };

      "deriveElaborate-listOf-nat-roundtrip" = {
        expr =
          let
            t = H.elab (runStrict (deriveElaborateGo (H.listOf H.nat) P.empty [ 0 1 2 ]));
          in
          "${t.tag}/${t.d.tag}";
        expected = "desc-con/boot-inr";
      };

      "deriveElaborate-pair-yields-pair" = {
        expr = (H.elab (runStrict (deriveElaborateGo
          (H.sigma "x" H.nat (_: H.bool))
          P.empty
          { fst = 0; snd = true; }))).term.tag;
        expected = "pair";
      };

      "deriveElaborate-thunk-yields-record-con" = {
        expr =
          let
            T = H.thunk H.derivation;
            carrier = fx.state.thunk.mkThunk { type = "derivation"; name = "x"; outPath = "/nix/store/x"; };
            t = H.elab (runStrict (deriveElaborateGo T P.empty carrier));
          in
          t.tag;
        expected = "desc-con";
      };

      "deriveElaborate-thunk-does-not-force" = {
        expr =
          let
            T = H.thunk H.derivation;
            bomb = { _tag = "Thunk"; _force = _: throw "force was invoked during elaboration"; };
            t = H.elab (runStrict (deriveElaborateGo T P.empty bomb));
          in
          t.tag;
        expected = "desc-con";
      };

      # Polymorphic intros as Record field args — kernel checks against
      # the declared field type via explicit Sum/Σ parameters.

      "decide-record-maybe-field-null-accepts" = {
        expr = fx.tc.elaborate.decide
          (FC.Record { a = FC.Maybe FP.String; })._kernel
          { a = null; };
        expected = true;
      };

      "decide-record-maybe-field-just-accepts" = {
        expr = fx.tc.elaborate.decide
          (FC.Record { a = FC.Maybe FP.String; })._kernel
          { a = "x"; };
        expected = true;
      };

      "decide-record-maybe-record-field-accepts-null" = {
        expr = fx.tc.elaborate.decide
          (FC.Record { x = FC.Maybe (FC.Record { a = FP.Int; }); })._kernel
          { x = null; };
        expected = true;
      };

      "decide-record-maybe-record-field-accepts-value" = {
        expr = fx.tc.elaborate.decide
          (FC.Record { x = FC.Maybe (FC.Record { a = FP.Int; }); })._kernel
          { x = { a = 1; }; };
        expected = true;
      };

      "decide-record-variant-field-first-branch-accepts" = {
        expr =
          let
            V = FC.Variant {
              none = FC.Record { };
              luks = FC.Record { mapperName = FP.String; };
            };
          in
          fx.tc.elaborate.decide
            (FC.Record { encryption = V; })._kernel
            { encryption = { _tag = "none"; value = { }; }; };
        expected = true;
      };

      "decide-record-variant-field-second-branch-accepts" = {
        expr =
          let
            V = FC.Variant {
              none = FC.Record { };
              luks = FC.Record { mapperName = FP.String; };
            };
          in
          fx.tc.elaborate.decide
            (FC.Record { encryption = V; })._kernel
            { encryption = { _tag = "luks"; value = { mapperName = "x"; }; }; };
        expected = true;
      };

      "decide-record-variant-three-branch-unit-payload" = {
        expr =
          let
            V = FC.Variant {
              wayland = FP.Unit;
              x11 = FP.Unit;
              hybrid = FP.Unit;
            };
            T = (FC.Record { session = V; })._kernel;
          in
          builtins.all
            (tag: fx.tc.elaborate.decide T {
              session = { _tag = tag; value = null; };
            })
            [ "wayland" "x11" "hybrid" ];
        expected = true;
      };

      "decide-record-sigma-field-accepts-pair" = {
        expr =
          let
            S = FD.Sigma {
              fst = FP.String;
              snd = _: FP.Int;
              universe = 0;
            };
          in
          fx.tc.elaborate.decide
            (FC.Record { p = S; })._kernel
            { p = { fst = "a"; snd = 1; }; };
        expected = true;
      };

      "decide-record-listOf-maybe-field-accepts" = {
        expr = fx.tc.elaborate.decide
          (FC.Record { xs = FC.ListOf (FC.Maybe FP.Int); })._kernel
          { xs = [ null 1 null 2 ]; };
        expected = true;
      };

      "decide-record-maybe-field-soundness" = {
        # Refinement guard inside Maybe inside Record still rejects via
        # `.check` (kernelDecide ∧ guard).
        expr =
          let
            Pos = FR.refined "Pos" FP.Int (x: x > 0);
            T = FC.Record { a = FC.Maybe Pos; };
          in
          {
            null_ok = T.check { a = null; };
            pos_ok = T.check { a = 5; };
            neg_rejected = T.check { a = (-1); };
          };
        expected = { null_ok = true; pos_ok = true; neg_rejected = false; };
      };
    };

}
