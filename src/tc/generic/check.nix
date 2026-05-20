# Generic description-driven value walker — the canonical fold on the
# full HOAS type algebra.
#
# Public surface:
#
#   deriveCheck    : ty → path → value → Computation Unit
#   deriveElaborate: ty → path → value → Computation Hoas
#   checkWithGuard : ty → path → value → Computation Unit
#
# `deriveGo` is a single polymorphic monadic fold over the type algebra,
# parameterised by an `Algebra A`. The two canonical algebras are:
#
#   unitAlg : A = Unit. Every node returns null. Used by `validateValue`
#             through the collecting handler — the walker emits typeCheck
#             effects on failure but constructs nothing.
#   hoasAlg : A = Hoas. Every node constructs the appropriate HOAS term.
#             Used by `elaborateValue` through the strict handler — failures
#             throw; on success `.value` is the elaborated HOAS tree.
#
# Validation and elaboration are not two functors. They are one fold instantiated
# at two carriers. Future interpretations (size, depth, decidable bridges) add
# algebras against the unchanged walker.
#
# The fold owns: shape inspection, `_htag` dispatch, effect emissions, path
# threading, `builtins.foldl'` iteration (avoiding construction-time stack growth
# from eager `bind (pure x) k`), and the dependent-Σ snd-type derivation via an
# internal strict-handler hoasAlg walk on fst.
#
# The algebra owns: per-shape success-case construction at carrier A. The
# field-walker is delegated to the algebra because unitAlg matches the legacy
# `f.type`-only field traversal while hoasAlg threads `prev` through `fieldType`
# for dependent-field typeFn resolution.
#
# Failure modes carry one of these `reason` tags so handlers under
# `fx.effects.typecheck.*` can route:
#
#   shape-mismatch    — structural disagreement at a primitive leaf, a non-attrset
#                       where a constructor record was expected, or an unrecognised
#                       `_con`/`_tag`.
#   missing-field     — a constructor field is absent from the record.
#   extra-field       — the record carries undeclared fields.
#   predicate-failed  — a refinement guard rejected the value after shape passed.
#   deferred-pi       — reserved for proof-bearing kernel terms (Phase 4.4/4.5).
#
# Refinement guards still bind-sequence outside the structural walker via
# `checkWithGuard` — the predicate is a Nix-meta-level function. Phase 4.5
# absorbs the predicate into a Σ-with-Decide-snd kernel encoding, at which
# point `checkWithGuard` collapses into `deriveCheck` over Σ-types and this
# special case deletes.
{ self, fx, ... }:

let
  inherit (fx.kernel) pure bind send;

  G = fx.tc.generic;
  P = G.path;
  Pos = fx.diag.positions;
  D = G.datatype;
  H = fx.tc.hoas;

  # Build the standard typeCheck-effect payload and continue with the
  # algebra's failure carrier. Under strict, the handler throws before the
  # bind continuation runs; under collecting, the bind continuation runs
  # with the resume value (discarded by `(_:`) and the carrier flows on.
  emit = alg: ty: path: reason: context: value:
    bind (send "typeCheck" {
      type = ty;
      inherit context value path reason;
    }) (_: pure alg.onFailure);

  # Wrap an arbitrary HOAS type into a minimal `{ name; check }` record so
  # handlers can format messages. `check = _: false` because every emission
  # represents a failure — strict's `param.type.check param.value` reads
  # `false` and throws; collecting/other handlers append.
  wrapType = ty:
    if builtins.isAttrs ty && ty ? name && ty ? check
    then ty
    else { name = ty._htag or (ty.name or "<unknown>"); check = _: false; };

  tryDatatypeInfo = hoasTy:
    builtins.tryEval (D.datatypeInfo hoasTy);

  # Native-Nix scalar predicates. The closed leaf-bridge — partial categorical
  # embedding of Nix's primitive value category into the kernel value category.
  nativePred = htag:
    if htag == "bool"     then builtins.isBool
    else if htag == "nat" then (v: builtins.isInt v && v >= 0)
    else if htag == "unit"     then (v: v == null)
    else if htag == "string"   then builtins.isString
    else if htag == "int"      then builtins.isInt
    else if htag == "float"    then builtins.isFloat
    else if htag == "attrs"    then builtins.isAttrs
    else if htag == "path"     then builtins.isPath
    else if htag == "derivation" then (v: builtins.isAttrs v && (v.type or null) == "derivation")
    else if htag == "derivation-thunk" then
      (v: builtins.isAttrs v && (v._tag or null) == "DerivationThunk" && v ? _force)
    else if htag == "function" then builtins.isFunction
    else if htag == "any"      then (_: true)
    else if htag == "U"        then (v: builtins.isAttrs v && v ? _kernel)
    else null;

  nativeExpectation = htag:
    if htag == "bool"     then "bool"
    else if htag == "nat"      then "non-negative integer"
    else if htag == "unit"     then "null (unit)"
    else if htag == "string"   then "string"
    else if htag == "int"      then "integer"
    else if htag == "float"    then "float"
    else if htag == "attrs"    then "attrset"
    else if htag == "path"     then "path"
    else if htag == "derivation" then "derivation (attrset with type=\"derivation\")"
    else if htag == "derivation-thunk" then "DerivationThunk carrier (attrset with _tag=\"DerivationThunk\" and _force closure)"
    else if htag == "function" then "function"
    else if htag == "U"        then "Type with _kernel"
    else "<native>";

  # Detect a list-shape datatype: two constructors, the first nullary, the
  # second carrying one data field + one recAt field. The surface form is a
  # Nix list rather than a constructor record.
  isListShape = info:
    let cs = info.constructors; in
    builtins.length cs == 2
    && (builtins.head cs).fields == []
    && (let cons = builtins.elemAt cs 1;
            ks = map (f: f.kind) cons.fields;
        in ks == [ "data" "recAt" ]);

  listElemType = info:
    let cons = builtins.elemAt info.constructors 1;
        elemField = builtins.head cons.fields;
    in elemField.type;

  # Resolve a constructor for an attrset value. Dispatch order:
  #   1. `_con` or `_tag` present → look up by exact name; null on miss.
  #   2. No tag and cardinality 1 → η-rule, the only constructor applies.
  #   3. No tag and cardinality > 1 → null (caller emits shape-mismatch).
  # The cardinality-1 η-rule does NOT shadow an explicit tag: a value with
  # an unknown `_con` against a 1-constructor type is still rejected.
  resolveCon = info: value:
    if !builtins.isAttrs value then null
    else
      let
        cs = info.constructors;
        n = builtins.length cs;
        tag = value._con or value._tag or null;
        findByName = name:
          let go = i:
            if i >= n then null
            else
              let c = builtins.elemAt cs i;
              in if c.name == name then c else go (i + 1);
          in go 0;
      in
        if tag != null then findByName tag
        else if n == 1 then builtins.head cs
        else null;

  # Recover fst's HOAS via a separate strict-handler trampoline over hoasAlg,
  # catching internal failures with tryEval. Used by walkSigma — the
  # dependent snd type requires the elaborated fst HOAS regardless of the
  # outer algebra's carrier. This closes the structural cycle that existed
  # in Phase 4 (`walkSigma → E.elaborateValue`) by routing through the same
  # canonical walker at a different carrier rather than back to the
  # elaborator module.
  elaborateFstHoas = ty: path: value:
    builtins.tryEval (
      (fx.trampoline.handle {
        handlers = fx.effects.typecheck.strict;
        state = null;
      } (deriveGo hoasAlg ty path value)).value
    );

  # Π-typed values: functions and `_hoasImpl`-bearing verified records are
  # accepted; non-functions emit shape-mismatch. A structural walker cannot
  # inspect the function's behaviour without applying it.
  walkPi = alg: ty: path: value:
    if (builtins.isAttrs value && value ? _hoasImpl) || builtins.isFunction value
    then pure (alg.onPi ty value)
    else emit alg (wrapType ty) path "shape-mismatch"
              "expected function, got ${builtins.typeOf value}" value;

  # Σ-types: walk fst at the outer algebra, then derive snd's type by
  # substituting fst's HOAS into `ty.body`. The HOAS recovery uses a
  # separate strict trampoline — even when validating, the dependent snd
  # type needs the elaborated fst.
  #
  # Position alphabet: `Pos.SigmaFst` / `Pos.SigmaSnd` (rendered `Σ.fst`
  # / `Σ.snd`). Matches both the SourceMap walker
  # (`tc/hoas/source_map.nix:127-131`) and Sigma's bespoke surface
  # `verify=` (`types/dependent.nix:584-587`), so the walker and the
  # surface validator emit identical blame paths — Findler-Felleisen
  # invariance under encoding.
  walkSigma = alg: ty: path: value:
    if !(builtins.isAttrs value && value ? fst && value ? snd) then
      emit alg (wrapType ty) path "shape-mismatch"
            "expected { fst; snd; }, got ${builtins.typeOf value}" value
    else
      let
        fstPath = P.extend path Pos.SigmaFst;
        sndPath = P.extend path Pos.SigmaSnd;
      in
      bind (deriveGo alg ty.fst fstPath value.fst) (fstA:
        let fstHoasTry = elaborateFstHoas ty.fst fstPath value.fst; in
        if !fstHoasTry.success then pure alg.onFailure
        else
          let
            sndTyTry = builtins.tryEval (ty.body fstHoasTry.value);
          in
          if !sndTyTry.success then pure alg.onFailure
          else
            bind (deriveGo alg sndTyTry.value sndPath value.snd) (sndA:
              pure (alg.onSigma ty fstA sndA)));

  walkMaybe = alg: ty: path: value:
    if value == null then pure (alg.onMaybeNull ty)
    else
      bind (deriveGo alg ty.inner path value) (innerA:
        pure (alg.onMaybeJust ty innerA));

  # Variant — first-class kernel sum type. Dispatch on `value._tag`,
  # locate the matching branch in `ty.branches`, descend into the branch
  # type with `Pos.Tag tag` as the leaf branch coordinate. No synthetic
  # `Pos.Field "value"` ever appears in the path because the walker
  # treats variants as primitive kernel constructs, not as μ-encoded
  # single-field records.
  #
  # Literature: every major dependent kernel (CIC/Coq, Lean 4, Agda)
  # treats inductive sums as kernel primitives; constructor names live
  # at the surface, positional eliminators at the core. Encoding sums
  # through μ + synthetic field would leak the field name into blame
  # paths, violating Findler-Felleisen / Wadler-Findler blame-label
  # source-invariance.
  walkVariant = alg: ty: path: value:
    if !(builtins.isAttrs value && value ? _tag && value ? value) then
      emit alg (wrapType ty) path "shape-mismatch"
            "expected { _tag; value; }, got ${builtins.typeOf value}" value
    else
      let
        tag = value._tag;
        branches = ty.branches or [];
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
                "unknown variant tag '${toString tag}'" value
        else
          let branchPath = P.extend path (Pos.Tag tag); in
          bind (deriveGo alg branch.type branchPath value.value)
               (innerA: pure (alg.onVariant ty tag innerA));

  # Walk an indexed list against an element HOAS type. The accumulator is
  # algebra-specific (`alg.listAcc`); for unitAlg it stays null (zero
  # per-element allocation), for hoasAlg it is a continuation that builds
  # the cons chain in a single O(N) finish pass.
  #
  # `builtins.foldl'` is strict in the accumulator, so each bind step
  # produces either `pure accB` (passing) or an Impure node with a snoc'd
  # queue (failing). The recursive-`go` shape would recurse N levels at
  # construction time because `bind (pure x) k` evaluates `k x` eagerly.
  walkElems = alg: ty: path: elemTy: value:
    if !builtins.isList value then
      emit alg (wrapType ty) path "shape-mismatch"
            "expected list, got ${builtins.typeOf value}" value
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
              bind (deriveGo alg elemTy childPath v) (elemA:
                pure (alg.listAcc.step ty elemTy accB elemA)));
      in
        bind (builtins.foldl' step (pure (alg.listAcc.init ty elemTy)) indices)
             (accB: pure (alg.listAcc.finish ty elemTy accB));

  walkLegacyList = alg: ty: path: value:
    walkElems alg ty path ty.elem value;

  walkPrim = alg: htag: ty: path: value:
    let pred = nativePred htag; in
    if pred == null then
      emit alg (wrapType ty) path "shape-mismatch"
            "unknown native type tag '${toString htag}'" value
    else if pred value then
      pure (alg.onPrim htag ty value)
    else
      emit alg (wrapType ty) path "shape-mismatch"
            "expected ${nativeExpectation htag}, got ${builtins.typeOf value}" value;

  # μ-/app-form datatypes. List-shape datatypes route through walkElems;
  # attrset values dispatch on `_con`/`_tag` via `resolveCon` and descend
  # through the algebra's `walkFields`. μ-encoded primitives (Bool's
  # `[[],[]]`, Nat's `[[],["recAt"]]`) route back through walkPrim.
  walkDatatype = alg: ty: path: value:
    let infoTry = tryDatatypeInfo ty; in
    if !infoTry.success then
      emit alg (wrapType ty) path "shape-mismatch"
            "type carries no datatype metadata" value
    else
      let
        info = infoTry.value;
        cs = info.constructors;
        sigs = map (c: map (f: f.kind) c.fields) cs;
        isBoolSig = sigs == [ [] [] ];
        isNatSig  = sigs == [ [] [ "recAt" ] ];
      in
      if isListShape info then
        walkElems alg ty path (listElemType info) value
      else if builtins.isAttrs value then
        let con = resolveCon info value; in
        if con == null then
          emit alg (wrapType ty) path "shape-mismatch"
                (info.name or "<datatype>") value
        else
          let
            multiCon = builtins.length cs > 1;
            walkPath = if multiCon
                       then P.extend path (Pos.Tag con.name)
                       else path;
          in alg.walkFields ty walkPath info con value
      else if isBoolSig then walkPrim alg "bool" ty path value
      else if isNatSig  then walkPrim alg "nat"  ty path value
      else
        emit alg (wrapType ty) path "shape-mismatch"
              "datatype '${info.name or "?"}' has no walker for non-attrset value (constructor signatures = ${builtins.toJSON sigs})"
              value;

  # The canonical polymorphic fold. Routes on `ty._htag` over the full
  # HOAS algebra and threads the algebra `alg` through every recursive
  # call. Validation is `deriveGo unitAlg`; elaboration is `deriveGo hoasAlg`.
  deriveGo = alg: ty: path: value:
    let t = ty._htag or null; in
    if t == "pi"        then walkPi alg ty path value
    else if t == "sigma" then walkSigma alg ty path value
    else if t == "maybe" then walkMaybe alg ty path value
    else if t == "variant" then walkVariant alg ty path value
    else if t == "list"  then walkLegacyList alg ty path value
    else if t == "mu" || t == "app" then walkDatatype alg ty path value
    else if nativePred t != null then walkPrim alg t ty path value
    else
      # No recognised `_htag`. Some construction paths attach datatype
      # metadata without setting `_htag`; consult `datatypeInfo` as a
      # fallback before emitting the unknown-tag error.
      let infoTry = tryDatatypeInfo ty; in
      if infoTry.success then walkDatatype alg ty path value
      else
        emit alg (wrapType ty) path "shape-mismatch"
              "unknown type tag '${toString t}'" value;

  # unitAlg's `walkFields`: Phase 4-style. Uses `f.type` directly, no prev
  # threading, foldl' for stack safety. Matches validateValue's legacy
  # field-by-field shape check.
  unitWalkFields = ty: path: _info: con: value:
    let
      fieldComp = f:
        let
          lbl = f.name;
          childPath = P.extend path (Pos.Field lbl);
          hasIt = builtins.hasAttr lbl value;
          fv = if hasIt then builtins.getAttr lbl value else null;
        in
          if !hasIt then
            send "typeCheck" {
              type = wrapType (f.type or { _htag = "<unknown>"; });
              context = lbl;
              value = null;
              path = childPath;
              reason = "missing-field";
            }
          else if f.kind == "recAt" then
            deriveGo unitAlg ty childPath fv
          else
            deriveGo unitAlg f.type childPath fv;
      step = acc: f: bind acc (_: fieldComp f);
    in builtins.foldl' step (pure null) con.fields;

  # hoasAlg's `walkFields`: prev-threaded constructor application chain.
  # Each field's HOAS type is resolved via `D.fieldType field prev` so
  # dependent fields (`typeFn prev`) resolve to the correct kernel type.
  # The accumulator is the HOAS `H.app` chain rooted at `con.ctor`.
  hoasWalkFields = ty: path: info: con: value:
    let
      fields = con.fields or [];
      openExtras = info.openExtras or false;
      fieldNames = map (f: f.name) fields;
      extraFields =
        if openExtras then []
        else builtins.filter
          (n: n != "_con" && n != "_tag" && !(builtins.elem n fieldNames))
          (builtins.attrNames value);
      # Resolve a field's HOAS type from prev. recAt fields recurse on the
      # parent type, decorated with the constructor's metadata so a bare
      # `mu` node retains its datatypeInfo on the inner descent.
      fieldTyAt = f: prev:
        if f.kind == "recAt"
        then
          let t = D.fieldType f prev; in
          if builtins.isAttrs t && (t._htag or null) == "mu"
          then t // { _dtypeMeta = info; }
          else t
        else D.fieldType f prev;
      go = remaining: prev: acc:
        if remaining == [] then pure acc
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
              # Strict aborts here; collecting accumulates the missing-field
              # error and the resulting HOAS is a partial application chain
              # (semantically meaningless under collecting + hoasAlg, but the
              # error stream is correct, which is what collecting consumers
              # read).
              bind (send "typeCheck" {
                type = wrapType (f.type or { _htag = "<unknown>"; });
                context = f.name;
                value = null;
                path = childPath;
                reason = "missing-field";
              }) (_: go rest prev acc)
            else
              bind (deriveGo hoasAlg tyAtF childPath fv) (fieldHoas:
                let
                  prev' = if f.kind == "data" || f.kind == "dataD"
                          then prev // { ${f.name} = fieldHoas; }
                          else prev;
                  acc' = H.app acc fieldHoas;
                in go rest prev' acc');
    in
      if extraFields != []
      then
        bind (send "typeCheck" {
          type = wrapType ty;
          context = "extra fields: ${builtins.concatStringsSep ", " extraFields}";
          inherit value path;
          reason = "extra-field";
        }) (_: go fields {} con.ctor)
      else go fields {} con.ctor;

  unitAlg = {
    onPi        = _: _: null;
    onMaybeNull = _: null;
    onMaybeJust = _: _: null;
    onSigma     = _: _: _: null;
    onVariant   = _: _: _: null;
    onPrim      = _: _: _: null;
    fromHoas    = _: null;
    onFailure   = null;
    listAcc = {
      init   = _: _: null;
      step   = _: _: _: _: null;
      finish = _: _: _: null;
    };
    walkFields = unitWalkFields;
  };

  hoasAlg = {
    onPi = ty: v:
      if builtins.isAttrs v && v ? _hoasImpl then v._hoasImpl
      else if builtins.isFunction v then H.opaqueLam v ty
      else throw "hoasAlg.onPi: walker shape-check should have rejected this";
    onMaybeNull = ty: H.inr ty.inner H.unit H.tt;
    onMaybeJust = ty: inner: H.inl ty.inner H.unit inner;
    onSigma = _: fstA: sndA: H.pair fstA sndA;
    # Variant elaboration mirrors `elaborate.nix:574`'s type-side
    # desugaring of `_htag = "variant"` into nested `H.sum`s:
    # `Variant{T0,…,Tn-1}` ≅ `Sum(T0, Sum(T1, …, Tn-1))`. The active
    # branch's value is injected with the matching `H.inl`/`H.inr`
    # chain so the elaborated kernel value type-checks against the
    # elaborated type.
    onVariant = ty: tag: inner:
      let
        branches = ty.branches or [];
        n = builtins.length branches;
        # Locate the active branch index (the walker already proved it
        # exists — `onVariant` only fires from a successful match).
        activeIdx =
          let go = i:
            if i >= n then null
            else if (builtins.elemAt branches i).tag == tag then i
            else go (i + 1);
          in go 0;
        # Right-associated Sum suffix: `Sum(T_i, Sum(T_{i+1}, …, T_{n-1}))`
        # collapses to just `T_{n-1}` at the deepest position. Matches
        # `elaborate.nix:574`'s `foldl' (acc i: sum branch.type acc)`
        # construction with the same `lastType` base.
        restFrom = i:
          if i == n - 1 then (builtins.elemAt branches i).type
          else H.sum (builtins.elemAt branches i).type (restFrom (i + 1));
        # Wrap `inner` in `i` outer `inr`s then one terminal `inl`
        # (unless it is the last branch, in which case the terminal
        # injection is absent — the rightmost summand is `T_{n-1}` not
        # `Sum(T_{n-1}, ⊥)`).
        inject = i:
          let
            leftTy  = (builtins.elemAt branches i).type;
            rightTy = restFrom (i + 1);
          in
            if i == n - 1 then inner
            else if i == activeIdx then H.inl leftTy rightTy inner
            else H.inr leftTy rightTy (inject (i + 1));
      in
        if n == 0 then
          throw "hoasAlg.onVariant: empty variant has no inhabitants"
        else if activeIdx == null then
          throw "hoasAlg.onVariant: tag '${toString tag}' not in branches"
        else if n == 1 then inner
        else inject 0;
    onPrim = htag: _ty: v:
      if htag == "bool"   then (if v then H.true_ else H.false_)
      else if htag == "nat"      then H.natLit v
      else if htag == "unit"     then H.tt
      else if htag == "string"   then H.stringLit v
      else if htag == "int"      then H.intLit v
      else if htag == "float"    then H.floatLit v
      else if htag == "attrs"    then H.attrsLit
      else if htag == "path"     then H.pathLit
      else if htag == "derivation" then H.derivationLit
      else if htag == "derivation-thunk" then H.derivationThunkLit
      else if htag == "function" then H.fnLit
      else if htag == "any"      then H.anyLit
      else if htag == "U" then
        if builtins.isAttrs v && v ? _kernel then v._kernel
        else throw "hoasAlg.onPrim: U requires _kernel-bearing value"
      else throw "hoasAlg.onPrim: unknown htag '${toString htag}'";
    fromHoas = h: h;
    # Unreachable under strict (the handler throws before bind continues).
    # Under collecting + hoasAlg (unusual combo), the resulting HOAS is
    # garbage but the error stream is preserved — that's what consumers read.
    onFailure = null;
    listAcc = {
      # Continuation-based accumulator: O(1) per step, O(N) finalisation.
      # Direct snoc would be O(K) per step (Nix `++` copies left list),
      # giving O(N²) total — defeats the bench property foldl' established.
      init   = _: _: (rest: rest);
      step   = _: elemTy: acc: elem: (rest: acc (H.cons elemTy elem rest));
      finish = _: elemTy: acc: acc (H.nil elemTy);
    };
    walkFields = hoasWalkFields;
  };

  deriveCheckGo     = ty: path: value: deriveGo unitAlg ty path value;
  deriveElaborateGo = ty: path: value: deriveGo hoasAlg ty path value;

  # Refinement guard: shape first via the unit walker, predicate second.
  # The two checks cannot run in parallel — the predicate's domain is
  # exactly the values that pass shape (Σ-type sequencing).
  #
  # `mkType` does not surface the bare `guard` predicate on the type
  # value; it composes it into `.check` (= `kernelDecide ∧ guard`) and
  # records the kernel-only decision in `.kernelCheck`. We reconstruct
  # the guard's verdict from the two: if shape passes and `.check`
  # rejects, the guard fired. `_kernelSufficient = false` flags the
  # presence of a guard so non-refined types fast-path through.
  #
  # Phase 4.5 absorbs this special case into Σ-with-Decide-snd at which
  # point `checkWithGuardGo` deletes and refinement validation falls out
  # of `deriveGo unitAlg` on a Σ-encoded form.
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
          else send "typeCheck" {
            type = wrapType ty;
            context = "<predicate>";
            inherit value;
            inherit path;
            reason = "predicate-failed";
          });

  runCollecting = comp:
    (fx.trampoline.handle {
      handlers = fx.effects.typecheck.collecting;
      state = [];
    } comp).state;

  runStrict = comp:
    (fx.trampoline.handle {
      handlers = fx.effects.typecheck.strict;
      state = null;
    } comp).value;
in
{
  scope = {
    deriveCheck     = deriveCheckGo;
    deriveElaborate = deriveElaborateGo;
    checkWithGuard  = checkWithGuardGo;
  };

  tests = let
    FP = fx.types.primitives;
    FC = fx.types.constructors;
    FD = fx.types.dependent;
    FR = fx.types.refinement;
    H = fx.tc.hoas;
  in {
    "deriveCheck-record-2field-passes" = {
      expr =
        let
          R = FC.Record { a = FP.Int; b = FP.Bool; };
          errs = runCollecting (deriveCheckGo R._kernel P.empty {
            a = 1; b = true;
          });
        in builtins.length errs;
      expected = 0;
    };

    "deriveCheck-record-missing-field-emits" = {
      expr =
        let
          R = FC.Record { a = FP.Int; b = FP.Bool; };
          errs = runCollecting (deriveCheckGo R._kernel P.empty { a = 1; });
        in {
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
        in builtins.length errs;
      expected = 0;
    };

    "deriveCheck-listOf-int-rejects-elem1" = {
      expr =
        let
          L = FC.ListOf FP.Int;
          errs = runCollecting (deriveCheckGo L._kernel P.empty [ 1 "x" 3 ]);
        in {
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
        in {
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
        in {
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

    "deriveCheck-either-left-int-passes" = {
      expr =
        let
          E2 = FC.Either FP.Int FP.String;
          errs = runCollecting (deriveCheckGo E2._kernel P.empty {
            _tag = "Left"; value = 1;
          });
        in builtins.length errs;
      expected = 0;
    };

    "deriveCheck-either-left-string-fails" = {
      expr =
        let
          E2 = FC.Either FP.Int FP.String;
          errs = runCollecting (deriveCheckGo E2._kernel P.empty {
            _tag = "Left"; value = "x";
          });
        in {
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
        in builtins.length errs;
      expected = 0;
    };

    "checkWithGuard-refinement-rejects-predicate" = {
      expr =
        let
          Pos = FR.refined "Pos" FP.Int (x: x >= 0);
          errs = runCollecting (checkWithGuardGo Pos P.empty (-1));
        in {
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
        in {
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
        in {
          count = builtins.length errs;
          reason = (builtins.head errs).reason;
          path = (builtins.head errs).path;
        };
      expected = {
        count = 1;
        reason = "shape-mismatch";
        # Either now uses H.variant — no synthetic `Pos.Field "value"`
        # between the tag and the payload's interior.
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
            _tag = "Some"; value = "not-an-int";
          });
        in {
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
            a = "wrong"; b = "wrong";
          };
          result = fx.trampoline.handle {
            handlers = (fx.effects.typecheck.firstN 1);
            state = { collected = []; aborted = false; };
          } comp;
        in {
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
          result = fx.trampoline.handle {
            handlers = fx.effects.typecheck.summarize;
            state = { byReason = {}; passed = 0; failed = 0; };
          } comp;
        in result.state.byReason;
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
        in "${t.tag}/${t.d.tag}";
      expected = "desc-con/boot-inr";
    };

    "deriveElaborate-pair-yields-pair" = {
      expr = (H.elab (runStrict (deriveElaborateGo
        (H.sigma "x" H.nat (_: H.bool)) P.empty { fst = 0; snd = true; }))).tag;
      expected = "pair";
    };
  };

  __docs = {
    checkWithGuard = {
      description = "checkWithGuard: refinement-predicate-aware variant of `deriveCheck` — runs shape check first via `unitAlg`, then composes the type's refinement predicate when present; required while refined types are encoded outside the canonical Σ-with-Decide-snd form.";
      signature = "checkWithGuard : Type -> Path -> Value -> Computation Null";
    };
    deriveCheck = {
      description = "deriveCheck: canonical typed walker over the HOAS algebra threading `unitAlg` — emits `fx.effects.typecheck` failures with structured `reason` (shape-mismatch, missing-field, extra-field, predicate-failed, deferred-pi) and `path` (a `fx.diag.positions` chain).";
      signature = "deriveCheck : Type -> Path -> Value -> Computation Null";
    };
    deriveElaborate = {
      description = "deriveElaborate: canonical typed walker over the HOAS algebra threading `hoasAlg` — reconstructs the corresponding HOAS term at every successfully-checked node; shares path threading and dispatch with `deriveCheck`.";
      signature = "deriveElaborate : Type -> Path -> Value -> Computation Hoas";
    };
  };
}
