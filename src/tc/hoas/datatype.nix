# Datatype macro: declarative constructor signatures compile to a DataSpec
# record `{ name; cons; D; T; <conName_i>; elim; _dtypeMeta }`. Plus the
# prelude instances (NatDT, ListDT, SumDT) and the surface forwarders
# (`nat`, `listOf`, `sum`, `zero`, `succ`, `nil`, `cons`, `inl`, `inr`)
# that route through the macro-generated constructors so the kernel's
# `dt-ctor-mono`/`dt-ctor-poly` chain-flatten path applies.
#
# A signature is a name and a non-empty ordered list of constructors;
# each constructor has a name and an ordered list of field
# specifications. The macro is a pure Nix function from the signature
# attrset to an attrset of HOAS terms; the kernel never learns about it.
{ self, ... }:

let
  # Field specification tags — invisible to consumers, used by conDesc /
  # mkCtor / stepTyOf to dispatch on field kind.
  _fieldMarker = "__nix-effects-datatype-field__";
  _conMarker = "__nix-effects-datatype-con__";
in {
  scope = {
    # Field specifications. Each is a tagged attrset; position in the
    # constructor's field list is the position in the constructor's
    # argument list and in the payload spine.
    field    = name: type: { _fieldTag = _fieldMarker; kind = "data";  inherit name type; };
    fieldD   = name: tyFn: { _fieldTag = _fieldMarker; kind = "dataD"; inherit name; typeFn = tyFn; };
    # Recursive self-reference at a specific index. `idxFn : prev -> Hoas`
    # computes the recursive-call index from markers bound by earlier
    # data/dataD fields. `recField name` is sugar for the recursive field
    # at the ⊤-slice (idxFn = _: ttPrim) — valid only when the enclosing
    # datatype's index type is ⊤, and equivalent to `recFieldAt name
    # (_: ttPrim)`.
    recField   = name:        { _fieldTag = _fieldMarker; kind = "recAt"; inherit name; idxFn = _: self.ttPrim; };
    recFieldAt = name: idxFn: { _fieldTag = _fieldMarker; kind = "recAt"; inherit name idxFn; };
    piField  = name: S:    { _fieldTag = _fieldMarker; kind = "pi";    inherit name S; };
    piFieldD = name: SFn:  { _fieldTag = _fieldMarker; kind = "piD";   inherit name; SFn = SFn; };

    # Constructor specification. `con` builds a constructor whose target
    # index is implicitly `ttPrim` (for ⊤-indexed families); `conI`
    # carries an explicit `targetIdx : prev -> Hoas` function computing
    # the target index from bound data/dataD markers.
    con  = name: fields:             { _conTag = _conMarker; inherit name fields; targetIdx = _: self.ttPrim; };
    conI = name: fields: targetIdx:  { _conTag = _conMarker; inherit name fields targetIdx; };

    # conDesc I prev fields targetIdx : Hoas Desc
    # Compile a field list into a description spine over index type `I`.
    # `prev` threads HOAS markers for earlier `field` / `fieldD` bindings
    # (the only field kinds that bind a description-level variable via
    # descArg); `recAt`, `pi`, `piD` do not extend `prev`. At the
    # ret-leaf the target index is `targetIdx prev`. `pi` / `piD` emit
    # the ⊤-slice `descPi` alias and are therefore only valid at I=⊤;
    # at I≠⊤ an indexed pi-field sugar would be required and none
    # exists yet.
    conDesc = I: prev: fields: targetIdx:
      let
        inherit (self) retI recI descArg descPi conDesc;
        isUnitI = (I._htag or null) == "unit";
      in
      if fields == [] then retI (targetIdx prev)
      else let
        f = builtins.head fields;
        rest = builtins.tail fields;
        k = f.kind;
      in
        if      k == "data"  then descArg f.type          (v: conDesc I (prev // { ${f.name} = v; }) rest targetIdx)
        else if k == "dataD" then descArg (f.typeFn prev) (v: conDesc I (prev // { ${f.name} = v; }) rest targetIdx)
        else if k == "recAt" then recI (f.idxFn prev) (conDesc I prev rest targetIdx)
        else if k == "pi"    then
          if isUnitI
          then descPi f.S (conDesc I prev rest targetIdx)
          else throw "datatype: piField '${f.name}' not supported at indexed family (I != unit)"
        else if k == "piD"   then
          if isUnitI
          then descPi (f.SFn prev) (conDesc I prev rest targetIdx)
          else throw "datatype: piFieldD '${f.name}' not supported at indexed family (I != unit)"
        else throw "datatype: unknown field kind '${k}'";

    # spineDesc descs : Hoas Desc
    # Combine per-constructor descriptions into a single description.
    # Uniform recursion: the singleton case IS the leaf (no outer tag);
    # n>=2 produces a right-associated plus-spine `plus D_0 (plus D_1
    # (... D_{n-1}))`. `interp (plus A B) X i` reduces STRUCTURALLY to
    # kernel `Sum (⟦A⟧ X i) (⟦B⟧ X i)` — no bool-tag dispatch, no
    # commuting-conv obligation on `interp ∘ bool-elim`. Matches the
    # plus-based shape used by the prelude descriptions (`natDesc` /
    # `listDesc` / `sumDesc` / `boolDesc` at `hoas/desc.nix` and
    # `hoas/combinators.nix`).
    spineDesc = descs:
      let
        inherit (self) plus spineDesc;
        n = builtins.length descs;
      in
      if n == 0 then throw "datatype: n=0 rejected (use H.void)"
      else if n == 1 then builtins.head descs
      else
        let
          D1 = builtins.elemAt descs 0;
          rest = builtins.tail descs;
        in plus D1 (spineDesc rest);

    # payloadTuple xs : Hoas
    # Build a right-nested pair from an ordered list of HOAS terms.
    # The terminator is `refl` — every call site feeds this into a
    # `descCon` at a ret-leaf of its description, where the payload's
    # innermost component inhabits `Eq I j i` (at I=⊤, `refl` witnesses
    # `Eq ⊤ tt tt`).
    payloadTuple = xs:
      let inherit (self) pair refl payloadTuple; in
      if xs == [] then refl
      else pair (builtins.head xs) (payloadTuple (builtins.tail xs));

    # encodeTag I dOuter descsHoas targetIdxVal t payload : Hoas
    # Wrap `payload` with the (n-1)-deep plus-coproduct prefix committing
    # at position t (0-based) out of n total. Mirrors spineDesc
    # structurally: at every layer the L/R type arguments are the interps
    # of the current summand and the plus-tree of the remaining summands
    # respectively, under the muFam `λi:I. μI I dOuter i`, evaluated at
    # the constructor's `targetIdxVal`. `inlPrim L R` at position t=0;
    # otherwise `inrPrim L R (encodeTag ... (t-1) (rest) payload)`. n=1
    # has no prefix. `descsHoas` must have length >= 1; the singleton
    # case returns `payload` directly.
    encodeTag = I: dOuter: descsHoas: targetIdxVal: t: payload:
      let
        inherit (self) plus inlPrim inrPrim interpHoas
                        muI lam encodeTag;
        n = builtins.length descsHoas;
        muFam = lam "_i" I (iArg: muI I dOuter iArg);
        # Plus-spine of summands starting at index k. Requires
        # `n - k >= 1`.
        spineAfter = k:
          let remaining = n - k; in
          if remaining == 1 then builtins.elemAt descsHoas k
          else plus (builtins.elemAt descsHoas k) (spineAfter (k + 1));
        interpAt = dH: interpHoas I dH muFam targetIdxVal;
      in
      if n == 1 then payload
      else
        let
          lTy = interpAt (builtins.elemAt descsHoas 0);
          rTy = interpAt (spineAfter 1);
          rest = builtins.tail descsHoas;
        in
        if t == 0 then inlPrim lTy rTy payload
        else inrPrim lTy rTy
               (encodeTag I dOuter rest targetIdxVal (t - 1) payload);

    # Internal: build a DataSpec at index type `I`. When `indexed =
    # false`, exposes `T` as the bare kernel-level type `muI I D ttPrim`
    # (I must be ⊤) and builds a 1-ary eliminator `P : T → U`. When
    # `indexed = true`, exposes `T` as the ann-wrapped family-as-function
    # `λi:I. muI I D i` and builds a 2-ary eliminator `P : (i:I) → muI
    # I D i → U` with an explicit scrutinee-index binder. Description
    # spine, constructor terms, and dispatchStep / jTransportLeaf are
    # shared across both modes, parameterised on the per-constructor
    # `targetIdx` spec field.
    _datatypeImpl = { I, indexed, name, consList }:
      let
        inherit (self)
          u forall lam let_ app ann fst_ snd_ pair
          ttPrim unitPrim
          plus sumPrim inlPrim inrPrim sumElimPrim
          eq refl j
          muI descI descCon descInd interpHoas allHoas
          conDesc spineDesc payloadTuple encodeTag;

        n = builtins.length consList;
        conNames = map (c: c.name) consList;

        # First duplicate constructor name (null if none).
        dupConName = let
          idxs = builtins.genList (x: x) n;
          step = acc: i:
            if acc != null then acc
            else let nm = builtins.elemAt conNames i;
                     seen = builtins.genList (j: builtins.elemAt conNames j) i;
                 in if builtins.elem nm seen then nm else null;
          in builtins.foldl' step null idxs;

        conDescs = map (c: conDesc I {} c.fields c.targetIdx) consList;
        # The description spine contains bare canonical forms (e.g.,
        # `retI j` carries a bare canonical j with no infer rule under
        # bidirectional discipline). `ann _ (descI I)` lets every
        # consumer (the `mu` type rule, `descCon`'s D, `descInd`'s D)
        # check the spine in CHECK mode against `Desc I`, where the
        # bare canonical forms are accepted by the existing check rules.
        D = ann (spineDesc conDescs) (descI I);
        # Bare μ at the constant ⊤ index. The exposed `T` at
        # indexed=false, and the field type of `pi` / `piD` binders
        # (which are only valid at I=⊤ — see conDesc).
        TAtTt = muI I D ttPrim;
        # Family-as-function: `λi:I. muI I D i`. The exposed `T` at
        # indexed=true.
        TFam = ann (lam "i" I (iArg: muI I D iArg))
                   (forall "_" I (_: u 0));
        T = if indexed then TFam else TAtTt;

        muFam = lam "_i" I (iArg: muI I D iArg);
        ppTy = forall "i" I (iArg: forall "_" (muI I D iArg) (_: u 0));

        # Apply the user motive `P` to a scrutinee `x` at its index
        # `idx`. At indexed=false the user motive is 1-ary and `idx` is
        # ignored; at indexed=true the motive is 2-ary.
        applyMotive = P: idx: x:
          if indexed then app (app P idx) x
          else app P x;

        # HOAS type of field `f` given `prev` markers for earlier
        # data/dataD fields. data/dataD bind a description-level
        # variable visible to later dependent forms; recAt / pi / piD
        # compile to recI / descPi which do not extend `prev`.
        fieldTyOf = f: prev:
          if      f.kind == "data"  then f.type
          else if f.kind == "dataD" then f.typeFn prev
          else if f.kind == "recAt" then muI I D (f.idxFn prev)
          else if f.kind == "pi"    then forall "_" f.S (_: muI I D ttPrim)
          else if f.kind == "piD"   then forall "_" (f.SFn prev) (_: muI I D ttPrim)
          else throw "datatype '${name}': unknown field kind '${f.kind}'";

        extendsPrev = f: f.kind == "data" || f.kind == "dataD";
        isIHField = f: f.kind == "recAt" || f.kind == "pi" || f.kind == "piD";

        # Π type of constructor `c`. Terminates in `muI I D (c.targetIdx
        # prev)` — the per-constructor μ-slice at its declared target
        # index. At I=⊤ with the default targetIdx this is `muI ⊤ D
        # ttPrim` = TAtTt.
        ctorTyOf = c:
          let
            tyGo = remaining: prev:
              if remaining == [] then muI I D (c.targetIdx prev)
              else
                let f = builtins.head remaining;
                    rest = builtins.tail remaining;
                in forall f.name (fieldTyOf f prev) (v:
                     tyGo rest
                       (if extendsPrev f then prev // { ${f.name} = v; } else prev));
          in tyGo c.fields {};

        # Build constructor term for the i-th constructor. Zero-field cons
        # become `descCon D <tag-encoded tt>` directly; fielded cons build
        # a curried lam cascade emitting descCon over the payloadTuple of
        # the args, wrapped in `ann` against the full Π type so the ctor
        # stays inferable when applied.
        #
        # Fielded cons are tagged `dt-ctor-mono` so `elaborate` can
        # recognise saturated applications in the `app` branch and emit a
        # flat `desc-con` Tm. Unsaturated or non-chain uses route through
        # `fallback` = `ann bareCtor ctorTyOf`, preserving the inferable
        # surface.
        mkCtor = i: c:
          if c.fields == []
          then
            let tIdx = c.targetIdx {}; in
            descCon D tIdx (encodeTag I D conDescs tIdx i (payloadTuple []))
          else
            let
              bareGo = remaining: prev: collected:
                if remaining == [] then
                  let tIdx = c.targetIdx prev; in
                  descCon D tIdx
                    (encodeTag I D conDescs tIdx i (payloadTuple collected))
                else
                  let f = builtins.head remaining;
                      rest = builtins.tail remaining;
                  in lam f.name (fieldTyOf f prev) (v:
                       bareGo rest
                         (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                         (collected ++ [v]));
              bareCtor = bareGo c.fields {} [];
              fallback = ann bareCtor (ctorTyOf c);
            in {
              _htag = "dt-ctor-mono";
              ctorIndex = i;
              nCtors = n;
              dHoas = D;
              # Index type of the enclosing datatype and the
              # constructor's target-index function. `elaborate`'s
              # chain-flatten path uses these to emit the correct
              # `descCon` i-slot and per-summand `interp` types at
              # I ≠ ⊤. `targetIdx : prev → Hoas I` — `prev` is an
              # attrset keyed by data/dataD field names (declaration
              # order), values are HOAS arguments collected from the
              # app spine.
              inherit I;
              targetIdx = c.targetIdx;
              # Per-constructor HOAS descriptions — consumed by
              # `elaborate`'s flatten path to precompute the per-layer
              # L/R interp Tms of the `inlPrim` / `inrPrim` wrapping.
              inherit conDescs;
              nFields = builtins.length c.fields;
              fields = c.fields;
              inherit fallback;
            };

        ctorRecord = builtins.listToAttrs (builtins.genList (i:
          let c = builtins.elemAt consList i;
          in { name = c.name; value = mkCtor i c; }
        ) n);

        # Type of step_i. Zero-field constructors reduce to `applyMotive
        # P (c.targetIdx {}) C_i`. Fielded constructors produce a Π over
        # fields (in declaration order), then a Π over IH binders (one
        # per recAt/pi/piD field in declaration order), terminating in
        # `applyMotive P (c.targetIdx prev) (C_i applied-to-fields)`.
        #
        # The terminal application chain requires C_i to be inferable,
        # hence mkCtor's ann-wrapping for fielded cons.
        stepTyOf = P: i: c:
          if c.fields == [] then
            applyMotive P (c.targetIdx {}) (mkCtor i c)
          else
            let
              ctor = mkCtor i c;

              # Reconstruct `prev` markers (data/dataD fields only) from
              # the ordered marker list, used to evaluate `c.targetIdx
              # prev` at the terminal position.
              prevOfMarkers = ms:
                builtins.foldl' (acc: m:
                  if m.kind == "data" || m.kind == "dataD"
                  then acc // { ${m.name} = m.marker; }
                  else acc) {} ms;

              ihGo = ihRemaining: markers:
                let
                  applied = builtins.foldl' (acc: m: app acc m.marker)
                                            ctor
                                            markers;
                in
                  if ihRemaining == [] then
                    applyMotive P (c.targetIdx (prevOfMarkers markers)) applied
                  else
                    let f = builtins.head ihRemaining;
                        rest = builtins.tail ihRemaining;
                        m = builtins.head (builtins.filter
                              (x: x.name == f.name) markers);
                        ihTy =
                          if      f.kind == "recAt" then
                            applyMotive P (f.idxFn m.prev) m.marker
                          else if f.kind == "pi"    then
                            forall "s" f.S (s:
                              applyMotive P ttPrim (app m.marker s))
                          else
                            forall "s" (f.SFn m.prev) (s:
                              applyMotive P ttPrim (app m.marker s));
                    in forall ("ih_" + f.name) ihTy (_: ihGo rest markers);

              # Π over fields, collecting markers + each field's `prev`
              # snapshot. After the last field, `ihGo` adds the IH binders.
              fieldGo = remaining: prev: collected:
                if remaining == [] then
                  ihGo (builtins.filter isIHField c.fields) collected
                else
                  let f = builtins.head remaining;
                      rest = builtins.tail remaining;
                  in forall f.name (fieldTyOf f prev) (v:
                       fieldGo rest
                         (if extendsPrev f then prev // { ${f.name} = v; } else prev)
                         (collected ++ [{
                            inherit (f) name kind;
                            marker = v;
                            prev = prev;
                          }]));
            in fieldGo c.fields {} [];

        # Apply user-supplied step `s` to the projections of `payload` and
        # `payloadIH` per `c`'s field list.
        #
        # Field x_j (0-based) lives at fst (snd^j payload), where the
        # payload is a right-nested pair from payloadTuple — so fields in
        # declaration order line up with snd-descents.
        #
        # For payloadIH, only rec/pi/piD fields contribute a Σ component
        # (data/dataD's allHoas case is the identity on the tail). The
        # i-th rec/pi IH (0-based among rec/pi-only fields, in declaration
        # order) lives at fst (snd^i payloadIH).
        buildStepApply = s: c: payload: payloadIH:
          if c.fields == [] then s
          else
            let
              projAt = j: src:
                let go = idx: acc:
                  if idx == 0 then fst_ acc
                  else go (idx - 1) (snd_ acc);
                in go j src;
              fieldArgs = builtins.genList (j: projAt j payload)
                                           (builtins.length c.fields);
              ihCount = builtins.length (builtins.filter isIHField c.fields);
              ihArgs = builtins.genList (i: projAt i payloadIH) ihCount;
              withFields = builtins.foldl' (acc: a: app acc a) s fieldArgs;
              withIHs = builtins.foldl' (acc: a: app acc a) withFields ihArgs;
            in withIHs;

        # Reconstruct `prev` markers (for data/dataD fields only) from
        # a runtime payload value. Used by dispatchStep to evaluate a
        # constructor's `targetIdx` at dispatch time so the J-motive can
        # carry the correct `(I, targetIdx_c)` witness pair.
        prevOfPayload = c: payload:
          let
            projAt = j: src:
              let go = idx: acc:
                if idx == 0 then fst_ acc
                else go (idx - 1) (snd_ acc);
              in go j src;
            step = acc: idx:
              let f = builtins.elemAt c.fields idx; in
              if f.kind == "data" || f.kind == "dataD"
              then acc // { ${f.name} = projAt idx payload; }
              else acc;
          in builtins.foldl' step {} (builtins.genList (x: x) (builtins.length c.fields));

        # dispatchStep Pp iArg ctx descs steps cons payload payloadIH : Hoas
        # Walks the per-constructor descriptions in declaration order,
        # threading an outer-context wrapper `ctx` that reconstitutes the
        # full payload at each level (used in the sumElim motive so conv
        # discharges Pp iArg (descCon D iArg (ctx ...)) ≡ P (C_i ...) via
        # Pp-β + Σ-η + J-transport on the leaf Eq witness). Pp is the
        # indexed motive wrapper `λi:I. λx:muI I D i. P-applied`; at
        # indexed=false it ignores i and applies P 1-ary, at indexed=true
        # it applies P 2-ary (i.e. Pp = P). n=1 (leaf) wraps the user
        # step in J-transport over the leaf Eq witness; n>=2 emits a
        # sumElim that commits to constructor i on `inl` (J-transported)
        # and descends into the rest-spine on `inr`.
        #
        # J-transport (jTransportLeaf targetIdx_c payloadCtx c r userApplied):
        # The user step `s` produces `userApplied : app Pp targetIdx_c
        # (descCon D targetIdx_c (payloadCtx (pair f_0 (... (pair f_{k-1}
        # refl)))))` where each f_i = fst(snd^i r) and the leaf is the
        # macro-inserted `refl`. The expected type is `app Pp iArg (descCon
        # D iArg (payloadCtx (pair f_0 (... (pair f_{k-1} snd^k r)))))` —
        # same modulo the iArg position and the leaf Eq witness `snd^k r :
        # Eq I targetIdx_c iArg`. MLTT without K cannot conv `VRefl ≡
        # VNe(eq)`; J is the sanctioned transport. Motive `M(y,e) = app
        # Pp y (descCon D y (payloadCtx (pair f_0 (... (pair f_{k-1}
        # e)))))`; base `M(targetIdx_c, refl) ≡ userApplied`; result
        # `M(iArg, snd^k r)` matches the expected type. k=0 corner: r
        # ITSELF is the Eq witness and `payloadCtx e` is the full payload
        # at the leaf.
        dispatchStep = Pp: iArg: ctx: descs: steps: cons: payload: payloadIH:
          let
            n' = builtins.length descs;

            jTransportLeaf = targetIdx_c: payloadCtx: c: r: userApplied:
              let
                k = builtins.length c.fields;
                projAt = i: src:
                  let go = idx: acc:
                    if idx == 0 then fst_ acc
                    else go (idx - 1) (snd_ acc);
                  in go i src;
                sndN = i: src:
                  let go = idx: acc:
                    if idx == 0 then acc
                    else go (idx - 1) (snd_ acc);
                  in go i src;
                eLeaf = sndN k r;
                buildPayload = e:
                  let
                    go = i:
                      if i == k then e
                      else pair (projAt i r) (go (i + 1));
                  in go 0;
                motive = lam "y" I (y:
                         lam "e" (eq I targetIdx_c y) (e:
                           app (app Pp y)
                               (descCon D y (payloadCtx (buildPayload e)))));
              in j I targetIdx_c motive userApplied iArg eLeaf;
          in
          if n' == 1 then
            let
              c = builtins.head cons;
              s = builtins.head steps;
              applied = buildStepApply s c payload payloadIH;
              targetIdx_c = c.targetIdx (prevOfPayload c payload);
            in jTransportLeaf targetIdx_c ctx c payload applied
          else
            let
              D1 = builtins.elemAt descs 0;
              s1 = builtins.head steps;
              c1 = builtins.head cons;
              restD = builtins.tail descs;
              restS = builtins.tail steps;
              restC = builtins.tail cons;
              restSpine = spineDesc restD;
              # Interp types of the two summands at the current iArg:
              # the outer plus's interp reduces to `Sum lInterp rInterp`
              # (kernel Sum), and `payload : Sum lInterp rInterp` is
              # dispatched via `sumElimPrim`.
              lInterp = interpHoas I D1 muFam iArg;
              rInterp = interpHoas I restSpine muFam iArg;
              # Sum-elim motive: each summand inhabits this Pp-target
              # rebuilt through `ctx (inlPrim/inrPrim …)`.
              sumMot = lam "s" (sumPrim lInterp rInterp) (s:
                forall "rih" (allHoas I D (plus D1 restSpine) Pp iArg s) (_:
                  app (app Pp iArg) (descCon D iArg (ctx s))));
              onInl = lam "r" lInterp (r:
                      lam "rih" (allHoas I D D1 Pp iArg r) (rih:
                        let targetIdx_c1 = c1.targetIdx (prevOfPayload c1 r); in
                        jTransportLeaf targetIdx_c1
                          (local: ctx (inlPrim lInterp rInterp local))
                          c1 r
                          (buildStepApply s1 c1 r rih)));
              ctx' = local: ctx (inrPrim lInterp rInterp local);
              onInr = lam "r" rInterp (r:
                      lam "rih" (allHoas I D restSpine Pp iArg r) (rih:
                        dispatchStep Pp iArg ctx' restD restS restC r rih));
            in app (sumElimPrim lInterp rInterp sumMot onInl onInr payload)
                 payloadIH;

        # Generic eliminator. The closed term is wrapped in `ann` against
        # its full Π type so it stays inferable when applied via `app` in
        # checked positions — the bidirectional kernel has no infer rule
        # for bare `lam`. `ann` is eval-transparent, so nf-equivalence
        # against the inline-adapter spelling is preserved.
        motiveTy =
          if indexed
          then forall "i" I (iArg: forall "_" (muI I D iArg) (_: u 0))
          else forall "_" TAtTt (_: u 0);
        stepNames = builtins.genList (i: "step_${toString i}") n;

        # Wrap a body with `lam step_i (stepTyOf P i c)` for each
        # constructor in declaration order, then call `mkBody` with the
        # collected step markers.
        buildLamCascade = mkBody: P:
          let
            go = i: stepsAcc:
              if i == n then mkBody stepsAcc
              else
                let c = builtins.elemAt consList i; in
                lam (builtins.elemAt stepNames i) (stepTyOf P i c) (s:
                  go (i + 1) (stepsAcc ++ [s]));
          in go 0 [];

        buildPiCascade = mkBody: P:
          let
            go = i:
              if i == n then mkBody
              else
                let c = builtins.elemAt consList i; in
                forall (builtins.elemAt stepNames i) (stepTyOf P i c) (_:
                  go (i + 1));
          in go 0;

        # Step body for `descInd`. Same shape at indexed=false and
        # indexed=true — the step function is always `λi:I. λd:⟦D⟧ muFam
        # i. λih:All D D Pp i d. dispatchStep Pp i id conDescs steps cons
        # d ih`.
        indStep = Pp: steps:
          lam "i" I (iArg:
          lam "d" (interpHoas I D muFam iArg) (d:
          lam "ih" (allHoas I D D Pp iArg d) (ih:
            dispatchStep Pp iArg (x: x) conDescs steps consList d ih)));

        elimTy =
          if indexed then
            forall "P" motiveTy (P:
            buildPiCascade
              (forall "i" I (iArg:
                forall "scrut" (muI I D iArg) (scrut: app (app P iArg) scrut)))
              P)
          else
            forall "P" motiveTy (P:
            buildPiCascade
              (forall "scrut" TAtTt (scrut: app P scrut))
              P);

        elimBody =
          if indexed then
            lam "P" motiveTy (P:
            buildLamCascade (steps:
              lam "i" I (iArg:
              lam "scrut" (muI I D iArg) (scrut:
                let_ "Pp" ppTy P (Pp:
                  descInd D Pp (indStep Pp steps) iArg scrut))))
              P)
          else
            lam "P" motiveTy (P:
            buildLamCascade (steps:
              lam "scrut" TAtTt (scrut:
                let_ "Pp" ppTy
                  (lam "i" I (_: lam "x" (muI I D ttPrim) (x: app P x))) (Pp:
                  descInd D Pp (indStep Pp steps) ttPrim scrut)))
              P);

        elim = ann elimBody elimTy;

        # Uniform metadata exposed alongside the DataSpec. `indexTy`
        # describes the index type of the family; at `indexed=false` it
        # is the unit type, at `indexed=true` it is the user-supplied
        # `I`. Consumers that walk `cons[i].fields` see only `name` /
        # `kind` — the full spec is available under `_cons`.
        _dtypeMeta = {
          inherit name indexed;
          indexTy = I;
          cons = map (c: {
            name = c.name;
            fields = map (f: { name = f.name; kind = f.kind; }) c.fields;
          }) consList;
        };

        # Per-field polymorphic types, consumed by datatypeP / datatypePI
        # to build the outer `ann (λparams. monoField) (Π(params).
        # monoFieldTy)` wrapping. At indexed=false `T`'s type is `U`; at
        # indexed=true `T` is a function from I to U and its type is
        # `Π(i:I). U`.
        _tys = {
          D = descI I;
          T = if indexed then forall "_" I (_: u 0) else u 0;
          elim = elimTy;
        } // (builtins.listToAttrs (builtins.genList (i:
          let c = builtins.elemAt consList i; in
          { name = c.name; value = ctorTyOf c; }
        ) n));
      in
        if n == 0 then throw "datatype '${name}': n=0 rejected (use H.void)"
        else if dupConName != null then
          throw "datatype '${name}': duplicate constructor name '${dupConName}'"
        else (ctorRecord // {
          inherit name D elim _dtypeMeta _tys;
          # Attach `_dtypeMeta` to the exported `T` so the elaborate-layer
          # extract path can recover constructor + field names when
          # decomposing macro-generated VMu values. Internal uses of `T`
          # within this let-block (fieldTyOf, ctorTyOf, dispatchStep, etc.)
          # are unaffected — the HOAS elaborator only reads `_htag` and `D`
          # from a "mu" form; extra attrs are ignored.
          T = T // { inherit _dtypeMeta; };
          _cons = consList;
        });

    # Monomorphic ⊤-indexed DataSpec. Exposes `T = muI ⊤ D ttPrim` (a
    # bare μ-type) and a 1-ary eliminator `P : T → U`.
    datatype = name: consList:
      self._datatypeImpl {
        I = self.unitPrim;
        indexed = false;
        inherit name consList;
      };

    # Monomorphic indexed DataSpec over index type `I`. Exposes `T = ann
    # (λi:I. muI I D i) (Π(_:I). U)` — a family-as-function — and a
    # 2-ary eliminator `P : (i:I) → muI I D i → U` with an explicit
    # scrutinee-index binder. Each constructor is a `conI name fields
    # targetIdx` where `targetIdx : prev → Hoas` computes the
    # constructor's target index from bound data/dataD markers;
    # recursive fields at non-default indices use `recFieldAt name
    # idxFn`.
    datatypeI = name: I: consList:
      self._datatypeImpl {
        inherit I;
        indexed = true;
        inherit name consList;
      };

    # Internal: polymorphic datatype builder. Each output field f is the
    # mono field λ-abstracted over params, wrapped in `ann` against
    # `Π(params). T_f` where `T_f` is pulled from the mono spec's
    # `_tys.<field>`. The outer `ann` is what makes the curried
    # constructor/eliminator inferable in checked positions after the
    # first parameter application; without it `app <polyField> firstArg`
    # would have a bare-λ head and fail synthesis.
    #
    # At `indexed = true`, `indexFn markers : Hoas` computes the index
    # type from parameter markers (the param-dependent analogue of
    # `datatypeI`'s I argument); the spec of each constructor uses
    # `conI name fields targetIdx`.
    #
    # The probe call `mkCons dummyMarkers` is only used to extract
    # constructor names and metadata (via shallow attrs c.name / f.name /
    # f.kind). Each polymorphic field's closure re-runs `mkCons` with real
    # HOAS markers at elaborate-time, so field types and constructor
    # bodies are never resolved against the probe's dummy values.
    _datatypePImpl = { indexed, name, params, indexFn, mkCons }:
      let
        inherit (self) u lam forall ann;

        nParams = builtins.length params;
        monoOf = markers:
          if indexed
          then self.datatypeI name (indexFn markers) (mkCons markers)
          else self.datatype  name (mkCons markers);
        # A parameter's `kind` is either a fixed Hoas (the common case,
        # e.g. `kind = u 0`) or a function from the list of
        # previously-bound parameter markers to a Hoas (e.g. for W-type's
        # `P : S → U` where `kind = ms: forall "_" (builtins.elemAt ms 0)
        # (_: u 0)`). This is the parameter-level analogue of `field` vs
        # `fieldD` and `piField` vs `piFieldD`: same "depends on prior
        # bindings" pattern, applied one scope outward.
        resolveKind = p: markers:
          if builtins.isFunction p.kind then p.kind markers else p.kind;
        overParams = mkBody:
          let go = i: markers:
            if i == nParams then mkBody markers
            else
              let p = builtins.elemAt params i; in
              lam p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [m]));
          in go 0 [];
        paramPi = mkBodyTy:
          let go = i: markers:
            if i == nParams then mkBodyTy markers
            else
              let p = builtins.elemAt params i; in
              forall p.name (resolveKind p markers) (m: go (i + 1) (markers ++ [m]));
          in go 0 [];
        polyField = fieldName:
          ann (overParams (markers:
                builtins.getAttr fieldName (monoOf markers)))
              (paramPi (markers:
                builtins.getAttr fieldName (monoOf markers)._tys));
        # Poly constructor wrapper: tagged `dt-ctor-poly` HOAS node
        # carrying the nParams/monoAt hook that `elaborate`'s `app` branch
        # uses to recognise saturated chains and flatten them into a flat
        # `desc-con` Tm. Non-saturated/non-chain uses elaborate via
        # `fallback` (the regular ann + overParams wrapping) and behave
        # identically to the pre-flattening code. For zero-field
        # constructors the fallback's inner body is the plain `descCon D
        # payload` HOAS; for fielded constructors it is the dt-ctor-mono
        # node's ann fallback.
        polyCtor = cName:
          ann (overParams (markers:
                let m = builtins.getAttr cName (monoOf markers); in
                if builtins.isAttrs m && m ? _htag && m._htag == "dt-ctor-mono"
                then m.fallback
                else m))
              (paramPi (markers:
                builtins.getAttr cName (monoOf markers)._tys));
        # Shallow probe: only c.name / f.name / f.kind are read. u 0 as a
        # dummy HOAS is structurally valid anywhere a type is expected;
        # field type expressions are never forced during the probe.
        dummyMarkers = map (_: u 0) params;
        probe = mkCons dummyMarkers;
        conNames = map (c: c.name) probe;
        # Eagerly validate shape (n=0, duplicate con names) at datatypeP time.
        _validate = builtins.seq (monoOf dummyMarkers).name null;
        # For each constructor name, expose a `dt-ctor-poly` tagged node
        # wrapping the polyCtor fallback. Keeps unsaturated uses identical
        # to the prior ann-lam cascade; enables the elaborate app-branch
        # to detect saturated chains and emit flat desc-con Tms for stack
        # safety on deep recursive values (5000+).
        mkPolyCtorNode = cName:
          let
            probeC = builtins.head (builtins.filter (c: c.name == cName) probe);
            nFields = builtins.length probeC.fields;
          in {
            _htag = "dt-ctor-poly";
            name = cName;
            inherit nParams;
            inherit nFields;
            fields = probeC.fields;
            # HOAS accessor: given a list of parameter HOAS args, produce
            # the mono constructor HOAS (a `dt-ctor-mono` tagged node for
            # fielded ctors, or a plain `descCon` HOAS for zero-field
            # ctors).
            monoAt = paramArgs: builtins.getAttr cName (monoOf paramArgs);
            # Fallback for non-saturated / non-chain uses.
            fallback = polyCtor cName;
          };
        ctorRecord = builtins.listToAttrs (map (cName: {
          name = cName;
          value = mkPolyCtorNode cName;
        }) conNames);
        # Polymorphic `_dtypeMeta`: `indexTy` depends on parameter
        # markers so it is not resolved here — consumers that need it
        # pass params through `indexFn` (stored alongside). Mono
        # datatypes expose `indexTy` directly.
        _dtypeMeta = {
          inherit name indexed;
          cons = map (c: {
            name = c.name;
            fields = map (f: { name = f.name; kind = f.kind; }) c.fields;
          }) probe;
        };
      in builtins.seq _validate (ctorRecord // {
        inherit name params;
        D    = polyField "D";
        # `T` carries `_dtypeMeta` so the elaborate-layer extract path can
        # peel an `app L.T A1 .. An` spine to find the polymorphic head
        # and recover constructor + field names for macro-generated VMu
        # values.
        T    = (polyField "T") // { inherit _dtypeMeta; };
        elim = polyField "elim";
        inherit _dtypeMeta;
        _cons = probe;
      });

    # ⊤-indexed polymorphic DataSpec. Each field of the output is an
    # `ann`-wrapped `λparams. monoField`. Constructors use `con`.
    datatypeP = name: params: mkCons:
      self._datatypePImpl {
        indexed = false;
        indexFn = _: self.unitPrim;
        inherit name params mkCons;
      };

    # Indexed polymorphic DataSpec. `indexFn : params → Hoas` produces
    # the index type from parameter markers; `mkCons` produces a list of
    # `conI`-tagged constructor specs.
    datatypePI = name: params: indexFn: mkCons:
      self._datatypePImpl {
        indexed = true;
        inherit name params indexFn mkCons;
      };

    # Macro-derived prelude datatypes. The surface `nat`, `listOf`, `sum`
    # and their introductions (`zero`, `succ`, `nil`, `cons`, `inl`,
    # `inr`) forward to fields of these specs; extract/reifyType detect
    # the μ-shape match and route decoding through the existing
    # nat/list/sum branches so reify-shape equivalence is preserved.
    NatDT =
      let inherit (self) datatype con recField; in
      datatype "Nat" [
        (con "zero" [])
        (con "succ" [ (recField "pred") ])
      ];

    ListDT =
      let inherit (self) datatypeP con field recField u; in
      datatypeP "List" [ { name = "A"; kind = u 0; } ] (ps:
        let A = builtins.elemAt ps 0; in [
          (con "nil"  [])
          (con "cons" [ (field "head" A) (recField "tail") ])
        ]);

    SumDT =
      let inherit (self) datatypeP con field u; in
      datatypeP "Sum"
        [ { name = "A"; kind = u 0; } { name = "B"; kind = u 0; } ]
        (ps: let A = builtins.elemAt ps 0; B = builtins.elemAt ps 1; in [
          (con "inl" [ (field "value" A) ])
          (con "inr" [ (field "value" B) ])
        ]);

    # Fin — monomorphic indexed datatype over Nat. Two constructors,
    # both with target index `succ m` carrying the index equality
    # through the ret-leaf. `Fin 0` is vacuous by construction; the
    # no-confusion discharge lives in `combinators.nix:absurdFin0`.
    FinDT =
      let inherit (self) datatypeI conI field recFieldAt nat succ; in
      datatypeI "Fin" nat [
        (conI "fzero" [ (field "m" nat) ]
          (p: succ p.m))
        (conI "fsuc"  [ (field "m" nat)
                        (recFieldAt "k" (p: p.m)) ]
          (p: succ p.m))
      ];

    # Vec — parametric indexed datatype `Vec A : Nat → U`. `vnil`
    # targets index `zero`; `vcons` targets `succ m` with the tail
    # at index `m`.
    VecDT =
      let inherit (self) datatypePI conI field recFieldAt u nat zero succ; in
      datatypePI "Vec"
        [ { name = "A"; kind = u 0; } ]
        (_: nat)
        (ps: let A = builtins.elemAt ps 0; in [
          (conI "vnil"  [] (_: zero))
          (conI "vcons"
            [ (field "m" nat)
              (field "x" A)
              (recFieldAt "xs" (p: p.m)) ]
            (p: succ p.m))
        ]);

    # Eq — parametric indexed datatype `Eq A a : A → U` with
    # parameter-dependent index type (`indexFn = ps: ps.A`). Single
    # constructor `refl` targets index `a`.
    EqDT =
      let inherit (self) datatypePI conI u; in
      datatypePI "Eq"
        [ { name = "A"; kind = u 0; }
          { name = "a"; kind = ms: builtins.elemAt ms 0; } ]
        (ps: builtins.elemAt ps 0)
        (ps: let a = builtins.elemAt ps 1; in [
          (conI "refl" [] (_: a))
        ]);

    # Surface forwarders onto the macro-derived prelude. `nat` is
    # `NatDT.T` directly — monomorphic `T` is a `"mu"` HOAS node carrying
    # `_dtypeMeta`. `listOf`/`sum` are spines of `app` over the
    # polymorphic `T`, keeping the parameter HOAS as a literal structural
    # slot. The un-reduced app form carries two pieces of information the
    # β-reduced `mu (listDesc A)` destroys: `_dtypeMeta` from the polyField
    # head and the parameter HOAS with any surface sugar intact
    # (`H.record`, `H.variant`, `H.maybe`). elaborateValue / validateValue
    # / extractInner all dispatch on the app-spine directly and never
    # round-trip through a kernel value to recover the parameter.
    nat = self.NatDT.T;
    listOf = A: self.app self.ListDT.T A;
    sum    = A: B: self.app (self.app self.SumDT.T A) B;

    # Macro-introduced constructors. `zero`/`nil`/`inl`/`inr` are spines
    # over the polymorphic `T` in `datatypeP`; `succ`/`cons` similarly
    # forward through the macro so the Nix-level surface stays unchanged
    # while the elaborated Tm flows through the `dt-ctor-mono` /
    # `dt-ctor-poly` chain-flatten path.
    zero = self.NatDT.zero;
    succ = h: self.app self.NatDT.succ h;
    nil = A: self.app self.ListDT.nil A;
    cons = A: h: t: self.app (self.app (self.app self.ListDT.cons A) h) t;
    inl = A: B: v: self.app (self.app (self.app self.SumDT.inl A) B) v;
    inr = A: B: v: self.app (self.app (self.app self.SumDT.inr A) B) v;
  };
  tests = {};
}
