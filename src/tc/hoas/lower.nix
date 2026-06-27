# HOAS → Tm lowering. `lower : Int → HoasTree → Tm` walks the
# intermediate HOAS tree built by the combinators / macro layer and emits
# de Bruijn indexed kernel terms. Binding chains (pi/sigma/lam/let), succ
# chains, and cons chains trampoline via `genericClosure` for stack safety
# to 8000+ depth. Macro-constructor applications route through
# `tryFlattenCtorChain` before the regular `app` case, collapsing
# saturated `dt-ctor-mono` / `dt-ctor-poly` spines into flat `desc-con`
# Tms.
#
# Also provides `checkHoas` / `inferHoas` wrappers around the kernel
# checker and the `natLit` helper for building S^n(zero).
{ self, fx, api, ... }:

let
  T = fx.tc.term;
  E = fx.tc.eval;
  CH = fx.tc.check;
  CHD = fx.tc.check.diag;
  meta = fx.tc.elaborate.meta;

  # List helpers — inline `take`/`drop` so this module does not need to
  # pull in nixpkgs `lib`.
  _listTake = n: xs:
    builtins.genList (i: builtins.elemAt xs i)
      (if n > builtins.length xs then builtins.length xs else n);
  _listDrop = n: xs:
    let len = builtins.length xs; in
    if n >= len then [ ]
    else builtins.genList (i: builtins.elemAt xs (n + i)) (len - n);

  # Depth budget for the native fast path of the structural walks below:
  # each recurses directly to this depth, then hands the remaining
  # sub-problem to a genericClosure worklist. The common shallow case
  # stays allocation-free; host-stack depth stays O(budget) on deep input.
  nativeWalkBudget = 512;

  # Peel an app-spine: walk outward while the node is an HOAS `app`,
  # returning `{ head; args = [arg_inner, ..., arg_outer]; }`. Ctor call
  # sites peel a fixed nParams + nFields, but `lower`'s app case peels the
  # whole user spine, so recurse directly for the common shallow case and
  # hand a deep left-nested `.fn` chain to a genericClosure worklist past
  # `nativeWalkBudget` — host-stack depth stays bounded.
  peelAppSpine = node: args: peelAppSpineGo nativeWalkBudget node args;

  peelAppSpineGo = fuel: node: args:
    if builtins.isAttrs node && node ? _htag && node._htag == "app"
    then
      if fuel <= 0 then peelAppSpineSlow node args
      else peelAppSpineGo (fuel - 1) node.fn ([ node.arg ] ++ args)
    else { head = node; inherit args; };

  peelAppSpineSlow = node0: args0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; node = node0; }];
        operator = item:
          if builtins.isAttrs item.node && item.node ? _htag && item.node._htag == "app"
          then [{ key = item.key + 1; node = item.node.fn; arg = item.node.arg; }]
          else [ ];
      };
      nArgs = builtins.length steps - 1;
      last = builtins.elemAt steps nArgs;
      # steps[1..] carry the `.arg` peeled to reach them, outer-to-inner;
      # emit them inner-to-outer (reverse) then append `args0` to match the
      # native `[node.arg] ++ args` accumulation — a single O(n) pass.
      peeled = builtins.genList (i: (builtins.elemAt steps (nArgs - i)).arg) nArgs ++ args0;
    in
    { head = last.node; args = peeled; };

  # Tm-level tag encoding via the first-class plus coproduct. Wraps
  # `payloadTm` with (n-1)-deep nested `mkBootInl L R …` / `mkBootInr L R …`
  # committing at position i out of n total. Mirrors the HOAS
  # `encodeTag` but operates on elaborated terms. `lTms`/`rTms` are
  # parallel lists of layer-k L/R type Tms — `lTms[k]` = interp of
  # summand k, `rTms[k]` = interp of the plus-tree of summands
  # k+1..n-1. For n=1 there is no prefix. Both lists must have length
  # >= 1 (caller guarantees via `n >= 2`).
  encodeTagTm = lTms: rTms: i: n: payloadTm:
    if n == 1 then payloadTm
    else
      let
        lTm = builtins.elemAt lTms 0;
        rTm = builtins.elemAt rTms 0;
      in
      if i == 0 then T.mkBootInl lTm rTm payloadTm
      else
        T.mkBootInr lTm rTm
          (encodeTagTm
            (_listDrop 1 lTms)
            (_listDrop 1 rTms)
            (i - 1)
            (n - 1)
            payloadTm);

  elaborateDescRef = depth: ref:
    ref // {
      I = lower depth ref.I;
      level = lowerLevel depth ref.level;
      params = map (lower depth) (ref.params or [ ]);
    };

  elaborateDescConCert = depth: cert:
    cert // {
      ref = elaborateDescRef depth cert.ref;
      target = lower depth cert.target;
    };

  appSpine = h: peelAppSpine h [ ];

  # Weak head normal form: β-reduces app-of-lam and δ-reduces surface
  # sugar nodes that carry an `_unfold` self-description. Sugar nodes
  # (`maybe`, `variant`, `thunk`) declare their μ-encoded expansion on
  # their own attrset; `hoasWhnf` is agnostic to the specific sugar
  # vocabulary. Consumers reading the head type former (`eqDTView`,
  # `dtypeView`, `elaborateForCheck`'s `tryFlattenCtorChainAt`) see the
  # same μ-form the kernel-side elaborator emits.
  # Call-by-name WHNF as a spine machine: `S` stacks the pending app
  # nodes (innermost on top). Peel an `app` head pushing the node,
  # β-reduce when the head is a `lam` and the stack is non-empty,
  # δ-unfold an `_unfold` node, else rebuild the spine with the reduced
  # head. Native to `nativeWalkBudget`; a deeper spine/β/δ chain hands
  # off to a genericClosure trampoline so host-stack depth stays bounded.
  # A type whose weak head is a deep neutral app-spine (`f a … a` under a
  # binder) drives the `.fn` peel one host frame per layer and overflows
  # the call stack past the ceiling without the handoff.
  hoasWhnf = h: hoasWhnfGo nativeWalkBudget h [ ];

  hoasWhnfGo = fuel: t: S:
    if !(builtins.isAttrs t && t ? _htag) then hoasWhnfRebuild t S
    else if t._htag == "app" then
      if fuel <= 0 then hoasWhnfSlow t S
      else hoasWhnfGo (fuel - 1) t.fn ([ t ] ++ S)
    else if t._htag == "lam" && S != [ ] then
      if fuel <= 0 then hoasWhnfSlow t S
      else hoasWhnfGo (fuel - 1) (t.body (builtins.head S).arg) (builtins.tail S)
    else if t ? _unfold then
      if fuel <= 0 then hoasWhnfSlow t S
      else hoasWhnfGo (fuel - 1) t._unfold S
    else hoasWhnfRebuild t S;

  # Rebuild outward from the settled head: each pending app node keeps its
  # fields with `fn` rewired to the reduced sub-head (matches the
  # recursive `h // { inherit fn; }`). `S` holds innermost first.
  hoasWhnfRebuild = t: S: builtins.foldl' (acc: a: a // { fn = acc; }) t S;

  # Deep-tail fallback for `hoasWhnfGo`: the same machine as a linear
  # genericClosure chain. `done` marks the settled head; the β step forces
  # its reduct into the key so the fold does not defer a step-deep chain.
  hoasWhnfSlow = t0: S0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; t = t0; S = S0; done = false; }];
        operator = item:
          if item.done then [ ]
          else if !(builtins.isAttrs item.t && item.t ? _htag) then
            [ (item // { key = item.key + 1; done = true; }) ]
          else if item.t._htag == "app" then
            [{ key = item.key + 1; t = item.t.fn; S = [ item.t ] ++ item.S; done = false; }]
          else if item.t._htag == "lam" && item.S != [ ] then
            let child = item.t.body (builtins.head item.S).arg; in
            [{ key = builtins.seq child (item.key + 1); t = child; S = builtins.tail item.S; done = false; }]
          else if item.t ? _unfold then
            [{ key = item.key + 1; t = item.t._unfold; inherit (item) S; done = false; }]
          else [ (item // { key = item.key + 1; done = true; }) ];
      };
      terminal = builtins.elemAt steps (builtins.length steps - 1);
    in hoasWhnfRebuild terminal.t terminal.S;

  eqDTView = h:
    let spine = appSpine (hoasWhnf h); in
    if builtins.isAttrs spine.head
      && spine.head ? _dtypeMeta
      && (spine.head._dtypeMeta.name or null) == "Eq"
      && builtins.length spine.args == 3
    then {
      A = builtins.elemAt spine.args 0;
      a = builtins.elemAt spine.args 1;
      b = builtins.elemAt spine.args 2;
    }
    else null;

  # When a checked type is a Π-telescope ending in a 3-arg `EqDT sort lhs
  # rhs` spine, the `vTy` and refl-conv builds in `checkHoas` each
  # re-derive the same three witness normal forms. Extract them once from
  # the checked Tm — eval'd under the telescope's neutral-binder env, the
  # way `extend` introduces binders — and share as lit-vals across both.
  # Sound: the witnesses are the checked type's own sub-Tms; wf is checked
  # on the unspliced Tm.

  # Each binder prepends `freshVar depth` (index 0 = innermost), matching
  # `extend`/`instantiateF`. Returns the terminal node, env, and depth.
  # Native to `nativeWalkBudget`; a deeper Π-telescope hands off to a
  # genericClosure worklist so host-stack depth stays bounded. The Tm this
  # descends is the kernel type-formation output — a lazy `mkPi` spine one
  # binder per level — so a native descent forces one thunk per host frame
  # and overflows on a deep telescope.
  peelTmTelescope = tm: env: depth:
    let
      go = fuel: t: e: d:
        if (t.tag or null) != "pi" then { node = t; env = e; depth = d; }
        else if fuel <= 0 then peelTmTelescopeSlow t e d
        else go (fuel - 1) t.codomain ([ (fx.tc.value.freshVar d) ] ++ e) (d + 1);
    in go nativeWalkBudget tm env depth;

  # genericClosure continuation: a linear chain peeling one Π binder per
  # step. The terminal node and its depth come from the last step; the
  # binder env is the freshVar run over `[startDepth, terminalDepth)`,
  # innermost (highest depth) first, matching the native prepend order.
  peelTmTelescopeSlow = tm0: env0: depth0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = depth0; tm = tm0; depth = depth0; }];
        operator = item:
          if (item.tm.tag or null) == "pi"
          then [{ key = item.depth + 1; tm = item.tm.codomain; depth = item.depth + 1; }]
          else [ ];
      };
      last = builtins.elemAt steps (builtins.length steps - 1);
      envTail = builtins.genList
        (i: fx.tc.value.freshVar (last.depth - 1 - i))
        (last.depth - depth0);
    in { node = last.tm; env = envTail ++ env0; depth = last.depth; };

  # Peel a Tm app-spine left-associatively: `app(app(app h a0) a1) a2`
  # ⇒ { head = h; args = [a0 a1 a2]; }.
  peelTmAppSpine = tm: acc:
    if (tm.tag or null) == "app"
    then peelTmAppSpine tm.fn ([ tm.arg ] ++ acc)
    else { head = tm; args = acc; };

  # Descend the HOAS Π-telescope to its body and return the `eqDTView`
  # (or null): the gate that confirms a checked 3-arg spine really is an
  # EqDT (head `_dtypeMeta.name == "Eq"`), not some other application.
  # The descent steps once per Π binder; recurse directly for the common
  # shallow case, then hand a deep telescope to a genericClosure worklist
  # so host-stack depth stays bounded.
  hoasEqBody = node: depth:
    let
      go = fuel: nd: d:
        let wh = hoasWhnf nd; in
        if (wh._htag or null) != "pi" then eqDTView wh
        else if fuel <= 0 then hoasEqBodySlow nd d
        else go (fuel - 1) (wh.body (self.litVal (fx.tc.value.freshVar d))) (d + 1);
    in go nativeWalkBudget node depth;

  hoasEqBodySlow = node0: depth0:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; node = node0; depth = depth0; }];
        operator = item:
          let wh = hoasWhnf item.node; in
          if (wh._htag or null) == "pi"
          then
            let child = wh.body (self.litVal (fx.tc.value.freshVar item.depth)); in
            [{ key = builtins.seq child (item.key + 1); node = child; depth = item.depth + 1; }]
          else [ ];
      };
      terminal = builtins.elemAt steps (builtins.length steps - 1);
    in
    eqDTView (hoasWhnf terminal.node);

  # If the checked `ty` is a Π-telescope ending in a 3-arg spine, eval its
  # sort/lhs/rhs sub-Tms ONCE under the telescope env; else null.
  checkedEqWitnesses = ty:
    let
      p = peelTmTelescope ty [ ] 0;
      body = if (p.node.tag or null) == "ann" then p.node.term else p.node;
      s = peelTmAppSpine body [ ];
    in
    if (body.tag or null) == "app" && builtins.length s.args == 3
    then {
      sort = E.eval p.env (builtins.elemAt s.args 0);
      lhs = E.eval p.env (builtins.elemAt s.args 1);
      rhs = E.eval p.env (builtins.elemAt s.args 2);
    }
    else null;

  # Rebuild the checked Π-telescope Tm with the terminal Eq spine's three
  # args replaced by the shared lit-vals — feeds `vTy` without re-deriving
  # the NFs (the spine head, carrying the EqDT constructor, is preserved).
  spliceTmEqWitnesses = ty: w:
    let
      go = tm:
        if (tm.tag or null) == "pi"
        then tm // { codomain = go tm.codomain; }
        else
          let
            isAnn = (tm.tag or null) == "ann";
            body = if isAnn then tm.term else tm;
            s = peelTmAppSpine body [ ];
            rebuilt = T.mkApp
              (T.mkApp (T.mkApp s.head (T.mkLitVal w.sort)) (T.mkLitVal w.lhs))
              (T.mkLitVal w.rhs);
          in
          if isAnn then tm // { term = rebuilt; } else rebuilt;
    in
    go ty;

  # Rebuild the HOAS Π-telescope with the terminal Eq body replaced by the
  # shared lit-val witnesses — feeds the refl-conv `elaborateForCheck`.
  spliceHoasEqWitnesses = h: w:
    let
      go = node:
        let wh = hoasWhnf node; in
        if (wh._htag or null) == "pi"
        then wh // { body = v: go (wh.body v); }
        else
          let ev = eqDTView wh; in
          if ev == null then node
          else self.eq (self.litVal w.sort) (self.litVal w.lhs) (self.litVal w.rhs);
    in
    go h;

  sameHoas = a: b:
    let r = builtins.tryEval (a == b); in
    r.success && r.value;

  dtypeView = h:
    let
      spine = peelAppSpine (hoasWhnf h) [ ];
      head = spine.head;
    in
    if builtins.isAttrs head
      && (head._htag or null) == "mu"
      && builtins.length spine.args == 0
      && builtins.isAttrs head.D
      && head.D ? _descRef
    then {
      meta = head.D._descRef;
      name = head.D._descRef.name;
      params = head.D._descRef.params or [ ];
      index = head.i;
    }
    else if builtins.isAttrs head && head ? _dtypeMeta then
      let
        meta = head._dtypeMeta;
        nParams = builtins.length (meta.params or [ ]);
        indexed = meta.indexed or false;
        expectedArgs = nParams + (if indexed then 1 else 0);
      in
      if builtins.length spine.args != expectedArgs then null
      else {
        inherit meta;
        name = meta.name;
        params = _listTake nParams spine.args;
        index =
          if indexed
          then builtins.elemAt spine.args nParams
          else self.ttPrim;
      }
    else null;

  fieldTyOf = mono: f: prev:
    stripAnnTy (
      if f.kind == "data" then f.type
      else if f.kind == "dataD" then f.typeFn prev
      else if f.kind == "recAt" then self.muI mono.I mono.dHoas (f.idxFn prev)
      else if f.kind == "pi" || f.kind == "piAt" then f.S
      else if f.kind == "piD" || f.kind == "piDAt" then f.SFn prev
      else throw "hoas.lower: unknown datatype field kind '${f.kind}'");

  # Strip `ann` off a field type. Parametric `monoAt` ascribes substituted
  # params against their kind (`ann (listOf string) (u 0)`), hiding the former
  # from consumers that inspect it. Applied in `fieldTyOf` so all readers see
  # through it; never in `hoasWhnf` (conv needs its `ann` boundaries).
  stripAnnTy = ty:
    if builtins.isAttrs ty && (ty._htag or null) == "ann"
    then stripAnnTy ty.term
    else ty;

  fieldMarkers = fields:
    builtins.genList
      (i:
        let f = builtins.elemAt fields i; in
        { _signatureField = true; inherit (f) name; index = i; })
      (builtins.length fields);

  prevFromMarkers = fields: markers:
    builtins.foldl'
      (acc: i:
        let f = builtins.elemAt fields i; in
        if f.kind == "data" || f.kind == "dataD"
        then acc // { ${f.name} = builtins.elemAt markers i; }
        else acc)
      { }
      (builtins.genList (x: x) (builtins.length fields));

  mergeMatch = left: right:
    if left == null || right == null then null
    else
      builtins.foldl'
        (acc: name:
          if acc == null then null
          else if acc ? ${name} && !(sameHoas acc.${name} right.${name})
          then null
          else acc // { ${name} = right.${name}; })
        left
        (builtins.attrNames right);

  matchForcedPattern = pattern: target:
    if builtins.isAttrs pattern && (pattern._signatureField or false) then
      { ${pattern.name} = target; }
    else if builtins.isAttrs pattern
      && builtins.isAttrs target
      && (pattern._htag or null) == "app"
      && (target._htag or null) == "app"
    then
      mergeMatch
        (matchForcedPattern pattern.fn target.fn)
        (matchForcedPattern pattern.arg target.arg)
    else if builtins.isAttrs pattern
      && builtins.isAttrs target
      && (pattern._htag or null) == "pair"
      && (target._htag or null) == "pair"
    then
      mergeMatch
        (matchForcedPattern pattern.fst target.fst)
        (matchForcedPattern pattern.snd target.snd)
    else if sameHoas pattern target then { }
    else null;

  forcedBindingsFromTarget = mono: expectedIndex:
    let
      markers = fieldMarkers mono.fields;
      prev = prevFromMarkers mono.fields markers;
    in
    matchForcedPattern (mono.targetIdx prev) expectedIndex;

  completeForcedFieldArgs = mono: expectedIndex: fieldArgs:
    if builtins.length fieldArgs == mono.nFields then fieldArgs
    else
      let
        forced = self.forcedFieldSet {
          fields = mono.fields;
          targetIdx = mono.targetIdx;
          fieldTyOf = fieldTyOf mono;
        };
        bindings = forcedBindingsFromTarget mono expectedIndex;
        go = i: argIx:
          if i == mono.nFields then
            if argIx == builtins.length fieldArgs then [ ] else null
          else
            let
              f = builtins.elemAt mono.fields i;
              isForced = forced.${f.name} or false;
              rest = nextArgIx:
                let tail = go (i + 1) nextArgIx; in
                if tail == null then null else tail;
            in
            if isForced then
              if bindings == null || !(bindings ? ${f.name}) then null
              else
                let tail = rest argIx; in
                if tail == null then null else [ bindings.${f.name} ] ++ tail
            else if argIx >= builtins.length fieldArgs then null
            else
              let tail = rest (argIx + 1); in
              if tail == null then null else [ (builtins.elemAt fieldArgs argIx) ] ++ tail;
      in
      go 0 0;

  applyHoasArgs = fn: args:
    builtins.foldl' (acc: arg: self.app acc arg) fn args;

  elaborateCtorChecked = depth: mono: fieldArgs:
    let
      go = i: prev: acc:
        if i == builtins.length fieldArgs then acc
        else
          let
            f = builtins.elemAt mono.fields i;
            arg = builtins.elemAt fieldArgs i;
            argTm = elaborateForCheck depth (fieldTyOf mono f prev) arg;
            prev' =
              if f.kind == "data" || f.kind == "dataD"
              then prev // { ${f.name} = arg; }
              else prev;
          in
          go (i + 1) prev' (T.mkApp acc argTm);
    in
    go 0 { } (lower depth mono);

  elaborateForCheck = depth: hoasTy: hoasTm:
    let
      whTy = hoasWhnf hoasTy;
      eqView = eqDTView whTy;
      # Type-directed ctor-chain flatten: recovers param args from the
      # expected type when the term spine no longer carries them.
      ctorFlat = tryFlattenCtorChainAt depth whTy hoasTm;
    in
    if builtins.isAttrs hoasTm
      && hoasTm ? _htag
      && hoasTm._htag == "refl"
      && eqView != null
    then lower depth (self.reflDT eqView.A eqView.a)
    else if ctorFlat != null then ctorFlat
    else if builtins.isAttrs whTy
      && whTy ? _htag
      && whTy._htag == "sigma"
      && builtins.isAttrs hoasTm
      && hoasTm ? _htag
      && hoasTm._htag == "pair"
    then
      T.mkPair
        (elaborateForCheck depth whTy.fst hoasTm.fst)
        (elaborateForCheck depth (whTy.body hoasTm.fst) hoasTm.snd)
    else if builtins.isAttrs whTy
      && whTy ? _htag
      && whTy._htag == "pi"
      && builtins.isAttrs hoasTm
      && hoasTm ? _htag
      && hoasTm._htag == "lam"
    then
      let marker = self.mkMarker depth; in
      T.mkLam hoasTm.name (lower depth whTy.domain)
        (elaborateForCheck (depth + 1) (whTy.body marker) (hoasTm.body marker))
    else if builtins.isAttrs hoasTm
      && hoasTm ? _htag
      && hoasTm._htag == "let"
    then
      let marker = self.mkMarker depth; in
      T.mkLet hoasTm.name
        (lower depth hoasTm.type)
        (elaborateForCheck depth hoasTm.type hoasTm.val)
        (elaborateForCheck (depth + 1) hoasTy (hoasTm.body marker))
    else lower depth hoasTm;

  # Build per-layer L/R interp Tm lists for a plus-spine of n summands
  # over index type `I`. Given the outer mu's description HOAS
  # `dHoasOuter`, the target index HOAS `targetIdxVal`, and the
  # per-summand HOAS descriptions `descsHoas`, emits
  #   lTms[k] = mkInterpD level I (descsHoas[k]) muFam targetIdxVal
  #   rTms[k] = mkInterpD level I (spineAfter (k+1)) muFam targetIdxVal  (k in 0..n-2)
  # where `muFam = λi:I. μ I dHoasOuter i`. Used by the datatype-macro
  # flatten path with `I`/`targetIdxVal` read off the ctor spec.
  # n must be >= 1.
  buildTagInterpTms = depth: level: I: dHoasOuter: targetIdxVal: descsHoas:
    let
      n = builtins.length descsHoas;
      muFam = self.lam "_i" I (iArg:
        self.muI I dHoasOuter iArg);
      # Plus-spine of summands k..n-1. Requires remaining >= 1.
      spineAfter = k:
        let remaining = n - k; in
        if remaining == 1 then builtins.elemAt descsHoas k
        else self.plusI I level (builtins.elemAt descsHoas k) (spineAfter (k + 1));
      interpTm = dHoas:
        lower depth
          (self.interpD level I dHoas muFam targetIdxVal);
    in
    {
      lTms = builtins.genList (k: interpTm (builtins.elemAt descsHoas k)) n;
      rTms = builtins.genList (k: interpTm (spineAfter (k + 1)))
        (if n >= 2 then n - 1 else 0);
    };

  # Classify a field list into a chain-flatten profile, or null if
  # neither shape applies.
  #   - "saturated": all fields are non-recursive. Emits a single flat
  #     `desc-con` whose payload is the right-nested pair of field Tms
  #     terminated with `tt`. No chain-walking.
  #   - "recursive": exactly one rec at the tail, every other field data.
  #     Walks a chain along the rec arg via `genericClosure` and emits a
  #     layered `desc-con` pyramid with a shared dTm across layers.
  # A trailing-rec ctor with zero data fields (e.g. `succ`, whose single
  # field is `rec`) is classified as "recursive" with `nData = 0`. A ctor
  # with zero fields is handled separately at the `tryFlattenCtorChain`
  # poly-branch via the `mono._htag == "desc-con"` short-circuit; both
  # profiles require `n >= 1` here.
  ctorShape = fields:
    let
      n = builtins.length fields;
      isData = f: f.kind == "data" || f.kind == "dataD";
      isNonRec = f: f.kind != "recAt";
      initsAllData = nInits:
        builtins.foldl'
          (ok: j: ok && isData (builtins.elemAt fields j))
          true
          (builtins.genList (x: x) nInits);
      allNonRec =
        n >= 1 && builtins.foldl'
          (ok: j: ok && isNonRec (builtins.elemAt fields j))
          true
          (builtins.genList (x: x) n);
      lastRec =
        n >= 1
        && (builtins.elemAt fields (n - 1)).kind == "recAt"
        && initsAllData (n - 1);
    in
    if lastRec then { kind = "recursive"; }
    else if allNonRec then { kind = "saturated"; }
    else null;

  # Macro-constructor chain flattening.
  #
  # The datatype macro emits fielded constructor terms as curried
  # λ-cascades wrapped in `ann`. A deeply-applied chain (e.g. a
  # 5000-element cons list) would elaborate to a 5000-deep `app`-tree Tm,
  # which blows the C++ stack on `infer`'s linear recursion.
  # `tryFlattenCtorChain` peels spines whose head is tagged
  # `dt-ctor-mono` or `dt-ctor-poly` and emits a flat `desc-con` Tm — a
  # single layer for non-recursive ctors (sum's `inl`/`inr`), a
  # `genericClosure`-walked pyramid for the list/nat-style `recursive`
  # shape.
  #
  # Chain-flatten precondition: one of two shapes per `ctorShape`:
  #   - "saturated": no field is recursive. Emits one flat `desc-con`.
  #   - "recursive": exactly one `rec` at the tail, every other field
  #     `data`. Aligns with the kernel's desc-con trampoline acceptance
  #     condition via `linearProfile`. Walks the chain along the rec tail.
  # Zero-field constructors never produce a `dt-ctor-mono` node — mkCtor
  # returns a plain `desc-con` HOAS with the tag-encoded payload baked
  # in. The poly-branch of `tryFlattenCtorChain` elaborates that mono
  # directly. Ctors outside either shape (tree's `node` with two recs,
  # dataD/piD-dependent fields) decline and the fallback
  # `ann (lam-cascade)` path handles the application normally.
  tryFlattenCtorChain = depth: h:
    let
      outer = peelAppSpine h [ ];
      head = outer.head;
      args = outer.args;
    in
    if !(builtins.isAttrs head && head ? _htag) then null
    else if head._htag == "dt-ctor-mono" then
      flattenCtor depth head null [ ] args true
    else if head._htag == "dt-ctor-poly" then
      let nP = head.nParams; in
      if builtins.length args < nP then null
      else
        let
          paramArgs = _listTake nP args;
          fieldArgs = _listDrop nP args;
          mono = head.monoAt paramArgs;
        in
        if !(builtins.isAttrs mono) || !(mono ? _htag) then null
        # Fielded ctors: mono is a `dt-ctor-mono` node; pass to the
        # shape-classified flattener.
        else if mono._htag == "dt-ctor-mono"
        then flattenCtor depth mono head paramArgs fieldArgs true
        # Zero-field ctors: `mkCtor` returns a plain `desc-con` HOAS
        # (no lam cascade, no tag). Elaborating it directly yields a
        # flat `desc-con` Tm with the parameter-instantiated D baked
        # in.
        else if mono._htag == "desc-con"
          && builtins.length fieldArgs == 0
        then lower depth mono
        else null
    else null;

  # Type-directed chain flattening for post-implicit-promotion spines:
  # the term spine carries only field args (param positions have been
  # forced and dropped); param args are recovered from the expected
  # type's HOAS spine. Match condition: spine head of `whTy` carries a
  # `_dtypeMeta.name` equal to the polyCtor's `_dtypeName`.
  tryFlattenCtorChainAt = depth: whTy: h:
    let
      outer = peelAppSpine h [ ];
      head = outer.head;
      fieldArgs = outer.args;
      ty = dtypeView whTy;
    in
    if !(builtins.isAttrs head && head ? _htag) then null
    else if ty == null then null
    else if head._htag == "dt-ctor-mono" then
      if (head.descRef.name or null) != ty.name then null
      else
        let fullFieldArgs = completeForcedFieldArgs head ty.index fieldArgs; in
        if fullFieldArgs == null then null
        else
          let flat = flattenCtor depth head null [ ] fullFieldArgs false; in
          if flat != null then flat
          else elaborateCtorChecked depth head fullFieldArgs
    else if head._htag == "dt-ctor-poly" && head ? _dtypeName then
      if ty.name != head._dtypeName || builtins.length ty.params != head.nParams
      then null
      else
        let mono = head.monoAt ty.params; in
        if !(builtins.isAttrs mono) || !(mono ? _htag) then null
        else if mono._htag == "dt-ctor-mono" then
          let fullFieldArgs = completeForcedFieldArgs mono ty.index fieldArgs; in
          if fullFieldArgs == null then null
          else
            let flat = flattenCtor depth mono head ty.params fullFieldArgs false; in
            if flat != null then flat
            else elaborateCtorChecked depth mono fullFieldArgs
        else if mono._htag == "desc-con" && builtins.length fieldArgs == 0
        then lower depth mono
        else null
    else null;

  # Chain-flatten dispatcher. `polyHead` is non-null for poly chains
  # (used in the recursive branch to verify each successor layer uses
  # the *same* poly ctor with the *same* param args; structural `==` on
  # HOAS param args suffices because the test site passes the same
  # references at every layer). `paramArgsInSpine` selects the layer
  # match: `true` expects `nParams + nFields` args per layer (params
  # threaded through the spine, pre-implicit-promotion form); `false`
  # expects `nFields` args per layer with `paramArgs` constant across
  # layers (recovered from expected type, post-promotion form).
  flattenCtor = depth: mono: polyHead: paramArgs: fieldArgs: paramArgsInSpine:
    let
      nFields = mono.nFields;
      shape = ctorShape mono.fields;
    in
    if builtins.length fieldArgs != nFields || shape == null then null
    else
      let
        dTm = lower depth mono.dHoas;
        descLevel = mono.descLevel or 0;
        ctorIdx = mono.ctorIndex;
        nCtors = mono.nCtors;
        I = mono.I;
        # Rebuild the `prev` attrset required by `mono.targetIdx` from an
        # ordered list of HOAS field-arg nodes. Positions line up with
        # `mono.fields`; only data/dataD entries contribute. Under the
        # ctorShape precondition, `data` fields populate every position
        # used to compute targetIdx (the ⊤-sugar and `datatypeI`'s
        # targetIdx function close only over data-level markers).
        prevOfArgs = args:
          builtins.foldl'
            (acc: idx:
              let f = builtins.elemAt mono.fields idx; in
              if f.kind == "data" || f.kind == "dataD"
              then acc // { ${f.name} = builtins.elemAt args idx; }
              else acc)
            { }
            (builtins.genList (x: x) (builtins.length args));
        # Lower each field arg to its payload Tm. data/dataD payloads are
        # unannotated value-lifts (fieldPayloadValue), so inferring them would
        # reject checkable-but-not-inferable args (bare cons/nil, unannotated
        # lambdas): the head would land in the element-type slot. Elaborate them
        # against the lifted field type so nested type-directed constructors
        # recover their params. Inferable payloads fall through elaborateForCheck
        # to plain `lower` (identical Tm); pi payloads are already ann-wrapped by
        # fieldPayloadValue, so they keep `lower` too.
        payloadCheckedTms = args:
          let
            go = idx: prev:
              if idx == builtins.length args then [ ]
              else
                let
                  f = builtins.elemAt mono.fields idx;
                  arg = builtins.elemAt args idx;
                  payload = self.fieldPayloadValue I mono.dHoas descLevel f prev arg;
                  tm =
                    if f.kind == "data" || f.kind == "dataD"
                    then elaborateForCheck depth
                      (self.fieldLiftType f descLevel
                        (fieldTyOf mono f prev))
                      payload
                    else lower depth payload;
                  prev' =
                    if f.kind == "data" || f.kind == "dataD"
                    then prev // { ${f.name} = arg; }
                    else prev;
                in
                [ tm ] ++ go (idx + 1) prev';
          in
          go 0 { };
        # Under the ⊤-sugar path (`datatype` / `datatypeP`), every
        # `targetIdx` is `_: ttPrim` regardless of `prev`, so the tags
        # are invariant across chain layers and can be shared. Detect
        # that case via `I`'s HOAS tag and precompute once; at I ≠ ⊤,
        # tags depend on each layer's `targetIdx prev` and are
        # recomputed per layer.
        isUnitI = (I._htag or null) == "unit";
        sharedTags =
          if isUnitI && nCtors >= 2
          then buildTagInterpTms depth descLevel I mono.dHoas self.ttPrim mono.conDescs
          else null;
        mkTags = targetIdxHoas:
          if sharedTags != null then sharedTags
          else if nCtors >= 2
          then buildTagInterpTms depth descLevel I mono.dHoas targetIdxHoas mono.conDescs
          else { lTms = [ ]; rTms = [ ]; };
      in
      if shape.kind == "saturated" then
      # No recursion: build one payload from the field Tms.
      #   descCon dTm tIdx (encodeTag i n (pair d_0 (pair d_1 (… (pair d_{n-1} refl) …))))
      # The innermost payload component inhabits `Eq I j i` at the
      # ret-leaf with `j = targetIdx prev`; refl witnesses it.
        let
          prev = prevOfArgs fieldArgs;
          targetIdxHoas = mono.targetIdx prev;
          targetIdxTm = lower depth targetIdxHoas;
          dataTms = payloadCheckedTms fieldArgs;
          leafTm = lower depth (self.payloadLeafAt I descLevel targetIdxHoas);
          tags = mkTags targetIdxHoas;
          payload = builtins.foldl'
            (acc: j:
              let d = builtins.elemAt dataTms (nFields - 1 - j);
              in T.mkPair d acc)
            leafTm
            (builtins.genList (x: x) nFields);
          cert =
            if mono ? descRef then {
              kind = "datatype-con-payload";
              ref = elaborateDescRef depth mono.descRef;
              target = targetIdxTm;
              ctor = ctorIdx;
              fieldCount = nFields;
            } else null;
          payloadTm = encodeTagTm tags.lTms tags.rTms ctorIdx nCtors payload;
        in
        if cert == null
        then T.mkDescCon dTm targetIdxTm payloadTm
        else T.mkDescConWithCert dTm targetIdxTm payloadTm cert
      else
        let
          recArg = builtins.elemAt fieldArgs (nFields - 1);
          nonRecArgs = _listTake (nFields - 1) fieldArgs;
          # Try to recognise a successor layer: peel an app spine and
          # require the head to be the same `mono` (mono chains) or the
          # same `polyHead` (poly chains). For poly chains, `paramArgsInSpine`
          # selects whether the layer carries params in the spine
          # (`pa != paramArgs` check) or only field args (constant params).
          tryNext = node:
            let sp = peelAppSpine node [ ]; in
            if !(builtins.isAttrs sp.head && sp.head ? _htag) then null
            else if polyHead == null then
              if sp.head != mono then null
              else if builtins.length sp.args != nFields then null
              else {
                nonRec = _listTake (nFields - 1) sp.args;
                recArg = builtins.elemAt sp.args (nFields - 1);
              }
            else if paramArgsInSpine then
              if sp.head != polyHead then null
              else if builtins.length sp.args != polyHead.nParams + nFields then null
              else
                let
                  pa = _listTake polyHead.nParams sp.args;
                  fa = _listDrop polyHead.nParams sp.args;
                in
                if pa != paramArgs then null
                else {
                  nonRec = _listTake (nFields - 1) fa;
                  recArg = builtins.elemAt fa (nFields - 1);
                }
            else
              if sp.head != polyHead then null
              else if builtins.length sp.args != nFields then null
              else {
                nonRec = _listTake (nFields - 1) sp.args;
                recArg = builtins.elemAt sp.args (nFields - 1);
              };
          # Start the chain at the given layer. `genericClosure` walks
          # along `recArg` as long as each tail peels to a matching
          # successor.
          startLayer = { inherit nonRecArgs recArg; };
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = startLayer; }];
            operator = item:
              let nxt = tryNext item.val.recArg; in
              if nxt == null then [ ]
              else [{
                key = item.key + 1;
                val = { nonRecArgs = nxt.nonRec; recArg = nxt.recArg; };
              }];
          };
          nLayers = builtins.length chain;
          # Sharing-aware validation: when the field kinds are simple
          # `data` (so `f.type` is a constant HOAS type), pre-check the
          # outermost layer's field Tms once at `CH.emptyCtx`. Each layer
          # whose non-rec args are Nix-equal to that representative then
          # carries `validatedFields.validated = true` on its own cert;
          # layers with different args keep the bare cert and take the
          # kernel check, so one odd element costs one slow layer rather
          # than unvalidating the whole chain. The kernel trampoline
          # trusts an attestation only when its own ctx is also empty
          # (the `H.checkHoas` boundary). Sound by referential
          # transparency of `check`: the elaborator's pre-check IS the
          # kernel checker; same `(ctx, tm, ty)` triple → same result.
          nNonRec = nFields - 1;
          repArgs = (builtins.elemAt chain 0).val.nonRecArgs;
          repValidated =
            let
              dataAt = j:
                (builtins.elemAt mono.fields j).kind == "data";
              eligible =
                depth == 0
                && nLayers >= 2
                && nNonRec >= 1
                && mono ? descRef
                && builtins.all dataAt (builtins.genList (x: x) nNonRec);
            in
            if !eligible then false
            else
              let
                preElabPayloadTms = payloadCheckedTms repArgs;
                checks = builtins.genList
                  (j:
                    let
                      f = builtins.elemAt mono.fields j;
                      vTy = E.eval [ ] (lower depth f.type);
                      tm = builtins.elemAt preElabPayloadTms j;
                      res = CH.checkTm CH.emptyCtx tm vTy;
                    in
                    res ? tag)
                  nNonRec;
              in
              builtins.all (x: x) checks;
          layerValidated = args: repValidated && args == repArgs;
          # Shared so per-layer certs don't allocate a fresh attestation set.
          fieldsAttested = { validated = true; };
          fieldsUnattested = { validated = false; };
          innermost = (builtins.elemAt chain (nLayers - 1)).val;
          # Base: whatever the innermost layer's `recArg` points to (the
          # first non-chain-successor tail).
          #
          # Pre-phase-1c (paramArgsInSpine = true): the rec arg carried its
          # params in the spine (e.g. `nil A`). `lower`'s `app` branch
          # would re-enter `tryFlattenCtorChain` on the rec arg's app spine
          # and flatten it. Plain `lower` is correct here.
          #
          # Post-phase-1c (paramArgsInSpine = false): the rec arg is a bare
          # `dt-ctor-poly`/`dt-ctor-mono` HOAS node. `lower` falls
          # through `t == "dt-ctor-poly"` to `h.fallback`, synthesising an
          # `ann (lam-cascade)` of Pi type — which the kernel desc-con
          # check rule rejects against the rec field's `μ I D i_rec`
          # expected type. Route the rec arg through `elaborateForCheck`
          # at the rec field's per-layer expected type so the bare polyCtor
          # gets type-directed flattening (matching the (5δ) treatment of
          # the outer ctor).
          recField = builtins.elemAt mono.fields (nFields - 1);
          innermostPrev = prevOfArgs innermost.nonRecArgs;
          recCarrierTy = self.muI mono.I mono.dHoas (recField.idxFn innermostPrev);
          baseFlat =
            if paramArgsInSpine then null
            else
              let
                baseSp = peelAppSpine innermost.recArg [ ];
              in
              if polyHead != null
                && builtins.isAttrs baseSp.head
                && (baseSp.head._htag or null) == "dt-ctor-poly"
                && (baseSp.head._dtypeName or null) == (polyHead._dtypeName or null)
                && baseSp.head.nParams == builtins.length paramArgs
                && builtins.length baseSp.args == baseSp.head.nFields
              then
                let baseMono = baseSp.head.monoAt paramArgs; in
                if builtins.isAttrs baseMono && (baseMono._htag or null) == "dt-ctor-mono"
                then flattenCtor depth baseMono baseSp.head paramArgs baseSp.args false
                else if builtins.isAttrs baseMono
                  && (baseMono._htag or null) == "desc-con"
                  && baseSp.head.nFields == 0
                then lower depth baseMono
                else null
              else null;
          baseTm =
            if paramArgsInSpine
            then lower depth innermost.recArg
            else if baseFlat != null
            then baseFlat
            else elaborateForCheck depth recCarrierTy innermost.recArg;
          # Build one layer's payload from its non-rec HOAS field args and
          # a tail accumulator. Field args line up positionally with
          # `mono.fields[0..nFields-2]` (the rec field is at the end);
          # `prevOfArgs` extracts the data markers needed by `targetIdx`.
          # The innermost pair terminator is `Refl : Eq I j j` where
          # `j = targetIdx prev` for this layer.
          buildLayer = nonRecHoasArgs: accTm:
            let
              prev = prevOfArgs nonRecHoasArgs;
              targetIdxHoas = mono.targetIdx prev;
              targetIdxTm = lower depth targetIdxHoas;
              nonRecTms = payloadCheckedTms nonRecHoasArgs;
              leafTm = lower depth (self.payloadLeafAt I descLevel targetIdxHoas);
              tags = mkTags targetIdxHoas;
              innerMost = T.mkPair accTm leafTm;
              payloadInner = builtins.foldl'
                (acc: j:
                  let f = builtins.elemAt nonRecTms (builtins.length nonRecTms - 1 - j);
                  in T.mkPair f acc)
                innerMost
                (builtins.genList (x: x) (builtins.length nonRecTms));
              cert =
                if mono ? descRef then {
                  kind = "datatype-con-payload";
                  ref = elaborateDescRef depth mono.descRef;
                  target = targetIdxTm;
                  ctor = ctorIdx;
                  fieldCount = builtins.length nonRecHoasArgs + 1;
                  validatedFields =
                    if layerValidated nonRecHoasArgs
                    then fieldsAttested
                    else fieldsUnattested;
                } else null;
              payloadTm = encodeTagTm tags.lTms tags.rTms ctorIdx nCtors payloadInner;
            in
            if cert == null
            then T.mkDescCon dTm targetIdxTm payloadTm
            else T.mkDescConWithCert dTm targetIdxTm payloadTm cert;
        in
        # Fold inward-to-outward: step idx=0 wraps baseTm with the
          # innermost layer's non-rec args, step idx=1 with the next layer
          # out, etc.
        builtins.foldl'
          (acc: idx:
            buildLayer (builtins.elemAt chain (nLayers - 1 - idx)).val.nonRecArgs acc)
          baseTm
          (builtins.genList (x: x) nLayers);

  # Universe-level coercion. The HOAS surface accepts a level slot in
  # one of two encodings:
  #   - a Nix-meta `Int` (concrete level, shimmed via `T.mkLevelLit`);
  #   - a HOAS Level term — either an `_htag`-tagged construct
  #     (`level`/`levelZero`/`levelSuc`/`levelMax`) or a `_hoas`-tagged
  #     marker for a bound `forall "k" level …` variable. Both route
  #     through `lower`, whose first dispatch already handles
  #     markers (→ `T.mkVar`) and `_htag` nodes uniformly.
  # Anything else is a typed error at this boundary so a leaked marker
  # or random attrset fails loudly here rather than corrupting the
  # kernel tree downstream.
  lowerLevel = depth: lvl:
    if builtins.isInt lvl then T.mkLevelLit lvl
    else if self.isMarker lvl || (builtins.isAttrs lvl && lvl ? _htag)
    then lower depth lvl
    else
      throw "hoas.lower.level: expected Int or HOAS Level; got ${
      if builtins.isAttrs lvl
      then "attrset with keys: ${builtins.concatStringsSep ", " (builtins.attrNames lvl)}"
      else builtins.typeOf lvl
    }";

  # Inverse of `lowerLevel`: a kernel Level Value back to a HOAS
  # Level node. Concrete chains map to the `levelZero`/`levelSuc`
  # combinators; `vLevelMax` reifies recursively; a neutral `vNe`
  # (a bound Level variable in the surrounding context) reifies to a
  # marker at the same de Bruijn level so that re-elaborating the
  # produced HOAS under a context that re-introduces the binder yields
  # back the same kernel Var. Levels are not function-typed, so any
  # `vNe` with a non-empty spine is a kernel invariant violation.
  reifyLevel = lv:
    if lv.tag == "VLevelZero" then self.levelZero
    else if lv.tag == "VLevelSuc" then self.levelSuc (self.reifyLevel lv.pred)
    else if lv.tag == "VLevelMax" then
      self.levelMax (self.reifyLevel lv.lhs) (self.reifyLevel lv.rhs)
    else if lv.tag == "VNe" then
      if lv.spine == [ ] then self.mkMarker lv.level
      else throw "hoas.reifyLevel: VNe Level with non-empty spine — Levels are not function-typed"
    else throw "hoas.reifyLevel: unsupported Level value tag '${lv.tag or "?"}'";

  # Lowering: HOAS tree → de Bruijn Tm.
  #
  # lower : Int → HoasTree → Tm
  # depth tracks the current binding depth. When we encounter a binding
  # combinator (pi, lam, sigma, let), we:
  #   1. Apply the stored Nix lambda to mkMarker(depth)
  #   2. Recursively lower the resulting body at depth+1
  #   3. Markers with level L become T.mkVar(depth - L - 1)
  lower = depth: h:
    # Marker → variable
    if self.isMarker h then
      T.mkVar (depth - h.level - 1)

    else if !(builtins.isAttrs h) || !(h ? _htag) then
      let
        desc =
          if builtins.isAttrs h
          then "attrset with keys: ${builtins.concatStringsSep ", " (builtins.attrNames h)}"
          else builtins.typeOf h;
      in
      throw "hoas.lower: not an HOAS node (${desc})"

    else
      let t = h._htag; in

      # -- Types --
        # `nat` is the description-based fixpoint `mu natDesc`. natDescTm is
        # pre-elaborated at module scope to avoid re-elaborating on every use.
      if t == "nat" then T.mkMu T.mkUnit self.natDescTm T.mkTt
      # Reserved identifier `__descDesc` resolves to the pre-elaborated
      # description-of-descriptions Tm. Same pre-elaboration shortcut as
      # `nat` → `natDescTm`; consumers emit a single `desc-desc` node
      # instead of the full descDesc HOAS tree.
      else if t == "desc-desc" then self.descDescTm
      # Generic pre-elaborated opaque HOAS node. Carries a cached `Tm` for
      # a closed surface program; the elaborator returns the Tm verbatim
      # regardless of `depth` (sound because closed Tms contain no free de
      # Bruijn indices that would shift across enclosing bindings). Mirrors
      # the `nat` / `desc-desc` shortcut for arbitrary closed kernel terms
      # that would otherwise be re-walked on every elaboration.
      else if t == "pre-elab" then h.tm
      # Closed-Val splice. `H.litVal v` reflects a closed `Val` into the
      # term language without structural reconstruction; eval returns the
      # carried value verbatim. Use in place of `embedTm (quote 0 v)` when
      # the Val is closed and will only be re-evaluated.
      else if t == "lit-val" then T.mkLitVal h.val
      else if t == "desc-desc-app" then
        T.mkDescDescAppAt
          (lowerLevel depth (h.iLev or self.levelZero))
          (lower depth h.I)
          (lowerLevel depth h.L)
      else if t == "canon-app" then
        T.mkCanonApp h.id (map (lower depth) h.params) (lower depth h.body)
      else if t == "unit" then T.mkUnit
      else if t == "empty" then T.mkEmpty
      else if t == "absurd" then T.mkAbsurd (lower depth h.type) (lower depth h.term)
      else if t == "string" then T.mkString
      else if t == "int" then T.mkInt
      else if t == "float" then T.mkFloat
      else if t == "attrs" then T.mkAttrs
      else if t == "path" then T.mkPath
      else if t == "derivation" then T.mkDerivation
      else if t == "function" then T.mkFunction
      else if t == "any" then T.mkAny
      else if t == "U" then T.mkU (lowerLevel depth h.level)
      # Level sort and its three constructors. `level` is a type former
      # (`U(0)`-inhabiting); the constructors build a Level Tm that
      # ultimately lands in a `U`/`desc-arg`/`desc-pi` level slot.
      else if t == "level" then T.mkLevel
      else if t == "level-zero" then T.mkLevelZero
      else if t == "level-suc" then T.mkLevelSuc (lowerLevel depth h.pred)
      else if t == "level-max" then
        T.mkLevelMax (lowerLevel depth h.lhs) (lowerLevel depth h.rhs)
      # Raw list tags are used by value extraction; public `listOf` is an
      # app spine over `ListDT.T`.
      else if t == "list" then T.mkMu T.mkUnit (lower depth (self.listDesc h.elem)) T.mkTt
      # Raw sum tags are used by value extraction; public `sum` is an app
      # spine over `SumDT.T`.
      else if t == "sum" then T.mkMu T.mkUnit (lower depth (self.sumDesc h.left h.right)) T.mkTt
      # Private bootstrap coproduct used by descPlus interpretation.
      else if t == "boot-sum" then T.mkBootSum (lower depth h.L) (lower depth h.R)
      else if t == "boot-inl" then
        T.mkBootInl (lower depth h.L) (lower depth h.R) (lower depth h.term)
      else if t == "boot-inr" then
        T.mkBootInr (lower depth h.L) (lower depth h.R) (lower depth h.term)
      else if t == "boot-sum-elim" then
        T.mkBootSumElim (lower depth h.left) (lower depth h.right)
          (lower depth h.motive)
          (lower depth h.onLeft)
          (lower depth h.onRight)
          (lower depth h.scrut)
      else if t == "boot-eq" then
        T.mkBootEq (lower depth h.type) (lower depth h.lhs) (lower depth h.rhs)

      # -- Compound types (sugar for nested sigma/sum) --
      else if t == "record" then
        let
          fields = h.fields;
          n = builtins.length fields;
        in
        if n == 0 then T.mkUnit
        else if n == 1 then lower depth (builtins.head fields).type
        else
        # Build nested Sigma right-to-left: Σ(f1:T1).Σ(f2:T2)...Tn
          let lastType = lower depth (builtins.elemAt fields (n - 1)).type;
          in builtins.foldl'
            (acc: i:
              let field = builtins.elemAt fields (n - 2 - i); in
              T.mkSigma field.name (lower depth field.type) acc
            )
            lastType
            (builtins.genList (x: x) (n - 1))

      else if t == "maybe" then
      # Sum(inner, LiftAt 0 k Unit) — Left = value present, Right = null.
      # Delegates to the `sum` branch so the description-based
      # representation (μ(sumDesc l r)) is used uniformly with
      # `inl`/`inr` values. Mirrors `maybeAt`'s `_unfold`; at k = 0 the
      # lift is idempotent and this is the old `Sum inner Unit`.
        let k = h.level or self.levelZero; in
        lower depth (self.sumAt k h.inner (self.LiftAt self.levelZero k self.unit))

      else if t == "thunk" then
      # Lazy deepSeq-safe carrier `{ _tag : String; _force : Unit -> inner }`.
      # Elaborated as a record where `_force` is `function_` (the kernel
      # never invokes the closure — that's the whole laziness point);
      # `inner` is preserved at the HOAS surface for diagnostics and
      # forget, but does NOT appear in the elaborated kernel type.
        lower depth
          (self.record [
            { name = "_tag"; type = self.string; }
            { name = "_force"; type = self.function_; }
          ])

      else if t == "variant" then
        let
          branches = h.branches;
          n = builtins.length branches;
        in
        if n == 0 then lower depth self.void
        else if n == 1 then lower depth (builtins.head branches).type
        else
        # Build nested Sum right-to-left: Sum(T1, Sum(T2, ...Tn)) at the
        # node's level. Delegates to the `sum` branch so the nesting is in
        # the description representation, matching the inl/inr injection
        # shape. Mirrors `variantAt`'s `_unfold`; at k = 0 this is `sum`.
          let lastType = (builtins.elemAt branches (n - 1)).type;
              k = h.level or self.levelZero;
          in lower depth (builtins.foldl'
            (acc: i:
              let branch = builtins.elemAt branches (n - 2 - i); in
              self.sumAt k branch.type acc
            )
            lastType
            (builtins.genList (x: x) (n - 1)))

      # -- Binding types and terms (trampolined for deep nesting) --
      else if t == "pi" || t == "sigma" || t == "lam" || t == "let" then
        let
          # Peel nested binding forms iteratively via genericClosure
          chain = builtins.genericClosure {
            startSet = [{ key = depth; val = h; }];
            operator = item:
              let node = item.val; in
              if builtins.isAttrs node && node ? _htag &&
                (let nt = node._htag; in nt == "pi" || nt == "sigma" || nt == "lam" || nt == "let")
              then
                let marker = self.mkMarker item.key; in
                [{ key = item.key + 1; val = node.body marker; }]
              else [ ];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
          baseElab = lower (depth + n) base;
        in
        builtins.foldl'
          (acc: i:
            let
              item = builtins.elemAt chain (n - 1 - i);
              node = item.val;
              d = item.key;
              nt = node._htag;
              plicityAttr =
                if node ? _plicity then { _plicity = node._plicity; } else { };
            in
            if nt == "pi" then T.mkPi node.name (lower d node.domain) acc // plicityAttr
            else if nt == "sigma" then T.mkSigma node.name (lower d node.fst) acc
            else if nt == "lam" then T.mkLam node.name (lower d node.domain) acc // plicityAttr
            else T.mkLet node.name
              (lower d node.type)
              (elaborateForCheck d node.type node.val)
              acc
          )
          baseElab
          (builtins.genList (x: x) n)

      # -- Non-binding terms --
      else if t == "tt" then T.mkTt
      else if t == "boot-refl" then T.mkBootRefl
      else if t == "refl" then
        throw "hoas.lower: public refl requires an expected Eq type; use checkHoas or reflDT"
      else if t == "funext" then T.mkFunext
      else if t == "string-lit" then T.mkStringLit h.value
      else if t == "int-lit" then T.mkIntLit h.value
      else if t == "float-lit" then T.mkFloatLit h.value
      else if t == "attrs-lit" then T.mkAttrsLit
      else if t == "path-lit" then T.mkPathLit
      else if t == "derivation-lit" then T.mkDerivationLit
      else if t == "fn-lit" then T.mkFnLit
      else if t == "any-lit" then T.mkAnyLit
      else if t == "pair" then
        T.mkPair (lower depth h.fst) (lower depth h.snd)
      else if t == "opaque-lam" then
        T.mkOpaqueLam h._fnBox (lower depth h.piHoas)
      else if t == "str-eq" then
        T.mkStrEq (lower depth h.lhs) (lower depth h.rhs)
      else if t == "str-len" then
        T.mkStrLen (lower depth h.s)
      else if t == "int-le" then
        T.mkIntLe (lower depth h.lhs) (lower depth h.rhs)
      else if t == "int-eq" then
        T.mkIntEq (lower depth h.lhs) (lower depth h.rhs)
      else if t == "ann" then
        if h.trusted or false
        then
          let
            term = lower depth h.term;
            type = lower depth h.type;
          in
          if h ? _descRef
          then T.mkAnnTrustedWithDescRef term type (elaborateDescRef depth h._descRef)
          else T.mkAnnTrusted term type
        else T.mkAnn (elaborateForCheck depth h.type h.term) (lower depth h.type)
      # Macro constructor fallback: elaborate as the annotated lam cascade.
      # Saturated chain applications are recognised in the `app` branch
      # below and emit flat `desc-con` Tms without touching this branch.
      else if t == "dt-ctor-mono" then lower depth h.fallback
      else if t == "dt-ctor-poly" then lower depth h.fallback
      # `app` tries flat-chain flattening for saturated macro-constructor
      # applications first. Non-chain applications fall through to the
      # regular `mkApp (elab fn) (elab arg)`.
      else if t == "app" then
        let
          flat = tryFlattenCtorChain depth h;
          plicityAttr = if h ? _plicity then { _plicity = h._plicity; } else { };
        in
        if flat != null then flat
        else T.mkApp (lower depth h.fn) (lower depth h.arg) // plicityAttr
      else if t == "fst" then T.mkFst (lower depth h.pair)
      else if t == "snd" then T.mkSnd (lower depth h.pair)

      # -- Descriptions --
      else if t == "desc" then
        T.mkDescAt
          (if h ? iLev then lowerLevel depth h.iLev else T.mkLevelZero)
          (if h ? k then lowerLevel depth h.k else T.mkLevelZero)
          (lower depth h.I)
      else if t == "mu" then
        T.mkMu (lower depth h.I) (lower depth h.D) (lower depth h.i)
      else if t == "desc-con" then
        let
          D = lower depth h.D;
          i = lower depth h.i;
          d = lower depth h.d;
        in
        if h ? _descConCert
        then T.mkDescConWithCert D i d (elaborateDescConCert depth h._descConCert)
        else T.mkDescCon D i d
      else if t == "desc-ind" then
        T.mkDescInd (lower depth h.D) (lower depth h.motive)
          (lower depth h.step)
          (lower depth h.i)
          (lower depth h.scrut)
      # Kernel-primitive `interpD` / `allD` / `everywhereD` Tms (CDMM
      # §4.2.3 + §6.1). The `level` / `K` slots accept any Level encoding
      # (Nix-int, HOAS Level term, or kernel Tm) via `lowerLevel`.
      else if t == "interp-d" then
        T.mkInterpD (lowerLevel depth h.level)
          (lower depth h.I)
          (lower depth h.D)
          (lower depth h.X)
          (lower depth h.i)
      else if t == "all-d" then
        T.mkAllD (lowerLevel depth h.level)
          (lower depth h.I)
          (lower depth h.D)
          (lowerLevel depth h.K)
          (lower depth h.X)
          (lower depth h.M)
          (lower depth h.i)
          (lower depth h.d)
      else if t == "everywhere-d" then
        T.mkEverywhereD (lowerLevel depth h.level)
          (lower depth h.I)
          (lower depth h.D)
          (lowerLevel depth h.K)
          (lower depth h.X)
          (lower depth h.M)
          (lower depth h.ih)
          (lower depth h.i)
          (lower depth h.d)

      # Encoded desc constructors. Each `desc-*-enc` HOAS node carries
      # the index type `I` and the relevant kernel arguments; elaborate
      # to a `mkApp` chain over the kernel-internal `encodeDescX_Tm`
      # closed lambdas. The result evaluates to a `VDescCon` value of
      # type `μ⊤(descDesc I k) tt` — the encoded form of the source
      # description. Homogeneous-l (no explicit `l`/`eq`) routes through
      # `encodeDescArgTm`/`encodeDescPiTm`; heterogeneous-l (caller
      # supplied `l` and `eq`) routes through `encodeDescArgAtTm`/
      # `encodeDescPiAtTm`. Optional `_label` (per-node field name) and
      # `_conLabel` (surrounding constructor name) on the HOAS node ride
      # a `mkAnnTrustedWithLabels` wrapper around the encoder chain; eval
      # propagates both onto the resulting VDescCon (see eval/core.nix
      # `ann` clause), and `descViewF` surfaces them through `.label` and
      # `.conLabel` for downstream renderers and generic walkers. The
      # slots are orthogonal: a single VDescCon may carry both, either,
      # or neither.
      else if t == "desc-ret-enc" then
        let
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          jTm = lower depth h.j;
          chain = T.mkApp (T.mkApp (T.mkApp (T.mkApp self.encodeDescRetTm iLevTm) iTm) kTm) jTm;
          tyTm = T.mkMu T.mkUnit (T.mkDescDescAppAt iLevTm iTm kTm) T.mkTt;
        in
        if h ? _label || h ? _conLabel
        then
          T.mkAnnTrustedWithLabels chain tyTm
            {
              field = h._label    or null;
              con = h._conLabel or null;
            }
        else chain
      else if t == "desc-arg-enc" then
        let
          marker = self.mkMarker depth;
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          sTm = lower depth h.S;
          bodyTm = lower (depth + 1) (h.body marker);
          tLam = T.mkLam "_" sTm bodyTm;
          chain =
            if h ? l && h ? eq
            then
              let
                lTm = lowerLevel depth h.l;
                eqTm = lower depth h.eq;
              in
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp
                          (T.mkApp self.encodeDescArgAtTm iLevTm)
                          iTm)
                        kTm)
                      lTm)
                    eqTm)
                  sTm)
                tLam
            else if h ? l
            then
              let lTm = lowerLevel depth h.l; in
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp
                          (T.mkApp self.encodeDescArgAtTm iLevTm)
                          iTm)
                        kTm)
                      lTm)
                    T.mkBootRefl)
                  sTm)
                tLam
            else
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp self.encodeDescArgTm iLevTm)
                      iTm)
                    kTm)
                  sTm)
                tLam;
          tyTm = T.mkMu T.mkUnit (T.mkDescDescAppAt iLevTm iTm kTm) T.mkTt;
        in
        if h ? _label || h ? _conLabel
        then
          T.mkAnnTrustedWithLabels chain tyTm
            {
              field = h._label    or null;
              con = h._conLabel or null;
            }
        else chain
      else if t == "desc-rec-enc" then
        let
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          jTm = lower depth h.j;
          dTm = lower depth h.D;
          chain = T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp self.encodeDescRecTm iLevTm)
                  iTm)
                kTm)
              jTm)
            dTm;
          tyTm = T.mkMu T.mkUnit (T.mkDescDescAppAt iLevTm iTm kTm) T.mkTt;
        in
        if h ? _label || h ? _conLabel
        then
          T.mkAnnTrustedWithLabels chain tyTm
            {
              field = h._label    or null;
              con = h._conLabel or null;
            }
        else chain
      else if t == "desc-pi-enc" then
        let
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          sTm = lower depth h.S;
          fTm = lower depth h.f;
          dTm = lower depth h.D;
          chain =
            if h ? l && h ? eq
            then
              let
                lTm = lowerLevel depth h.l;
                eqTm = lower depth h.eq;
              in
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp
                          (T.mkApp
                            (T.mkApp self.encodeDescPiAtTm iLevTm)
                            iTm)
                          kTm)
                        lTm)
                      eqTm)
                    sTm)
                  fTm)
                dTm
            else if h ? l
            then
              let lTm = lowerLevel depth h.l; in
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp
                          (T.mkApp
                            (T.mkApp self.encodeDescPiAtTm iLevTm)
                            iTm)
                          kTm)
                        lTm)
                      T.mkBootRefl)
                    sTm)
                  fTm)
                dTm
            else
              T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp self.encodeDescPiTm iLevTm)
                        iTm)
                      kTm)
                    sTm)
                  fTm)
                dTm;
          tyTm = T.mkMu T.mkUnit (T.mkDescDescAppAt iLevTm iTm kTm) T.mkTt;
        in
        if h ? _label || h ? _conLabel
        then
          T.mkAnnTrustedWithLabels chain tyTm
            {
              field = h._label    or null;
              con = h._conLabel or null;
            }
        else chain
      else if t == "desc-plus-enc" then
        let
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          aTm = lower depth h.A;
          bTm = lower depth h.B;
          chain = T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp self.encodeDescPlusTm iLevTm)
                  iTm)
                kTm)
              aTm)
            bTm;
          tyTm = T.mkMu T.mkUnit (T.mkDescDescAppAt iLevTm iTm kTm) T.mkTt;
        in
        if h ? _label || h ? _conLabel
        then
          T.mkAnnTrustedWithLabels chain tyTm
            {
              field = h._label    or null;
              con = h._conLabel or null;
            }
        else chain
      else if t == "desc-elim-enc" then
        let
          iLevTm = lowerLevel depth (h.iLev or self.levelZero);
          iTm = lower depth h.I;
          kTm = lowerLevel depth h.k;
          lTm = lowerLevel depth h.L;
          mTm = lower depth h.motive;
          rTm = lower depth h.onRet;
          aTm = lower depth h.onArg;
          ecTm = lower depth h.onRec;
          pTm = lower depth h.onPi;
          plTm = lower depth h.onPlus;
          sTm = lower depth h.scrut;
        in
        T.mkApp
          (T.mkApp
            (T.mkApp
              (T.mkApp
                (T.mkApp
                  (T.mkApp
                    (T.mkApp
                      (T.mkApp
                        (T.mkApp
                          (T.mkApp
                            (T.mkApp self.encodeDescElimTm iLevTm)
                            iTm)
                          kTm)
                        lTm)
                      mTm)
                    rTm)
                  aTm)
                ecTm)
              pTm)
            plTm)
          sTm

      # -- Lift primitive --
      # The bound witness `eq : Eq Level (max l m) m` is auto-emitted as
      # `T.mkBootRefl` when absent; the kernel CHECK rule decides `convLevel
      # (max l m) m` via the semilattice quotient. The HOAS `*WithEq`
      # variants pass an explicit eq term (used when `l`/`m` are level-
      # polymorphic binders and `convLevel` cannot decide `refl`). Same
      # bound-witness shape as desc-arg.
      else if t == "lift" then
        T.mkLift (lowerLevel depth h.l) (lowerLevel depth h.m)
          (if h ? eq then lower depth h.eq else T.mkBootRefl)
          (lower depth h.A)
      else if t == "lift-intro" then
        T.mkLiftIntro (lowerLevel depth h.l) (lowerLevel depth h.m)
          (if h ? eq then lower depth h.eq else T.mkBootRefl)
          (lower depth h.A)
          (lower depth h.a)
      else if t == "lift-elim" then
        T.mkLiftElim (lowerLevel depth h.l) (lowerLevel depth h.m)
          (if h ? eq then lower depth h.eq else T.mkBootRefl)
          (lower depth h.A)
          (lower depth h.x)

      # -- Eliminators --
      # Generated datatype eliminators route through the macro-generated
      # `*.elim` terms, which produce `descInd` spines directly. User-level
      # motive-universe escape hatches go through `descInd` on the datatype
      # description, not through dedicated kernel eliminator tags.
      else if t == "j" then
        let
          headTm = lower depth
            (self.implicitApp
              (self.implicitApp (self.EqDT.elim 0) h.type)
              h.lhs);
          motiveTm = lower depth h.motive;
          baseTy = self.app (self.app h.motive h.lhs) (self.reflDT h.type h.lhs);
          baseTm = elaborateForCheck depth baseTy h.base;
          rhsTm = lower depth h.rhs;
          eqTm = elaborateForCheck depth (self.eq h.type h.lhs h.rhs) h.eq;
        in
        T.mkApp
          (T.mkApp
            (T.mkApp
              (T.mkApp
                headTm
                motiveTm)
              baseTm)
            rhsTm)
          eqTm

      else if t == "boot-j" then
        T.mkBootJ (lower depth h.type) (lower depth h.lhs)
          (lower depth h.motive)
          (lower depth h.base)
          (lower depth h.rhs)
          (lower depth h.eq)

      else if t == "squash" then
        T.mkSquash (lower depth h.A)
      else if t == "squash-intro" then
        T.mkSquashIntro (lower depth h.a)
      else if t == "squash-elim" then
        T.mkSquashElim (lower depth h.A) (lower depth h.B)
          (lower depth h.f)
          (lower depth h.x)

      else if h ? _surfaceRegistry then
        let
          handler = fx.tc.surface.registry.handlerFor h._surfaceRegistry t;
        in
        if handler == null
        then throw "hoas.lower: unknown tag: ${t}"
        else
          handler (fx.tc.surface.handlerContext {
            inherit depth h lower;
            hoas = self;
            inherit fx;
          })

      else throw "hoas.lower: unknown tag: ${t}";

  # ---- Meta-free elaboration pre-scan (`elab` / `checkHoas` /
  # ---- `inferHoas` fast paths) ----
  #
  # `elab` discards the elaborator result unless the run created
  # metavariables: `delta == {}` falls through to the rigid Tm, and
  # elaborator errors fall through before the delta check. On this path
  # the only freshMeta producer is `insertImplicits`
  # (tc/elaborate/insertion.nix), reached from
  #   - elabInferApp: explicit app whose fn type forces to an implicit
  #     VPi (tc/elaborate/infer.nix), and
  #   - elabSub: app/ann argument whose inferred type forces to an
  #     implicit VPi (tc/elaborate/check.nix).
  # The rigid kernel checker cannot create metas, and the meta layer
  # never descends into binders (elabInfer routes only app/meta heads to
  # the meta path; rigidOrSub routes only app/ann/meta arguments), so a
  # syntactic walk of the app-spine skeleton — spine fns plus arguments
  # that are themselves app/ann, transitively — suffices to prove delta
  # stays empty. Scan-clean terms return the rigid Tm without running
  # the elaborator at all: bit-identical to the fall-through result.
  #
  # `checkHoas` / `inferHoas` use the same scan with a stronger payoff:
  # they consume the elaborator output even when `delta == {}`, relying
  # on the conservativity claim that a meta-free elaborator run equals
  # the kernel rule (both sides build the result through the same
  # kernel sub-checks and the identical `T.mkApp`/`T.mkAnn`
  # reconstruction; the rigid routes inside the elaborator ARE direct
  # `checkTm`/`inferTm` calls). Scan-clean terms there route straight
  # to the kernel rule. The checking direction needs one extra
  # condition: the expected type's head must not force to an implicit
  # Pi, else `descendImplicitPi` would rewrite the term (meta-free, but
  # not the kernel's output) and `elabSub` would skip its insertion
  # gate asymmetrically.
  #
  # sig(tm) approximates the plicity prefix of tm's type as
  # { pre : [Plicity]; open : Bool }. `open` marks an unknown tail:
  # anything not provably explicit makes the enclosing consumption dirty
  # (run the elaborator — never wrong, only slower). A closed empty
  # prefix is a type former that can never force to a VPi, so
  # insertImplicits cannot fire on it.

  # Type formers whose values are canonical and never a VPi. Must stay
  # minimal: a wrong entry here is a soundness hole, not a perf loss.
  scanSafeEnd = {
    U = true; mu = true; sigma = true; "boot-sum" = true; unit = true;
    lift = true;
    string = true; int = true; float = true; attrs = true; path = true;
    derivation = true; function = true; any = true;
  };

  # Plicity prefix of a syntactic pi tower. Native recursion is bounded in
  # host-stack depth despite the tower depth: the result `{ pre; open }`
  # holds the codomain recursion behind `rest`, a thunk. Every consumer
  # peels `pre` one binder at a time (`head`/`tail`/`!= []`) or reads `open`
  # once the prefix is exhausted; each step forces a single `++`/`inherit`
  # level and leaves `rest` unforced, so the call stack stays O(1) in the
  # tower depth (verified at depth 16000, well past the ~10000 ceiling a
  # depth-scaling walk overflows at).
  scanPrefixOf = ty:
    let t = if builtins.isAttrs ty then ty.tag or null else null; in
    if t == "pi" then
      let rest = scanPrefixOf ty.codomain; in
      { pre = [ (ty._plicity or "explicit") ] ++ rest.pre; inherit (rest) open; }
    else { pre = [ ]; open = !(builtins.isString t && scanSafeEnd ? ${t}); };

  # sig of a rigid (non-app) term in fn position. lam plicity
  # miscalibration is safe in both directions: the kernel never invents
  # implicit VPis, so a wrong sidecar can only over-dirty the scan.
  scanSigOf = tm:
    let t = if builtins.isAttrs tm then tm.tag or null else null; in
    if t == "ann" then scanPrefixOf tm.type
    else if t == "lam" then { pre = [ (tm._plicity or "explicit") ]; open = true; }
    else { pre = [ ]; open = true; };

  # The type may force to an implicit VPi: implicit head or unknown
  # prefix. Drives the elabSub argument condition.
  scanHeadRisky = sig:
    if sig.pre != [ ] then builtins.head sig.pre == "implicit"
    else sig.open;

  # Argument (checking) position: only app/ann/meta arguments reach
  # elabSub, which runs insertImplicits on the argument's inferred type;
  # everything else is rigid-checked and cannot create metas.
  scanArgClean = tm: scanArgCleanGo nativeWalkBudget tm;

  scanArgCleanGo = fuel: tm:
    let t = if builtins.isAttrs tm then tm.tag or null else null; in
    if t == "meta" then false
    else if t == "app" then
      let sig = scanInferSigGo fuel tm; in
      sig != null && !(scanHeadRisky sig)
    else if t == "ann" then !(scanHeadRisky (scanPrefixOf tm.type))
    else true;

  # Infer-mode skeleton walk. Returns the consumed sig, or null when the
  # elaborator must run. Implicit apps consume a binder without insertion
  # regardless of its plicity (userExplicit = false skips insertImplicits).
  # The app skeleton branches on both `.fn` and `.arg`, so a deep literal
  # app tower recurses once per layer. `scanInferSigGo` recurses directly
  # for the common shallow case (preserving its lazy short-circuit); past
  # `nativeWalkBudget` it hands the remaining sub-term to `scanInferSigSlow`
  # so host-stack depth stays bounded.
  scanInferSig = tm: scanInferSigGo nativeWalkBudget tm;

  scanInferSigGo = fuel: tm:
    let t = if builtins.isAttrs tm then tm.tag or null else null; in
    if t == "meta" then null
    else if t == "app" then
      if fuel <= 0 then scanInferSigSlow tm
      else
        let fnSig = scanInferSigGo (fuel - 1) tm.fn; in
        if fnSig == null then null
        else
          let explicitApp = (tm._plicity or "explicit") == "explicit"; in
          if fnSig.pre != [ ] then
            (if explicitApp && builtins.head fnSig.pre != "explicit" then null
             else if scanArgCleanGo (fuel - 1) tm.arg
             then { pre = builtins.tail fnSig.pre; inherit (fnSig) open; }
             else null)
          # Consuming a closed empty prefix is a guaranteed "expected
          # function type" error (errors fall through to the rigid Tm
          # anyway), but stay conservative: run the elaborator.
          else if !fnSig.open || explicitApp then null
          else if scanArgCleanGo (fuel - 1) tm.arg then fnSig
          else null
    else scanSigOf tm;

  # Deep-tail fallback for `scanInferSigGo`: an explicit post-order task
  # stack that folds each app node's sig from its children. `eval` expands
  # a node; `app1`/`app2` pop child sigs and combine. An app argument's
  # clean-ness is its own sig (mirrors `scanArgClean`); non-app arguments
  # stay shallow. Force each sig into the key so the fold does not defer a
  # step-count-deep chain.
  scanInferSigSlow = tm0:
    let
      push = x: s: { head = x; tail = s; };
      tagOf = x: if builtins.isAttrs x then x.tag or null else null;
      combine = fnSig: explicitApp: argClean:
        if fnSig == null then null
        else if fnSig.pre != [ ] then
          (if explicitApp && builtins.head fnSig.pre != "explicit" then null
           else if argClean then { pre = builtins.tail fnSig.pre; inherit (fnSig) open; }
           else null)
        else if !fnSig.open || explicitApp then null
        else if argClean then fnSig
        else null;
      steps = builtins.genericClosure {
        startSet = [{ key = 0; tasks = push { ev = tm0; } null; results = null; }];
        operator = item:
          if item.tasks == null then [ ]
          else
            let task = item.tasks.head; rest = item.tasks.tail; in
            if task ? ev then
              let tm = task.ev; t = tagOf tm; in
              if t == "app" then
                let explicitApp = (tm._plicity or "explicit") == "explicit"; in
                if tagOf tm.arg == "app" then
                  [{
                    key = item.key + 1;
                    tasks = push { ev = tm.fn; }
                      (push { ev = tm.arg; }
                        (push { app2 = { inherit explicitApp; }; } rest));
                    results = item.results;
                  }]
                else
                  let argClean = scanArgClean tm.arg; in
                  [{
                    key = item.key + 1;
                    tasks = push { ev = tm.fn; }
                      (push { app1 = { inherit explicitApp argClean; }; } rest);
                    results = item.results;
                  }]
              else
                let sig = if t == "meta" then null else scanSigOf tm; in
                [{
                  key = builtins.seq sig (item.key + 1);
                  tasks = rest;
                  results = push sig item.results;
                }]
            else if task ? app1 then
              let sig = combine item.results.head task.app1.explicitApp task.app1.argClean; in
              [{
                key = builtins.seq sig (item.key + 1);
                tasks = rest;
                results = push sig item.results.tail;
              }]
            else
              let
                argSig = item.results.head;
                fnSig = item.results.tail.head;
                argClean = argSig != null && !(scanHeadRisky argSig);
                sig = combine fnSig task.app2.explicitApp argClean;
              in
              [{
                key = builtins.seq sig (item.key + 1);
                tasks = rest;
                results = push sig item.results.tail.tail;
              }];
      };
      final = builtins.head (builtins.filter (it: it.tasks == null) steps);
    in
    final.results.head;
in
{
  scope = {
    lower = api.leaf {
      description = "lower: depth-parameterised HOAS-to-Tm compiler — `lower depth h` converts a HOAS term to its de Bruijn `Tm` representation; `depth` is the binding level at the call site.";
      signature = "lower : Int -> Hoas -> Tm";
      doc = ''
        The principal HOAS-side compilation entry. Binding chains are
        lowered iteratively via `genericClosure` for stack safety
        to 8000+ depth. Use directly when controlling the binding
        depth (e.g. when re-lowering an open HOAS subterm). For
        the closed-term case, prefer `elab` which fixes `depth = 0`.
      '';
      value = lower;
    };
    reifyLevel = api.leaf {
      description = "reifyLevel: HOAS Level → kernel Level Tm — converts a HOAS-side level expression (Int, level term, or already-reified Tm) to the kernel's canonical Level representation.";
      signature = "reifyLevel : Level -> Tm";
      value = reifyLevel;
    };

    # Rigid-fallback on structural overlay error; throw on unsolved
    # metas at the boundary.
    elab = api.leaf {
      description = "elab: closed-term HOAS-to-Tm compiler — lowers a HOAS term from depth 0, runs meta-aware synthesis + zonking, and surfaces unsolved metas as a throw at the elaborator boundary.";
      signature = "elab : Hoas -> Tm";
      value = h:
        let
          tmRaw = lower 0 h;
          outerTag = tmRaw.tag or null;
        in
        # Meta-aware synthesis only fires for outer `app` (implicit-Pi
        # insertion via elabInferApp) or `meta` heads. Every other tag
        # delegates straight to the rigid kernel `inferTm`, which is a
        # recursive structural walk — wasted work that also blows the
        # call stack on deep Tms. Return the rigid Tm directly.
        if outerTag != "app" && outerTag != "meta"
        then tmRaw
        # Skeleton pre-scan: a clean app spine provably creates no
        # metas, so the elaborator run below would fall through to
        # tmRaw — skip it. (`meta` outer tags scan dirty.)
        else if scanInferSig tmRaw != null
        then tmRaw
        else
          let r = meta.runElab self.unit (meta.elabInfer CH.emptyCtx tmRaw); in
          if builtins.isAttrs r.value && r.value ? error
          then tmRaw
          else if r.state.delta == { }
          then tmRaw
          else
            let zonked = meta.zonkTm 0 r.state r.value.term; in
            if zonked ? error
            then throw "H.elab: ${zonked.error.tag} ${toString (zonked.error.id or 0)} — supply expected type via H.checkHoas, or annotate the call site"
            else zonked.value;
    };

    # Elaborate type + term, then run the kernel checker. On success the
    # elaborated Tm is returned unchanged; on failure the result is
    # decorated with `hint` (from `fx.diag.hints`) and `surface` (back-map
    # through the term's SourceMap).
    #
    # Inlined rather than routed through `CHD.runCheckDLazy` to avoid a
    # per-call function layer + closure allocation on the hot success
    # path. The SourceMap reference sits inside the failure branch, so
    # `self.sourceMapOf hoasTm` is only forced when a type error fires.
    # `CHD.runCheckDLazy` / `elab2` remain available for library callers
    # that prefer the shell wrapper or an eager (Tm, SourceMap) pair.
    checkHoas = api.leaf {
      description = "checkHoas: HOAS-driven type-checker — `checkHoas typeHoas termHoas` elaborates both, runs the kernel `check` rule, and returns the checked term or a structured Error.";
      signature = "checkHoas : Hoas -> Hoas -> Tm | Error";
      doc = ''
        The principal entry for verifying a HOAS term against a HOAS
        type. Elaborates type and term in tandem (so binders align),
        then invokes the kernel `check` rule which produces a
        verified `Tm` or a structured `Error` carrying the failing
        rule and contextual `Detail`. Returns the Error directly
        (does not throw); callers route through `?error` for fast
        dispatch.
      '';
      value = hoasTy: hoasTm:
        let
          # Type-check the type Tm first so that desc-* CHECK rules
          # retarget any inner descriptions to encoded form. The eval'd
          # type Val then has the same shape as the values produced by
          # desc-con's internal `checkDescAtAnyLevel` retarget — without
          # this pass the type's `.D` stays primitive while the term's
          # checked payload becomes encoded, causing a structural mismatch
          # at conv time.
          tyRaw = self.elab hoasTy;
          tyResult = CH.runCheck (CH.checkTypeLevel CH.emptyCtx tyRaw);
          tyHasError = builtins.isAttrs tyResult && tyResult ? error;
          ty = if tyHasError then tyRaw else tyResult.term;
          # Derive the EqDT sort/lhs/rhs witnesses once from the checked Tm
          # and share them across the vTy and refl-conv builds, which
          # otherwise each re-derive them.
          sharedEq =
            if tyHasError || hoasEqBody hoasTy 0 == null
            then null
            else checkedEqWitnesses ty;
          ty' = if sharedEq == null then ty else spliceTmEqWitnesses ty sharedEq;
          hoasTy' = if sharedEq == null then hoasTy else spliceHoasEqWitnesses hoasTy sharedEq;
          tm = elaborateForCheck 0 hoasTy' hoasTm;
          vTy = E.eval [ ] ty';
          # Single-track: by conservativity, meta-free elaborator output
          # equals the kernel checker's output. Kernel pass fires on the
          # elaborator-error fallback for the rigid diagnostic — and
          # directly when the pre-scan proves the run meta-free up
          # front: a scan-clean term against an expected type whose
          # head is not an implicit Pi (`descendImplicitPi` cannot
          # rewrite, `elabSub` cannot insert) makes the elaborator a
          # kernel run in costume. The forced head is shared with the
          # kernel run that follows.
          scanFast =
            scanArgClean tm
            && !(meta.isImplicitPi (E.forceVal vTy));
          metaRun =
            if tyHasError || scanFast then null
            else meta.runElab self.unit (meta.elabCheck CH.emptyCtx tm vTy);
          metaErr =
            metaRun != null
            && builtins.isAttrs metaRun.value && metaRun.value ? error;
          r =
            if tyHasError then tyResult
            else if scanFast || metaErr then CH.runCheck (CH.check CH.emptyCtx tm vTy)
            else if metaRun.state.delta == { } then metaRun.value
            else
              let zonked = meta.zonkTm 0 metaRun.state metaRun.value; in
              if zonked ? error
              then throw "H.checkHoas: ${zonked.error.tag} ${toString (zonked.error.id or 0)} — expected type did not pin all metavariables"
              else zonked.value;
        in
        if builtins.isAttrs r && r ? error
        then
          let
            hint = fx.diag.hints.resolve r.error;
            errorTree =
              if hint == null then r.error
              else fx.diag.error.setLeafHint hint r.error;
          in
          r // {
            error = errorTree;
            inherit hint;
            surface = CHD.sourceMap.hoasAtError r.error (self.sourceMapOf hoasTm);
          }
        else r;
    };

    inferHoas = api.leaf {
      description = "inferHoas: HOAS-driven type inference — `inferHoas termHoas` elaborates and runs the kernel `infer` rule, returning `{ term, type }` or a structured Error.";
      signature = "inferHoas : Hoas -> { term : Tm, type : Val } | Error";
      doc = ''
        Complement to `checkHoas` for the synthesis direction. Many
        HOAS forms are inference-friendly (annotated values,
        applications with inferable heads); pure inference fails on
        checking-only forms like bare lambdas or data constructors
        without an enclosing annotation.
      '';
      value = hoasTm:
        let
          tmRaw = lower 0 hoasTm;
          outerTag = tmRaw.tag or null;
          # See H.elab for the structural rationale: only `app` / `meta`
          # heads can drive new meta allocation through `elabInferApp`.
          # Scan-provably meta-free spines skip the elaborator the same
          # way: meta-free synthesis equals the kernel rule (the
          # conservativity claim in `checkHoas`), so the rigid branch
          # below returns the same result without the elaborator run.
          metaCandidate =
            (outerTag == "app" || outerTag == "meta")
            && scanInferSig tmRaw == null;
          metaRun =
            if metaCandidate
            then meta.runElab self.unit (meta.elabInfer CH.emptyCtx tmRaw)
            else null;
          metaErr =
            !metaCandidate
            || (builtins.isAttrs metaRun.value && metaRun.value ? error);
          # Single-track on success (conservativity). Kernel fallback
          # only for the rigid diagnostic on elaborator-error.
          r =
            if metaErr
            then CH.runCheck (CH.infer CH.emptyCtx tmRaw)
            else if metaRun.state.delta == { }
            then {
              term = metaRun.value.term;
              type = metaRun.value.type;
            }
            else
              let zonked = meta.zonkTm 0 metaRun.state metaRun.value.term; in
              if zonked ? error
              then throw "H.inferHoas: ${zonked.error.tag} ${toString (zonked.error.id or 0)} — synthesis is partial; supply expected type via H.checkHoas"
              else {
                term = zonked.value;
                type = metaRun.value.type;
              };
        in
        if builtins.isAttrs r && r ? error
        then
          let
            hint = fx.diag.hints.resolve r.error;
            errorTree =
              if hint == null then r.error
              else fx.diag.error.setLeafHint hint r.error;
          in
          r // {
            error = errorTree;
            inherit hint;
            surface = CHD.sourceMap.hoasAtError r.error (self.sourceMapOf hoasTm);
          }
        else r;
    };

    # Natural number literal helper — build S^n(zero).
    natLit = api.leaf {
      description = "natLit: Nix integer to HOAS Nat — `natLit n` builds `succ^n zero` as a HOAS term; convenience wrapper around iterated `succ` application.";
      signature = "natLit : Int -> Hoas";
      value = n:
        builtins.foldl' (acc: _: self.succ acc) self.zero (builtins.genList (x: x) n);
    };
  };
  tests = { };
}
