# Evaluator core: value operations, eliminators, and the main `evalF`.
#
# Pure evaluator interpreting kernel terms in an environment of values
# (§4, §9). Zero effect-system imports — part of the trusted computing
# base.
#
# Fuel-threaded: each `evalF` call decrements a counter; exhaustion
# throws "normalization budget exceeded". Default budget is 10M steps
# (§9). Trampolines the `desc-con` chain via `builtins.genericClosure`
# to bound stack depth on deep generated recursive data (§11.3).
#
# Description operations (`vDescIndF`, `linearProfileF`)
# live in the sibling `desc.nix`; `evalF` dispatches to them through
# `self`.
{ self, fx, api, ... }:

let
  val = fx.tc.value;
  inherit (val) mkClosure
    envCons envNth envLen envFromList
    vLam vPi vSigma vPair
    vUnit vTt vEmpty vBootSum vBootInl vBootInr vBootEq vBootRefl vFunext vU vNe vNeSnoc
    vSquash vSquashIntro
    vLevel vLevelZero vLevelSuc vLevelMax
    vLift vLiftIntro
    vMu vDescCon vDescConChain
    vString vInt vFloat vAttrs vPath vDerivation vFunction vAny
    vStringLit vIntLit vFloatLit vAttrsLit vPathLit vDerivationLit vFnLit vAnyLit
    eApp eFst eSnd eBootSumElim eBootJ eStrEq eAbsurd eLiftElim
    eSquashElim;
  H = fx.tc.hoas;
  boolDescTm = H.elab H.boolDesc;

  # Cached `U(0)` value. `mkU mkLevelZero` produces a term whose `level` is the
  # `level-zero` singleton; evaluating under the U-case returns this
  # sentinel directly — no fuel decrement, no dispatch, no allocation.
  vUZero = vU vLevelZero;

  # Effective `_layers` of a chain-form Val, honoring an optional `_layersOff`
  # slice offset. Fast-path `o == 0` returns the array unchanged — byte-identical
  # for every value built by the constructor; only offset-carrying machine
  # predecessors materialize a slice, on cold reads.
  effLayers = cv:
    let o = cv._layersOff or 0; ls = cv._layers;
    in if o == 0 then ls
       else builtins.genList (i: builtins.elemAt ls (o + i)) ((builtins.length ls) - o);

  # mkValueF: dispatch-algebra-parameterized kernel evaluator body.
  #
  # The kernel instantiates `mkValueF self` (recovering original
  # semantics); overlays — notably `tc/elaborate/eval-overlay.nix` —
  # instantiate with their own self-table so closure-body evaluation
  # respects VMeta-aware dispatch (`tc/elaborate/value.nix` elims).
  #
  # Refs: Abel-Pientka 2011 §2. Kernel-purity (value.nix:13-17) is
  # preserved by parameterizing the dispatch surface; the kernel's
  # `self` never sees VMeta. Closure bodies whose env contains a
  # `VMeta` must be evaluated through the overlay self, never through
  # the kernel self.
  mkValueF = self_: fuel: envIn: tm:
    if fuel <= 0 then throw "normalization budget exceeded"
    else
      let env = envFromList envIn; t = tm.tag; f = fuel - 1; ev = self_.evalF f env; in
      if t == "var" then envNth env tm.idx
      else if t == "let" then self_.evalF f (envCons (ev tm.val) env) tm.body
      else if t == "ann" then
        let
          v = ev tm.term;
          v1 =
            if tm ? _descRef
            then v // { _descRef = evalDescRef ev tm._descRef; }
            else v;
          v2 = if tm ? _label then v1 // { _label = tm._label; } else v1;
          v3 = if tm ? _conLabel then v2 // { _conLabel = tm._conLabel; } else v2;
        in
        v3

      else if t == "pi" then
        let v = vPi tm.name (ev tm.domain) (mkClosure env tm.codomain);
        in if tm ? _plicity then v // { _plicity = tm._plicity; } else v
      else if t == "lam" then
        let v = vLam tm.name (ev tm.domain) (mkClosure env tm.body);
        in if tm ? _plicity then v // { _plicity = tm._plicity; } else v
      else if t == "app" then self_.vAppF f (ev tm.fn) (ev tm.arg)

      else if t == "sigma" then vSigma tm.name (ev tm.fst) (mkClosure env tm.snd)
      else if t == "pair" then vPair (ev tm.fst) (ev tm.snd)
      else if t == "fst" then self_.vFst (ev tm.pair)
      else if t == "snd" then self_.vSnd (ev tm.pair)

      else if t == "unit" then vUnit
      else if t == "tt" then vTt
      else if t == "empty" then vEmpty
      else if t == "absurd" then
        self_.vAbsurd (ev tm.type) (ev tm.term)

      else if t == "boot-sum" then vBootSum (ev tm.left) (ev tm.right)
      else if t == "boot-inl" then vBootInl (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "boot-inr" then vBootInr (ev tm.left) (ev tm.right) (ev tm.term)
      else if t == "boot-sum-elim" then
        let scrut = ev tm.scrut; in
        if scrut.tag == "VBootInl" then self_.vAppF f (ev tm.onLeft) scrut.val
        else if scrut.tag == "VBootInr" then self_.vAppF f (ev tm.onRight) scrut.val
        else
          self_.vBootSumElimF f (ev tm.left) (ev tm.right) (ev tm.motive)
            (ev tm.onLeft)
            (ev tm.onRight)
            scrut

      else if t == "boot-eq" then vBootEq (ev tm.type) (ev tm.lhs) (ev tm.rhs)
      else if t == "boot-refl" then vBootRefl
      else if t == "funext" then vFunext
      else if t == "boot-j" then
        let eq = ev tm.eq; in
        if eq.tag == "VBootRefl" then ev tm.base
        else
          self_.vBootJ (ev tm.type) (ev tm.lhs) (ev tm.motive)
            (ev tm.base)
            (ev tm.rhs)
            eq

      else if t == "squash" then vSquash (ev tm.A)
      else if t == "squash-intro" then vSquashIntro (ev tm.a)
      else if t == "squash-elim" then
        self_.vSquashElimF f (ev tm.A) (ev tm.B) (ev tm.f) (ev tm.x)

      # Descriptions
      else if t == "desc" then
      # Level-zero fast-path: the prelude `desc I` (= desc^0 I) is
      # the overwhelmingly common shape. Reuse the `vLevelZero`
      # singleton and skip the eval/int-shim pipeline on `tm.k`.
        let
          iLevVal =
            if tm.iLev.tag != "level-zero"
            then ev tm.iLev
            else vLevelZero;
        in
        if tm.k.tag == "level-zero"
        then val.vDescAt vLevelZero iLevVal (ev tm.I)
        else val.vDescAt (ev tm.k) iLevVal (ev tm.I)
      else if t == "mu" then vMu (ev tm.I) (ev tm.D) (ev tm.i)
      # desc-con-chain — canonical flat-form chain. Bijective dual of
      # the chain-form Val (`_shape == "linearChain"`); no peel analysis
      # needed. Layers iterate via `map` (libnix-iterative), so the
      # construction consumes O(1) simultaneously-active libnix frames
      # regardless of N — the depth-axis property the brief demands.
      else if t == "desc-con-chain" then
        let
          outerDV = ev tm.outerD;
          leftV   = ev tm.payloadLeft;
          rightV  = ev tm.payloadRight;
          baseDV  = ev tm.base.D;
          baseIV  = if tm.base.i.tag == "tt" then vTt else ev tm.base.i;
          baseDdV = ev tm.base.d;
          baseVal = vDescCon baseDV baseIV baseDdV;
          layerVals = map (l: {
            i     = if l.i.tag == "tt" then vTt else ev l.i;
            heads = map ev l.heads;
            cert  = null;
          }) tm.layers;
          finalOuterI =
            if layerVals == [ ] then baseIV
            else (builtins.head layerVals).i;
        in
        vDescConChain outerDV finalOuterI tm.payloadTag
          leftV rightV layerVals baseVal

      # desc-con — trampolined for deep recursive chains (5000+).
      # Peels a homogeneous desc-con chain along its single recursive
      # position when D = plus A B with exactly one of A, B linear-
      # recursive (a descArg-chain ending in `descRec descRet`). The
      # recursive summand drives the chain; its injection side picks
      # the payload tag (`boot-inl` when A is recursive, `boot-inr` when B is).
      #
      # Payload at each layer is `boot-inl/boot-inr lTy rTy (pair f_0 … (pair REC refl))`
      # — n data fields, the recursive tail, and a refl witness for
      # the ret-leaf equality. lTy/rTy are invariant across layers (D
      # is shared) and reused from the first peel.
      #
      # Non-linear shapes (tree, mutual recursion, multi-recursive
      # ctors, non-plus D) fall through to per-layer evaluation.
      #
      # D-sharing across layers: fast path is structural equality of
      # the D subterm (holds when elaborate emits a shared dTm per
      # chain, and when β-reducing macro-generated constructors under
      # a shared param env); fallback is conv-equality of the evaluated
      # D against the outer dVal.
      else if t == "desc-con" then
        let
          dVal = ev tm.D;
          cert = tm._descConCert or null;
          certRef = if cert == null then null else cert.ref;
          certLinear =
            if certRef == null then null else certRef.linearChain or null;
          dRef = dVal._descRef or null;
          dLinear = if dRef == null then null else dRef.linearChain or null;
          sameCertRef = other:
            certRef != null
            && other != null
            && (other.kind or null) == (certRef.kind or null)
            && (other.name or null) == (certRef.name or null)
            && (other.arity or null) == (certRef.arity or null)
            && (other.indexed or null) == (certRef.indexed or null)
            && builtins.length (other.params or [ ]) == builtins.length (certRef.params or [ ])
            && (other.linearChain or null) == certLinear;
          certClassify =
            if certLinear == null then null
            else {
              side = certLinear.side;
              fieldCount = certLinear.dataFieldCount;
              ctor = certLinear.ctor;
              certified = true;
            };
          refClassify =
            if dLinear == null then null
            else {
              side = dLinear.side;
              fieldCount = dLinear.dataFieldCount;
              ctor = dLinear.ctor;
            };
          refDeclinesLinear =
            (certRef != null && certLinear == null)
            || (dRef != null && dLinear == null);
          # Classify plus D. null declines the trampoline; otherwise
          # returns the linear profile and which side (`inl`/`inr`)
          # carries the recursive summand.
          plusSides =
            let view = self_.descViewF f dVal; in
            if view != null && view.idx == 4
            then { A = view.A; B = view.B; }
            else null;
          classify =
            if certClassify != null then certClassify
            else if refClassify != null then refClassify
            else if refDeclinesLinear then null
            else if plusSides == null then null
            else
              let
                pA = self_.linearProfileF f plusSides.A;
                pB = self_.linearProfileF f plusSides.B;
              in
              if pA != null && pB == null then { profile = pA; side = "inl"; }
              else if pB != null && pA == null then { profile = pB; side = "inr"; }
              else null;
          profile = if classify == null then [ ] else classify.profile;
          nFields =
            if classify == null then 0
            else classify.fieldCount or (builtins.length profile);
          depth = envLen env;
          sameD = node:
            if classify ? certified then
              let nodeCert = node._descConCert or null; in
              nodeCert != null
              && (nodeCert.kind or null) == "datatype-con-payload"
              && nodeCert.ctor == classify.ctor
              && sameCertRef nodeCert.ref
            else if node.D == tm.D then true
            else fx.tc.conv.conv depth (self_.evalF f env node.D) dVal;
          # Walk n data-field pairs terminated by `pair REC refl`.
          collectPairs = inner:
            let
              isRetLeaf = p:
                p.tag == "boot-refl"
                || (p.tag == "lift-intro" && p.a.tag == "boot-refl");
              collect = i: p: acc:
                if i == nFields then
                  if p.tag != "pair" then null
                  else if !(isRetLeaf p.snd) then null
                  else if p.fst.tag != "desc-con" then null
                  else { heads = acc; tail = p.fst; }
                else
                  if p.tag != "pair" then null
                  else collect (i + 1) p.snd (acc ++ [ p.fst ]);
            in
            collect 0 inner [ ];
          walkPayload = payload:
            if classify == null then null
            else
              let
                sv = self_.sumPayloadTmView payload;
                inner =
                  if sv == null || sv.side != classify.side
                  then null
                  else collectPairs sv.value;
              in
              if inner == null then null
              else inner // { rebuildVal = sv.rebuildVal; };
          peel = node:
            if classify == null then null
            else if node.tag != "desc-con" then null
            else if !(sameD node) then null
            else walkPayload node.d;
          # Integer key is sufficient for dedup. `peel` is O(1) field
          # inspection into the already-concrete `tm`; no deferred work
          # accumulates on `val`, so the trampoline.nix deepSeq defense
          # is unnecessary and would add O(N²) cost through repeated
          # traversal.
          chain = builtins.genericClosure {
            startSet = [{ key = 0; val = tm; peeled = peel tm; }];
            operator = item:
              if item.peeled == null then [ ]
              else
                let val = item.peeled.tail; in
                [{ key = item.key + 1; inherit val; peeled = peel val; }];
          };
          n = builtins.length chain - 1;
          base = (builtins.elemAt chain n).val;
          topPeel = if n >= 1 then (builtins.elemAt chain 0).peeled else null;
          withCert = node: iVal: dPayload:
            let
              raw = vDescCon dVal iVal dPayload;
            in
            if node ? _descConCert
            then raw // { _descConCert = node._descConCert; }
            else raw;
        in
        if n > f then throw "normalization budget exceeded"
        else
          let
            baseI =
              if base.i.tag == "tt" then vTt else self_.evalF (f - n) env base.i;
            baseVal = withCert base baseI (self_.evalF (f - n) env base.d);
            chainForm = classify != null && plusSides != null;
          in
          if chainForm then
            let
              payloadInfo = {
                tag = if classify.side == "inl" then "VBootInl" else "VBootInr";
                left = plusSides.A;
                right = plusSides.B;
              };
              tmLayers = builtins.genList
                (k:
                  let
                    layerItem = builtins.elemAt chain k;
                    layerTm   = layerItem.val;
                  in {
                    i =
                      if layerTm.i.tag == "tt" then vTt
                      else self_.evalF (f - n) env layerTm.i;
                    heads = map
                      (h: self_.evalF (f - n) env h)
                      layerItem.peeled.heads;
                    cert = layerTm._descConCert or null;
                  })
                n;
              # Val-level peel: see machine.nix:KDescConPeel_BaseD chain-form
              # branch for design rationale. Recovers layers when Tm-level
              # peel terminates at a runtime `var` whose bound Val is a
              # recursive-side ctor (the typical descInd reduction case).
              chainNF = self_.forceAndPeelChainV payloadInfo.tag nFields baseVal;
              allLayers = tmLayers ++ chainNF.layers;
              finalBase = chainNF.base;
              finalOuterI =
                if allLayers == [ ] then finalBase.i
                else (builtins.head allLayers).i;
            in
            vDescConChain dVal finalOuterI
              payloadInfo.tag payloadInfo.left payloadInfo.right
              allLayers finalBase
          else
            let
              buildInner = hs: innerTail:
                if hs == [ ] then innerTail
                else vPair (builtins.head hs) (buildInner (builtins.tail hs) innerTail);
              wrapPayload = innerVal:
                topPeel.rebuildVal (tm': self_.evalF (f - n) env tm') innerVal;
            in
            builtins.foldl'
              (acc: i:
                let
                  layerItem = builtins.elemAt chain (n - 1 - i);
                  layer = layerItem.val;
                  peeled = layerItem.peeled;
                  heads = peeled.heads;
                  headVals = map (h: self_.evalF (f - n + i) env h) heads;
                  iLayerVal =
                    if layer.i.tag == "tt" then vTt else self_.evalF (f - n + i) env layer.i;
                in
                withCert layer iLayerVal
                  (wrapPayload (buildInner headVals (vPair acc vBootRefl)))
              )
              baseVal
              (builtins.genList (x: x) n)
      else if t == "desc-ind" then
        self_.vDescIndF f (ev tm.D) (ev tm.motive) (ev tm.step) (ev tm.i) (ev tm.scrut)

      else if t == "desc-desc-app" then
        let
          iLevVal =
            if tm.iLev.tag != "level-zero"
            then ev tm.iLev
            else vLevelZero;
        in
        self_.mkDescDescAppVF f iLevVal (ev tm.I) (ev tm.L)

      # Generic canonical application. Evaluates the body and currying-
      # applies it to each param; stamps the result `VDescCon` with
      # `_canonRef = { id; params; }` so conv/quote short-circuit on the
      # canonical identity. The smart-form's static contract requires the
      # body to reduce to a curried chain of `VLam`s yielding a VDescCon.
      else if t == "canon-app" then
        self_.mkCanonAppVF f tm.id (map ev tm.params) (ev tm.body)

      # Kernel-primitive `interpD` / `allD` / `everywhereD`. Level-zero
      # fast-path on `tm.level` (and `tm.K` where present) mirrors the
      # `desc-arg` shape — the prelude's homogeneous-at-zero call sites
      # bypass the eval pipeline on a `mkLevelZero` literal.
      else if t == "interp-d" then
        self_.vInterpDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I)
          (ev tm.D)
          (ev tm.X)
          (ev tm.i)
      else if t == "all-d" then
        self_.vAllDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I)
          (ev tm.D)
          (if tm.K.tag == "level-zero" then vLevelZero else ev tm.K)
          (ev tm.X)
          (ev tm.M)
          (ev tm.i)
          (ev tm.d)
      else if t == "everywhere-d" then
        self_.vEverywhereDF f
          (if tm.level.tag == "level-zero" then vLevelZero else ev tm.level)
          (ev tm.I)
          (ev tm.D)
          (if tm.K.tag == "level-zero" then vLevelZero else ev tm.K)
          (ev tm.X)
          (ev tm.M)
          (ev tm.ih)
          (ev tm.i)
          (ev tm.d)

      # Lift primitive. Level-zero fast-path on `tm.l` / `tm.m` mirrors
      # the `desc-arg` / `desc-pi` shape — both slots are most often
      # `mkLevelZero` for the prelude's homogeneous-at-zero call sites,
      # and the smart constructor's `convLevel l m` idempotent collapse
      # then fires immediately on the cached `vLevelZero` singleton.
      else if t == "lift" then
        self_.vLiftF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq)
          (ev tm.A)
      else if t == "lift-intro" then
        self_.vLiftIntroF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq)
          (ev tm.A)
          (ev tm.a)
      else if t == "lift-elim" then
        self_.vLiftElimF
          (if tm.l.tag == "level-zero" then vLevelZero else ev tm.l)
          (if tm.m.tag == "level-zero" then vLevelZero else ev tm.m)
          (ev tm.eq)
          (ev tm.A)
          (ev tm.x)

      else if t == "U" then
        if tm.level.tag == "level-zero" then vUZero
        else vU (ev tm.level)

      # Level expressions are preserved structurally. Normalisation
      # (`max a a = a`, `suc (max a b) = max (suc a) (suc b)`, zero
      # absorption, sorted spine) happens at conv time, not eval.
      else if t == "level" then vLevel
      else if t == "level-zero" then vLevelZero
      else if t == "level-suc" then vLevelSuc (ev tm.pred)
      else if t == "level-max" then vLevelMax (ev tm.lhs) (ev tm.rhs)
      # Axiomatized primitives
      else if t == "string" then vString
      else if t == "int" then vInt
      else if t == "float" then vFloat
      else if t == "attrs" then vAttrs
      else if t == "path" then vPath
      else if t == "derivation" then vDerivation
      else if t == "function" then vFunction
      else if t == "any" then vAny

      else if t == "str-eq" then self_.vStrEq (ev tm.lhs) (ev tm.rhs)

      else if t == "string-lit" then vStringLit tm.value
      else if t == "int-lit" then vIntLit tm.value
      else if t == "float-lit" then vFloatLit tm.value
      else if t == "attrs-lit" then vAttrsLit
      else if t == "path-lit" then vPathLit
      else if t == "derivation-lit" then vDerivationLit
      else if t == "fn-lit" then vFnLit
      else if t == "any-lit" then vAnyLit

      # Opaque lambda: axiomatized value — not callable in kernel
      else if t == "opaque-lam" then val.vOpaqueLam tm._fnBox (ev tm.piTy)

      # Closed-Val splice: identity on the carried Val, env-independent.
      else if t == "lit-val" then tm.val

      else throw "tc: eval unknown tag '${t}'";

  evalDescRef = eval: ref:
    ref // {
      I = eval ref.I;
      level = eval ref.level;
      params = map eval (ref.params or [ ]);
    };
in
{
  scope = {
    defaultFuel = 10000000;

    instantiateF = fuel: cl: arg: self.evalF fuel (envCons arg cl.env) cl.body;

    # Re-export the outer-`let` chain-`_layers` slicer as a self member so
    # `machine.nix` (`self.effLayers`) and `conv.nix` (`E.effLayers`) share
    # one definition.
    effLayers = effLayers;

    # Force a `VThunkTm` to its underlying Val. Prefers the record's
    # memoized `forced` field (attached by the machine's `ev`), so
    # repeated forces of the same record share one machine run; the
    # fallback covers raw `vThunkTm` records. Stepwise tail-recursive
    # against the (already-enforced) invariant that `runMachineF` Done is
    # never a `VThunkTm`: the second call is a no-op, kept defensive.
    # Non-`VThunkTm` inputs pass through. Use at every external-API entry
    # point that reads a stored sub-Val's `.tag`.
    forceVal = v:
      if (v.tag or "") != "VThunkTm" then v
      else self.forceVal
        (v.forced or (self.runMachineF self.defaultFuel v.env v.tm));

    # Canonical linearChain normal form. Force-peels a Val along its
    # recursive spine and recursively flattens nested chain-form bases
    # into a single flat layer list. Every sub-Val `.tag` inspection
    # forces first (the VThunkTm read-site invariant, value.nix:109-118):
    # a thunk hiding a recursive ctor would otherwise halt the peel one
    # layer short. One `genericClosure` -> O(1) libnix frames per layer.
    # `start` may be a raw recursive `VDescCon` or an already chain-form
    # Val; both canonicalize identically.
    #   pTag    : sum-payload discriminator tag (e.g. "VBootInr")
    #   nFields : constructor arity (#heads per layer)
    # -> { layers = [{ i; heads; cert }]  # outer-first (value.nix LayerRec)
    #    ; base                           # flat: not chain-form, not peelable
    #    ; outerTag, outerLeft, outerRight # payload-wide, from the outermost layer
    #    }
    forceAndPeelChainV = pTag: nFields: start:
      let
        F = self.forceVal;
        isRetLeafV = p0:
          let p = F p0; in
          p.tag == "VBootRefl"
          || (p.tag == "VLiftIntro" && (F p.a).tag == "VBootRefl");
        peel1 = node0:
          let node = F node0; in
          if node.tag != "VDescCon" then null
          else
            let nd = F node.d; in
            if nd.tag != pTag then null
            else
              let
                collectV = kk: p0: hs:
                  let p = F p0; in
                  if kk == nFields then
                    if p.tag != "VPair" then null
                    else if !(isRetLeafV p.snd) then null
                    else if (F p.fst).tag != "VDescCon" then null
                    else {
                      i = node.i; heads = hs; cert = node._descConCert or null;
                      left = nd.left or null; right = nd.right or null;
                      tail = p.fst;
                    }
                  else if p.tag != "VPair" then null
                  else collectV (kk + 1) p.snd (hs ++ [ p.fst ]);
              in collectV 0 nd.val [ ];
        step = node0:
          let node = F node0; in
          if (node._shape or null) == "linearChain"
          then {
            kind = "chain"; layers = effLayers node; next = node._base;
            tag = node._payloadTag or null;
            left = node._payloadLeft or null; right = node._payloadRight or null;
          }
          else
            let pl = peel1 node; in
            if pl == null then { kind = "base"; node = node; tag = null; }
            else {
              kind = "layer"; layers = [ { inherit (pl) i heads cert; } ]; next = pl.tail;
              tag = pTag; left = pl.left; right = pl.right;
            };
        walk = builtins.genericClosure {
          startSet = [ { key = 0; s = step start; } ];
          operator = item:
            if item.s.kind == "base" then [ ]
            else [ { key = item.key + 1; s = step item.s.next; } ];
        };
        payloadStep =
          let ps = builtins.filter (it: it.s.tag != null) walk;
          in if ps == [ ] then null else (builtins.head ps).s;
      in {
        layers = builtins.concatLists (map (it: it.s.layers or [ ]) walk);
        base = (builtins.elemAt walk (builtins.length walk - 1)).s.node;
        outerTag = if payloadStep == null then null else payloadStep.tag;
        outerLeft = if payloadStep == null then null else payloadStep.left;
        outerRight = if payloadStep == null then null else payloadStep.right;
      };

    # The eliminators below (vAppF, vFst, vSnd, vStrEq, vBootSumElimF, vBootJ,
    # vAbsurd, vSquashElimF, vLiftF, vLiftIntroF, vLiftElimF) tag-dispatch
    # without a `VLazyDescIndAccLayer` arm. Safe by a three-layer invariant:
    # (a) `machine.nix:1116-1128` (`stepIf` Done-transform) — `runMachineF`
    # cannot exit Done with a layer-tagged Val; the kont stack force-cascades
    # via `forceLazyLayer` first; (b) `machine.nix:142-171` (`ev` tier-3
    # dispatch) — every eliminator / desc-ind Tm routes through `evalF` =
    # `runMachineF`, inheriting (a); (c) `datatype.nix:880-936`
    # (`dispatchStep`) — user-step `ih` args are emitted as
    # `fst_ (snd_ … payloadIH)` chains, all tier-3, so layers in the
    # incoming env force through (b) before binding. Regression coverage:
    # `nix/nix-effects/tests/regression-layer-leak.nix`.
    vAppF = fuel: fn0: arg:
      let fn = self.forceVal fn0; in
      if fn.tag == "VDescViewFn" then self.applyDescViewFnByKindF fuel fn arg
      else if fn.tag == "VLam" then self.instantiateF fuel fn.closure arg
      else if fn.tag == "VNe" then vNeSnoc fn (eApp arg)
      else throw "tc: vApp on non-function (tag=${fn.tag})";

    vFst = api.leaf {
      description = "vFst: kernel pair-projection — return the first component of a `VPair`; extend the spine with `eFst` on a stuck `VNe`.";
      signature = "vFst : Val -> Val";
      value = p:
        if p.tag == "VPair" then p.fst
        else if p.tag == "VNe" then vNeSnoc p eFst
        else throw "tc: vFst on non-pair (tag=${p.tag})";
    };

    vSnd = api.leaf {
      description = "vSnd: kernel pair-projection — return the second component of a `VPair`; extend the spine with `eSnd` on a stuck `VNe`.";
      signature = "vSnd : Val -> Val";
      value = p:
        if p.tag == "VPair" then p.snd
        else if p.tag == "VNe" then vNeSnoc p eSnd
        else throw "tc: vSnd on non-pair (tag=${p.tag})";
    };

    # vStrEq — string equality primitive.
    # Both VStringLit → plus-encoded VDescCon true/false. Neutral → spine.
    # StrEq is symmetric, so we canonicalize neutral-first for the spine.
    vStrEq = lhs0: rhs0:
      let
        lhs = self.forceVal lhs0;
        rhs = self.forceVal rhs0;
        boolDescV = self.eval [ ] boolDescTm;
        eqTtV = vBootEq vUnit vTt vTt;
        vBoolTrue = vDescCon boolDescV vTt (vBootInl eqTtV eqTtV vBootRefl);
        vBoolFalse = vDescCon boolDescV vTt (vBootInr eqTtV eqTtV vBootRefl);
      in
      if lhs.tag == "VStringLit" && rhs.tag == "VStringLit" then
        if lhs.value == rhs.value then vBoolTrue else vBoolFalse
      else if lhs.tag == "VNe" then
        vNeSnoc lhs (eStrEq rhs)
      else if rhs.tag == "VNe" then
        vNeSnoc rhs (eStrEq lhs)
      else throw "tc: vStrEq on non-string (tags=${lhs.tag}, ${rhs.tag})";

    vBootSumElimF = fuel: left: right: motive: onLeft: onRight: scrut:
      if scrut.tag == "VBootInl" then self.vAppF fuel onLeft scrut.val
      else if scrut.tag == "VBootInr" then self.vAppF fuel onRight scrut.val
      else if scrut.tag == "VNe" then
        vNeSnoc scrut (eBootSumElim left right motive onLeft onRight)
      else throw "tc: vBootSumElim on non-bootstrap-sum (tag=${scrut.tag})";

    vBootJ = api.leaf {
      description = "vBootJ: J-eliminator over `VBootEq` — on `VBootRefl` returns the base case (checker has already verified the sides match); on `VNe` extends the spine with an `eBootJ` frame.";
      signature = "vBootJ : Val -> Val -> Val -> Val -> Val -> Val -> Val";
      doc = ''
        Arguments are `type lhs motive base rhs eq`. When `eq` is
        `VBootRefl`, returns `base` directly — the checker has already
        verified `lhs ≡ rhs`, so `rhs` is unused. When `eq` is `VNe`,
        preserves `rhs` in the `EBootJ` spine frame so quotation can
        reconstruct the stuck term. Any other shape is rejected with
        an internal error.
      '';
      value = type: lhs: motive: base: rhs: eq:
        if eq.tag == "VBootRefl" then base
        else if eq.tag == "VNe" then
          vNeSnoc eq (eBootJ type lhs motive base rhs)
        else throw "tc: vBootJ on non-eq (tag=${eq.tag})";
    };

    # Empty has no canonical inhabitants — non-VNe is a soundness bug.
    vAbsurd = type: x:
      if x.tag == "VNe"
      then vNeSnoc x (eAbsurd type)
      else throw "tc: vAbsurd on non-neutral (tag=${x.tag}) — Empty has no canonical inhabitant";

    # `recTrunc A B f x` for `x : Squash A` returning `Squash B`.
    # β-reduces on canonical `VSquashIntro a` to `f a`; on stuck `VNe`
    # appends an `ESquashElim` frame. Throws on any other shape — INFER
    # rejects `recTrunc` of a non-Squash value before evaluation.
    vSquashElimF = fuel: A: B: f: x:
      if x.tag == "VSquashIntro" then self.vAppF fuel f x.a
      else if x.tag == "VNe"
      then vNeSnoc x (eSquashElim A B f)
      else throw "tc: vSquashElim on non-Squash (tag=${x.tag})";

    vLiftF = api.leaf {
      description = "vLiftF: kernel `Lift l m eq A` type-former value — the type of values of `A : U(l)` transported up to `U(m)`; collapses idempotently when `convLevel l m` and composes nested Lifts.";
      signature = "vLiftF : Val -> Val -> Val -> Val -> Val";
      doc = ''
        Idempotence: `Lift l l _ A ≡ A` for homogeneous code — returns
        `A` directly when `convLevel l m`.
        Composition: `Lift l m _ (Lift l' l _ A') ≡ Lift l' m _ A'` —
        flattens by lowering the inner level. The witness slot `eq`
        is irrelevant on collapse since both bound conditions hold by
        transitivity; emit `vBootRefl` for the composed form.
      '';
      value = l: m: eq: A:
        if fx.tc.conv.convLevel l m then A
        else if builtins.isAttrs A && (A.tag or null) == "VLift"
        then vLift A.l m vBootRefl A.A
        else vLift l m eq A;
    };

    vLiftIntroF = api.leaf {
      description = "vLiftIntroF: kernel `liftIntro` value former — wraps `a : A` as a `VLift l m _ A`-typed value; idempotent at `convLevel l m`, and η-reduces a stuck `lower`-spine via `lift _ (lower _ x) ≡ x`.";
      signature = "vLiftIntroF : Val -> Val -> Val -> Val -> Val -> Val";
      doc = ''
        Witness-irrelevance is enforced structurally: levels are
        compared via `convLevel` and the carried `A` via syntactic
        equality. The spine's `eq` field is not consulted. The
        η-reduction inspects the tail of a `VNe` spine for an
        `ELiftElim` frame whose parameters match; on hit, drops the
        frame to yield the inner stuck term.
      '';
      value = l: m: eq: A: a:
        if fx.tc.conv.convLevel l m then a
        else if a.tag == "VNe" && a.spine != [ ]
          && (
          let last = builtins.elemAt a.spine (builtins.length a.spine - 1);
          in last.tag == "ELiftElim"
            && fx.tc.conv.convLevel last.l l
            && fx.tc.conv.convLevel last.m m
            && last.A == A
        )
        then
          let n = builtins.length a.spine; in
          vNe a.level (builtins.genList (i: builtins.elemAt a.spine i) (n - 1))
        else vLiftIntro l m eq A a;
    };

    vLiftElimF = api.leaf {
      description = "vLiftElimF: kernel `lower` eliminator — idempotent at `convLevel l m`; β-reduces `lower _ (lift _ a) -> a` on `VLiftIntro`; appends `ELiftElim` to a stuck `VNe` spine.";
      signature = "vLiftElimF : Val -> Val -> Val -> Val -> Val -> Val";
      value = l: m: eq: A: x:
        if fx.tc.conv.convLevel l m then x
        else if x.tag == "VLiftIntro" then x.a
        else if x.tag == "VNe"
        then vNeSnoc x (eLiftElim l m eq A)
        else throw "tc: vLiftElim on non-Lift (tag=${x.tag})";
    };

    mkValueF = api.leaf {
      description = "mkValueF: dispatch-algebra-parameterized core evaluator body. Kernel instantiates `mkValueF self`; overlays (notably `tc/elaborate/eval-overlay.nix`) instantiate with their own self-table to thread VMeta-aware dispatch through closure bodies, preserving kernel-purity (Abel-Pientka 2011, section 2; see `tc/elaborate/value.nix:13-17`).";
      signature = "mkValueF : Self -> Int -> Env -> Tm -> Val";
      value = mkValueF;
    };

    evalF = api.leaf {
      description = "evalF: kernel-term evaluator. Routes through the depth-budgeted hybrid in `tc/eval/direct.nix`: direct `mkValueF` recursion for shallow structural terms, the CEK machine (`tc/eval/machine.nix`) at budget exhaustion and for the tags that must see machine-internal Val tags (notably `VLazyDescIndAccLayer`). `mkValueF` remains exported for overlays (notably `tc/elaborate/eval-overlay.nix`) that compose their own self-table with VMeta-aware dispatch.";
      signature = "evalF : Int -> Env -> Tm -> Val";
      value = fuel: env: tm: self.evalHybridF fuel (envFromList env) tm;
    };

    eval = api.leaf {
      description = "eval: default-fuel wrapper around `evalF`; spends from the `defaultFuel` (10M-step) budget. The canonical evaluator entry for kernel consumers.";
      signature = "eval : Env -> Tm -> Val";
      value = self.evalF self.defaultFuel;
    };
    instantiate = api.leaf {
      description = "instantiate: default-fuel closure application — given `Closure { env; body; }` and an argument `Val`, evaluate the body in the extended environment.";
      signature = "instantiate : Closure -> Val -> Val";
      value = self.instantiateF self.defaultFuel;
    };
    vApp = api.leaf {
      description = "vApp: default-fuel kernel function-application value — beta-reduces `VLam`, extends the spine for `VNe`, threads through `VDescViewFn`.";
      signature = "vApp : Val -> Val -> Val";
      value = self.vAppF self.defaultFuel;
    };
    mkDescDescAppV = api.leaf {
      description = "mkDescDescAppV: default-fuel canonical `descDesc iLev I L`-value constructor — produces the levitated description-of-descriptions value, cached and shared across the kernel for index `I` at universe `iLev` and level `L`.";
      signature = "mkDescDescAppV : Val -> Val -> Val -> Val  -- iLev, I, L";
      value = self.mkDescDescAppVF self.defaultFuel;
    };
    vBootSumElim = api.leaf {
      description = "vBootSumElim: default-fuel boot-sum eliminator — dispatches `VBootInl` to `onLeft` and `VBootInr` to `onRight`; extends the spine on `VNe`.";
      signature = "vBootSumElim : Val -> Val -> Val -> Val -> Val -> Val -> Val";
      value = self.vBootSumElimF self.defaultFuel;
    };
    vSquashElim = self.vSquashElimF self.defaultFuel;
  };

  tests =
    let
      T = fx.tc.term;
      H = fx.tc.hoas;
      HI = fx.tc.hoas._internal._indexed;
      inherit (val) freshVar;
      inherit (self) eval instantiate;

      idTm = T.mkLam "x" T.mkUnit (T.mkVar 0);
      appIdTt = T.mkApp idTm T.mkTt;
      encRet = H.elab (H.retI H.unit 0 H.tt);
      encArg = H.elab (H.descArg H.unit 0 H.nat (_: H.retI H.unit 0 H.tt));
      encArg1 = H.elab (H.descArg H.unit 1 (H.u 0) (_: H.retI H.unit 1 H.tt));
      encRec = H.elab (HI.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
      encPi = H.elab (H.descPi 0 H.nat (H.retI H.unit 0 H.tt));
      descViewOf = tm: self.descView (eval [ ] tm);
    in
    {
      "eval-var-0" = { expr = (eval [ vTt vUnit ] (T.mkVar 0)).tag; expected = "VTt"; };
      "eval-var-1" = { expr = (eval [ vTt vUnit ] (T.mkVar 1)).tag; expected = "VUnit"; };

      "eval-let" = {
        expr = (eval [ ] (T.mkLet "x" T.mkUnit T.mkTt (T.mkVar 0))).tag;
        expected = "VTt";
      };

      "eval-ann" = {
        expr = (eval [ ] (T.mkAnn T.mkTt T.mkUnit)).tag;
        expected = "VTt";
      };

      "eval-lam" = { expr = (eval [ ] idTm).tag; expected = "VLam"; };
      "eval-pi" = { expr = (eval [ ] (T.mkPi "x" T.mkUnit T.mkUnit)).tag; expected = "VPi"; };
      "eval-app-beta" = {
        expr = (eval [ ] appIdTt).tag;
        expected = "VTt";
      };
      "eval-app-stuck" = {
        expr = (eval [ (freshVar 0) ] (T.mkApp (T.mkVar 0) T.mkTt)).tag;
        expected = "VNe";
      };

      "eval-sigma" = { expr = (eval [ ] (T.mkSigma "x" T.mkUnit T.mkUnit)).tag; expected = "VSigma"; };
      "eval-pair" = { expr = (eval [ ] (T.mkPair T.mkTt T.mkTt)).tag; expected = "VPair"; };
      "eval-fst" = {
        expr = (eval [ ] (T.mkFst (T.mkPair T.mkTt T.mkTt))).tag;
        expected = "VTt";
      };
      "eval-snd" = {
        expr = (eval [ ] (T.mkSnd (T.mkPair T.mkTt T.mkTt))).tag;
        expected = "VTt";
      };
      "eval-fst-stuck" = {
        expr = (eval [ (freshVar 0) ] (T.mkFst (T.mkVar 0))).tag;
        expected = "VNe";
      };

      "eval-unit" = { expr = (eval [ ] T.mkUnit).tag; expected = "VUnit"; };
      "eval-tt" = { expr = (eval [ ] T.mkTt).tag; expected = "VTt"; };

      "eval-boot-sum" = { expr = (eval [ ] (T.mkBootSum T.mkUnit T.mkUnit)).tag; expected = "VBootSum"; };
      "eval-boot-inl" = { expr = (eval [ ] (T.mkBootInl T.mkUnit T.mkUnit T.mkTt)).tag; expected = "VBootInl"; };
      "eval-boot-inr" = { expr = (eval [ ] (T.mkBootInr T.mkUnit T.mkUnit T.mkTt)).tag; expected = "VBootInr"; };
      "eval-boot-sum-elim-inl" = {
        expr = (eval [ ] (T.mkBootSumElim T.mkUnit T.mkUnit
          (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
          (T.mkLam "x" T.mkUnit T.mkTt)
          (T.mkLam "y" T.mkUnit T.mkTt)
          (T.mkBootInl T.mkUnit T.mkUnit T.mkTt))).tag;
        expected = "VTt";
      };
      "eval-boot-sum-elim-inr" = {
        expr = (eval [ ] (T.mkBootSumElim T.mkUnit T.mkUnit
          (T.mkLam "s" (T.mkBootSum T.mkUnit T.mkUnit) T.mkUnit)
          (T.mkLam "x" T.mkUnit T.mkTt)
          (T.mkLam "y" T.mkUnit T.mkTt)
          (T.mkBootInr T.mkUnit T.mkUnit T.mkTt))).tag;
        expected = "VTt";
      };

      "eval-eq" = { expr = (eval [ ] (T.mkBootEq T.mkUnit T.mkTt T.mkTt)).tag; expected = "VBootEq"; };
      "eval-refl" = { expr = (eval [ ] T.mkBootRefl).tag; expected = "VBootRefl"; };
      "eval-funext" = { expr = (eval [ ] T.mkFunext).tag; expected = "VFunext"; };
      "eval-squash" = { expr = (eval [ ] (T.mkSquash T.mkUnit)).tag; expected = "VSquash"; };
      "eval-squash-A" = { expr = (eval [ ] (T.mkSquash T.mkUnit)).A.tag; expected = "VUnit"; };
      "eval-squash-intro" = {
        expr = (eval [ ] (T.mkSquashIntro T.mkTt)).tag;
        expected = "VSquashIntro";
      };
      "eval-squash-intro-a" = {
        expr = (eval [ ] (T.mkSquashIntro T.mkTt)).a.tag;
        expected = "VTt";
      };
      "eval-squash-elim-beta" = {
        # recTrunc Unit Unit (λ_:Unit. squashIntro tt) (squashIntro tt) → squashIntro tt
        expr =
          let
            f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
            e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkSquashIntro T.mkTt);
          in
          (eval [ ] e).tag;
        expected = "VSquashIntro";
      };
      "eval-squash-elim-stuck" = {
        # recTrunc on a stuck VNe leaves an ESquashElim spine frame.
        expr =
          let
            f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
            e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkVar 0);
          in
          (eval [ (freshVar 0) ] e).tag;
        expected = "VNe";
      };
      "eval-squash-elim-stuck-spine-tag" = {
        expr =
          let
            f = T.mkLam "_" T.mkUnit (T.mkSquashIntro T.mkTt);
            e = T.mkSquashElim T.mkUnit T.mkUnit f (T.mkVar 0);
            r = eval [ (freshVar 0) ] e;
          in
          (builtins.head r.spine).tag;
        expected = "ESquashElim";
      };
      "eval-j-refl" = {
        expr = (eval [ ] (T.mkBootJ T.mkUnit T.mkTt
          (T.mkLam "y" T.mkUnit (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) T.mkUnit))
          T.mkTt
          T.mkTt
          T.mkBootRefl)).tag;
        expected = "VTt";
      };
      "eval-j-stuck" = {
        expr = (eval [ (freshVar 0) ] (T.mkBootJ T.mkUnit T.mkTt
          (T.mkLam "y" T.mkUnit (T.mkLam "e" (T.mkBootEq T.mkUnit T.mkTt (T.mkVar 0)) (T.mkU T.mkLevelZero)))
          (T.mkU T.mkLevelZero)
          T.mkTt
          (T.mkVar 0))).tag;
        expected = "VNe";
      };

      "eval-U0" = { expr = (eval [ ] (T.mkU T.mkLevelZero)).tag; expected = "VU"; };
      "eval-U0-level" = {
        expr = (eval [ ] (T.mkU T.mkLevelZero)).level.tag;
        expected = "VLevelZero";
      };
      "eval-U1-level" = {
        expr = (eval [ ] (T.mkU (T.mkLevelSuc T.mkLevelZero))).level.tag;
        expected = "VLevelSuc";
      };
      "eval-U-level-max" = {
        expr = (eval [ ] (T.mkU (T.mkLevelMax T.mkLevelZero
          (T.mkLevelSuc T.mkLevelZero)))).level.tag;
        expected = "VLevelMax";
      };

      "eval-string" = { expr = (eval [ ] T.mkString).tag; expected = "VString"; };
      "eval-int" = { expr = (eval [ ] T.mkInt).tag; expected = "VInt"; };
      "eval-float" = { expr = (eval [ ] T.mkFloat).tag; expected = "VFloat"; };
      "eval-attrs" = { expr = (eval [ ] T.mkAttrs).tag; expected = "VAttrs"; };
      "eval-path" = { expr = (eval [ ] T.mkPath).tag; expected = "VPath"; };
      "eval-derivation" = { expr = (eval [ ] T.mkDerivation).tag; expected = "VDerivation"; };
      "eval-function" = { expr = (eval [ ] T.mkFunction).tag; expected = "VFunction"; };
      "eval-any" = { expr = (eval [ ] T.mkAny).tag; expected = "VAny"; };
      "eval-string-lit" = { expr = (eval [ ] (T.mkStringLit "hello")).tag; expected = "VStringLit"; };
      "eval-string-lit-value" = { expr = (eval [ ] (T.mkStringLit "hello")).value; expected = "hello"; };
      "eval-int-lit" = { expr = (eval [ ] (T.mkIntLit 42)).tag; expected = "VIntLit"; };
      "eval-int-lit-value" = { expr = (eval [ ] (T.mkIntLit 42)).value; expected = 42; };
      "eval-float-lit" = { expr = (eval [ ] (T.mkFloatLit 3.14)).tag; expected = "VFloatLit"; };
      "eval-float-lit-value" = { expr = (eval [ ] (T.mkFloatLit 3.14)).value; expected = 3.14; };
      "eval-attrs-lit" = { expr = (eval [ ] T.mkAttrsLit).tag; expected = "VAttrsLit"; };
      "eval-path-lit" = { expr = (eval [ ] T.mkPathLit).tag; expected = "VPathLit"; };
      "eval-derivation-lit" = { expr = (eval [ ] T.mkDerivationLit).tag; expected = "VDerivationLit"; };
      "eval-fn-lit" = { expr = (eval [ ] T.mkFnLit).tag; expected = "VFnLit"; };
      "eval-any-lit" = { expr = (eval [ ] T.mkAnyLit).tag; expected = "VAnyLit"; };

      "instantiate-identity" = {
        expr = (instantiate (mkClosure [ ] (T.mkVar 0)) vTt).tag;
        expected = "VTt";
      };
      "instantiate-const" = {
        expr = (instantiate (mkClosure [ vTt ] (T.mkVar 1)) vUnit).tag;
        expected = "VTt";
      };

      "eval-desc" = { expr = (eval [ ] (T.mkDesc T.mkLevelZero T.mkUnit)).tag; expected = "VDesc"; };
      "eval-desc-ret" = { expr = (descViewOf encRet).idx; expected = 0; };
      "eval-desc-arg" = {
        expr = (descViewOf encArg).idx;
        expected = 1;
      };
      "eval-desc-arg-sort" = {
        expr = (descViewOf encArg).sTy.tag;
        expected = "VMu";
      };
      "eval-desc-arg-level-one-sort" = {
        expr = (descViewOf encArg1).sTy.tag;
        expected = "VU";
      };
      "eval-desc-rec" = {
        expr = (descViewOf encRec).idx;
        expected = 2;
      };
      "eval-desc-pi" = {
        expr = (descViewOf encPi).idx;
        expected = 3;
      };
      "eval-desc-pi-S" = {
        expr = (descViewOf encPi).sTy.tag;
        expected = "VMu";
      };
      "eval-desc-pi-D" = {
        expr = (self.descView (descViewOf encPi).sub).idx;
        expected = 0;
      };
      "eval-mu" = {
        expr = (eval [ ] (T.mkMu T.mkUnit encRet T.mkTt)).tag;
        expected = "VMu";
      };
      "eval-desc-con" = {
        expr = (eval [ ] (T.mkDescCon encRet T.mkTt T.mkBootRefl)).tag;
        expected = "VDescCon";
      };
      "eval-generated-list-5000" = {
        expr =
          let
            bigList = builtins.foldl'
              (acc: _:
                H.cons H.zero acc
              )
              H.nil
              (builtins.genList (x: x) 5000);
          in
          (eval [ ] (H.checkHoas (H.listOf H.nat) bigList)).tag;
        expected = "VDescCon";
      };
      "eval-desc-ind-stuck" = {
        # desc-ind on a neutral scrutinee produces VNe
        expr = (eval [ (freshVar 0) ] (T.mkDescInd encRet
          (T.mkVar 0)
          (T.mkVar 0)
          T.mkTt
          (T.mkVar 0))).tag;
        expected = "VNe";
      };

      # interp-d / all-d / everywhere-d Tm dispatch.
      "eval-interp-d-ret" = {
        # interpD 0 Unit (descRet tt) (λ_:Unit. Unit) tt = Lift 0 0 _ (Eq Unit tt tt) ≡ Eq Unit tt tt.
        expr = (eval [ ] (T.mkInterpD T.mkLevelZero T.mkUnit
          encRet
          (T.mkLam "_" T.mkUnit T.mkUnit)
          T.mkTt)).tag;
        expected = "VBootEq";
      };
      "eval-interp-d-stuck" = {
        # interpD on a stuck D produces VNe with EInterpD frame.
        expr = (eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
          (T.mkVar 0)
          (T.mkLam "_" T.mkUnit T.mkUnit)
          T.mkTt)).tag;
        expected = "VNe";
      };
      "eval-interp-d-stuck-spine-tag" = {
        expr =
          let
            r = eval [ (freshVar 0) ] (T.mkInterpD T.mkLevelZero T.mkUnit
              (T.mkVar 0)
              (T.mkLam "_" T.mkUnit T.mkUnit)
              T.mkTt);
          in
          (builtins.head r.spine).tag;
        expected = "EInterpD";
      };
      "eval-all-d-ret" = {
        # allD 0 Unit (descRet tt) 0 X M tt refl = Lift 0 0 _ Unit ≡ Unit.
        expr = (eval [ ] (T.mkAllD T.mkLevelZero T.mkUnit
          encRet
          T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkUnit)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
          T.mkTt
          T.mkBootRefl)).tag;
        expected = "VUnit";
      };
      "eval-all-d-stuck-spine-tag" = {
        expr =
          let
            r = eval [ (freshVar 0) ] (T.mkAllD T.mkLevelZero T.mkUnit
              (T.mkVar 0)
              T.mkLevelZero
              (T.mkLam "_" T.mkUnit T.mkUnit)
              (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
              T.mkTt
              T.mkBootRefl);
          in
          (builtins.head r.spine).tag;
        expected = "EAllD";
      };
      "eval-everywhere-d-ret" = {
        # everywhereD 0 Unit (descRet tt) 0 X M ih tt refl
        #   = liftIntro 0 0 refl Unit tt ≡ tt.
        expr = (eval [ ] (T.mkEverywhereD T.mkLevelZero T.mkUnit
          encRet
          T.mkLevelZero
          (T.mkLam "_" T.mkUnit T.mkUnit)
          (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
          (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit (T.mkU T.mkLevelZero)))
          T.mkTt
          T.mkBootRefl)).tag;
        expected = "VTt";
      };
      "eval-everywhere-d-stuck-spine-tag" = {
        expr =
          let
            r = eval [ (freshVar 0) ] (T.mkEverywhereD T.mkLevelZero T.mkUnit
              (T.mkVar 0)
              T.mkLevelZero
              (T.mkLam "_" T.mkUnit T.mkUnit)
              (T.mkLam "i" T.mkUnit (T.mkLam "_" T.mkUnit (T.mkU T.mkLevelZero)))
              (T.mkLam "j" T.mkUnit (T.mkLam "x" T.mkUnit (T.mkU T.mkLevelZero)))
              T.mkTt
              T.mkBootRefl);
          in
          (builtins.head r.spine).tag;
        expected = "EEverywhereD";
      };

      "eval-desc-ind-ret-con" = {
        # ind (ret tt) P (λi d ih. tt) tt (con tt refl) = tt
        expr =
          let
            D = encRet;
            P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
            step = T.mkLam "i" T.mkUnit
              (T.mkLam "d" T.mkUnit
                (T.mkLam "ih" T.mkUnit T.mkTt));
            scrut = T.mkDescCon D T.mkTt T.mkBootRefl;
          in
          (eval [ ] (T.mkDescInd D P step T.mkTt scrut)).tag;
        expected = "VTt";
      };
      "eval-desc-ind-arg-con" = {
        # D = arg Nat (λ_. ret tt), ind D P step tt (con tt (zero, refl)) = tt
        expr =
          let
            D = encArg;
            P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
            step = T.mkLam "i" T.mkUnit
              (T.mkLam "d" (T.mkU T.mkLevelZero)
                (T.mkLam "ih" T.mkUnit T.mkTt));
            scrut = T.mkDescCon D T.mkTt (T.mkPair (H.elab H.zero) T.mkBootRefl);
          in
          (eval [ ] (T.mkDescInd D P step T.mkTt scrut)).tag;
        expected = "VTt";
      };
      # A computed motive (here behind an identity application) reaches the
      # machine as a deferred Tm; the VDescCon arm must force it through the
      # driver before reading its domain. Exercised through quote of a stuck
      # everywhere-d spine over a neutral desc — the spine embeds muFam/ihVal
      # whose binder domains read motive.domain.
      "eval-desc-ind-deferred-motive-nf" = {
        expr =
          let
            D = encRet;
            P = T.mkLam "i" T.mkUnit (T.mkLam "_" (T.mkMu T.mkUnit D T.mkTt) T.mkUnit);
            deferredP = T.mkApp (T.mkLam "p" T.mkUnit (T.mkVar 0)) P;
            step = T.mkLam "i" T.mkUnit
              (T.mkLam "d" T.mkUnit
                (T.mkLam "ih" T.mkUnit (T.mkVar 0)));
            scrut = T.mkDescCon (T.mkVar 0) T.mkTt T.mkBootRefl;
            run = motive:
              (fx.tc.quote.nf [ (freshVar 0) ]
                (T.mkDescInd (T.mkVar 0) motive step T.mkTt scrut)).tag;
          in
          { control = run P; probe = run deferredP; };
        expected = { control = "everywhere-d"; probe = "everywhere-d"; };
      };

      # Lift primitive — type-former, introducer, eliminator.
      "eval-lift-idempotent" = {
        # Lift l l _ A ≡ A — homogeneous lift idempotence. Both levels
        # mkLevelZero, so convLevel fires and the smart constructor returns
        # A directly.
        expr = (eval [ ] (T.mkLift T.mkLevelZero T.mkLevelZero T.mkBootRefl T.mkUnit)).tag;
        expected = "VUnit";
      };
      "eval-lift-distinct-levels" = {
        # 0 < 1: convLevel rejects, vLiftF falls through to constructor.
        expr = (eval [ ] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl
          T.mkUnit)).tag;
        expected = "VLift";
      };
      "eval-lift-distinct-levels-A" = {
        expr = (eval [ ] (T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl
          T.mkUnit)).A.tag;
        expected = "VUnit";
      };
      "eval-lift-composition" = {
        # Lift 0 2 _ (Lift 0 1 _ Unit) collapses to Lift 0 2 _ Unit by
        # the inner-Lift composition rule (witness combined into vBootRefl).
        expr =
          let
            inner = T.mkLift T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit;
            outer = T.mkLift T.mkLevelZero
              (T.mkLevelSuc (T.mkLevelSuc T.mkLevelZero))
              T.mkBootRefl
              inner;
          in
          (eval [ ] outer).A.tag;
        # Composition collapses A to the deepest underlying type (Unit).
        expected = "VUnit";
      };

      "eval-lift-intro-idempotent" = {
        # lift l l _ A a ≡ a (η-collapse on idempotent Lift)
        expr = (eval [ ] (T.mkLiftIntro T.mkLevelZero T.mkLevelZero T.mkBootRefl
          T.mkUnit
          T.mkTt)).tag;
        expected = "VTt";
      };
      "eval-lift-intro-distinct-levels" = {
        # 0 < 1: builds a VLiftIntro cell.
        expr = (eval [ ] (T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
          T.mkBootRefl
          T.mkUnit
          T.mkTt)).tag;
        expected = "VLiftIntro";
      };

      "eval-lift-elim-idempotent" = {
        # lower l l _ A x ≡ x (idempotent at l=m)
        expr = (eval [ ] (T.mkLiftElim T.mkLevelZero T.mkLevelZero T.mkBootRefl
          T.mkUnit
          T.mkTt)).tag;
        expected = "VTt";
      };
      "eval-lift-elim-beta" = {
        # lower (lift a) → a
        expr =
          let
            inner = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              T.mkTt;
            outer = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              inner;
          in
          (eval [ ] outer).tag;
        expected = "VTt";
      };
      "eval-lift-elim-stuck" = {
        # lower on a neutral produces VNe with ELiftElim spine entry.
        expr = (eval [ (freshVar 0) ]
          (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
            T.mkBootRefl
            T.mkUnit
            (T.mkVar 0))).tag;
        expected = "VNe";
      };
      "eval-lift-elim-stuck-spine-tag" = {
        expr =
          let
            r = eval [ (freshVar 0) ]
              (T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
                T.mkBootRefl
                T.mkUnit
                (T.mkVar 0));
          in
          (builtins.elemAt r.spine 0).tag;
        expected = "ELiftElim";
      };

      "eval-lift-intro-eta-stuck" = {
        # lift (lower x) on a stuck `x` η-reduces by dropping the
        # trailing ELiftElim from the spine.
        expr =
          let
            lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              (T.mkVar 0);
            wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              lowerd;
          in
          (eval [ (freshVar 0) ] wrapped).tag;
        expected = "VNe";
      };
      "eval-lift-intro-eta-spine-empty" = {
        # After η, the only spine entry (the ELiftElim) is gone.
        expr =
          let
            lowerd = T.mkLiftElim T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              (T.mkVar 0);
            wrapped = T.mkLiftIntro T.mkLevelZero (T.mkLevelSuc T.mkLevelZero)
              T.mkBootRefl
              T.mkUnit
              lowerd;
          in
          (eval [ (freshVar 0) ] wrapped).spine;
        expected = [ ];
      };

      # `desc-desc-app` eval rule stamps `_canonRef = { id;
      # params = [iLev, I, L]; }` on the outer Val produced by applying
      # `descDescVal` at `(iLev, I, L)`. `mkDescDescApp` is the
      # level-zero convenience form.
      "eval-descDescApp-has-canonRef" = {
        expr = (eval [ ] (T.mkDescDescApp T.mkUnit T.mkLevelZero)) ? _canonRef;
        expected = true;
      };
      "eval-descDescApp-canonRef-id" = {
        expr = (eval [ ] (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.id;
        expected = "descDesc";
      };
      "eval-descDescApp-canonRef-params-iLev" = {
        expr = (builtins.elemAt
          (eval [ ] (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.params
          0).tag;
        expected = "VLevelZero";
      };
      "eval-descDescApp-canonRef-params-I" = {
        expr = (builtins.elemAt
          (eval [ ] (T.mkDescDescApp T.mkUnit T.mkLevelZero))._canonRef.params
          1).tag;
        expected = "VUnit";
      };
      "eval-descDescApp-canonRef-params-L" = {
        expr = (builtins.elemAt
          (eval [ ] (T.mkDescDescApp T.mkUnit (T.mkLevelSuc T.mkLevelZero)))._canonRef.params
          2).tag;
        expected = "VLevelSuc";
      };
      "eval-descDescAppAt-canonRef-params-iLev" = {
        expr = (builtins.elemAt
          (eval [ ] (T.mkDescDescAppAt
            (T.mkLevelSuc T.mkLevelZero)
            T.mkUnit
            T.mkLevelZero))._canonRef.params
          0).tag;
        expected = "VLevelSuc";
      };
    };
}
