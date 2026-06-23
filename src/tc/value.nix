# Type-checking kernel: Value constructors (Val)
#
# Values are the result of evaluation. They use de Bruijn levels
# (counting outward from top of context) instead of indices.
# Closures are defunctionalized: { env, body } — no Nix lambdas in TCB.
# Neutrals use spine representation: { tag, level, spine }.
#
# Spec reference: kernel-spec.md §3
{ api, ... }:
let
  # -- Environments: singly-linked cons cells (de Bruijn). --
  # envNil = null; head = index 0 (most-recently-bound). Extension
  # (envCons) is O(1) — no list copy, no cached field. Both length
  # (envLen) and lookup (envNth) walk the spine ITERATIVELY (genericClosure
  # / foldl' over a range) so deep environments clear BOTH the native
  # C-stack and Nix's max-call-depth. A cached `depth` field is rejected:
  # `depth = tail.depth + 1` is an N-deep recursion whether forced lazily
  # (at envLen) or strictly (the evaluator threads env as nested envCons
  # thunks, so `seq`-ing depth forces the whole tail chain) — either way
  # it overflows at ~10000, the very bug this representation fixes.
  # envFromList is idempotent on cons (isList guard) so normalizing at
  # evaluator entry points is O(1) on already-normalized environments.
  envNil = null;
  envCons = x: e: { head = x; tail = e; };
  # `envCons`/`envNth` are also INLINED at the hot evaluator arms — as
  # `{ head = …; tail = …; }` literals at the extension sites and as an
  # unrolled i≤7 select at the var sites. That inlining IS the frame-cut;
  # do not re-wrap those sites into a call, it puts back the env frame the
  # inline removes.
  envLen = e:
    if e == null then 0
    else builtins.length (builtins.genericClosure {
      startSet = [ { key = 0; cur = e; } ];
      operator = item:
        if item.cur.tail == null then [ ]
        else [ { key = item.key + 1; cur = item.cur.tail; } ];
    });
  # Small indices (de Bruijn refs are recently-bound-dominant) take an
  # unrolled select chain — no genList range, no foldl' frame. The de
  # Bruijn INDEX stays shallow even when env DEPTH grows large (measured
  # max index 12 on the hot workload); i≤7 covers ~98% of lookups, so the
  # unroll stops there and rarer deeper lookups fall to the iterative
  # tail, which also keeps the C-stack/call-depth guarantee on
  # pathological indices.
  envNth = e: i:
    # A plain Nix list (elaborate-layer list-contexts) is indexed verbatim;
    # cons spines (the kernel typing context + evaluator env) take the
    # iterative walk below. Mirrors envFromList's isList idempotence.
    if builtins.isList e then builtins.elemAt e i
    else if i == 0 then e.head
    else if i == 1 then e.tail.head
    else if i == 2 then e.tail.tail.head
    else if i == 3 then e.tail.tail.tail.head
    else if i == 4 then e.tail.tail.tail.tail.head
    else if i == 5 then e.tail.tail.tail.tail.tail.head
    else if i == 6 then e.tail.tail.tail.tail.tail.tail.head
    else if i == 7 then e.tail.tail.tail.tail.tail.tail.tail.head
    else (builtins.foldl' (acc: _: acc.tail)
      e.tail.tail.tail.tail.tail.tail.tail.tail
      (builtins.genList (x: x) (i - 8))).head;
  # Materialize a de Bruijn spine into an index-ordered Nix list (index 0
  # = most-recently-bound = head). Iterative (genericClosure) so deep
  # spines stay host-stack- and call-depth-flat; tolerates a null- or
  # list-terminated spine (a plain Nix list passes through verbatim, a
  # cons spine ending in a list appends that tail). Inverse of envFromList
  # on cons inputs; the read counterpart consumers reach for when they
  # need every element (e.g. an `any`/`map` over the whole context), not
  # an indexed lookup (envNth) or just the length (envLen).
  envToList = e:
    if builtins.isList e then e
    else if e == null then [ ]
    else
      let
        cells = builtins.genericClosure {
          startSet = [ { key = 0; cur = e; } ];
          operator = s:
            if builtins.isAttrs s.cur.tail
            then [ { key = s.key + 1; cur = s.cur.tail; } ]
            else [ ];
        };
        last = (builtins.elemAt cells (builtins.length cells - 1)).cur.tail;
        tailList = if builtins.isList last then last else [ ];
      in
      map (s: s.cur.head) cells ++ tailList;
  envReverse = xs: builtins.foldl' (acc: x: [ x ] ++ acc) [ ] xs;
  envFromList = xs:
    if builtins.isList xs
    then builtins.foldl' (acc: x: envCons x acc) envNil (envReverse xs)
    else xs;
  envPrepend = xs: e: builtins.foldl' (acc: x: envCons x acc) e (envReverse xs);

  # -- Closures --
  # `env` is normalized to cons cells so the ~30 explicit-list
  # `mkClosure [ … ]` eliminator sites need no change.
  mkClosure = env: body: { env = envFromList env; inherit body; };

  # Instantiate: eval(envCons arg env, body) — caller provides eval function
  # This module only defines the data; eval.nix provides instantiation.

  # -- Value constructors --

  # Functions
  vLam = name: domain: closure: { tag = "VLam"; inherit name domain closure; };
  vPi = name: domain: closure: { tag = "VPi"; inherit name domain closure; };

  # Pairs
  vSigma = name: fst: closure: { tag = "VSigma"; inherit name fst closure; };
  vPair = fst: snd: { tag = "VPair"; inherit fst snd; };

  # Unit
  vUnit = { tag = "VUnit"; };
  vTt = { tag = "VTt"; };

  # Empty
  vEmpty = { tag = "VEmpty"; };

  # Bootstrap coproduct
  vBootSum = left: right: { tag = "VBootSum"; inherit left right; };
  vBootInl = left: right: val: { tag = "VBootInl"; inherit left right val; };
  vBootInr = left: right: val: { tag = "VBootInr"; inherit left right val; };

  # Identity
  vBootEq = type: lhs: rhs: { tag = "VBootEq"; inherit type lhs rhs; };
  vBootRefl = { tag = "VBootRefl"; };

  # Propositional truncation. `Squash A : U(l)` for `A : U(l)`. Any two
  # inhabitants of `Squash A` are conv-equal — proof irrelevance is
  # definitional. Lives at the same universe as `A`; no separate SProp
  # sort. The `recTrunc` eliminator's motive is restricted to
  # `Squash`-typed targets so irrelevance does not leak into observable
  # positions.
  vSquash = A: { tag = "VSquash";      inherit A; };
  vSquashIntro = a: { tag = "VSquashIntro"; inherit a; };

  # Function extensionality postulate — zero-payload atomic value.
  vFunext = { tag = "VFunext"; };

  # Descriptions
  # `desc^level I` carries an explicit universe level. The level is
  # `vLevelZero` for the prelude (no high-universe contents); higher
  # levels appear when encoded descriptions quantify over sorts at
  # strictly positive universes. Int-shim mirrors `vU`.
  #
  # `iLev` records the universe of `I` (the index sort). Defaults to
  # `vLevelZero` for the ⊤-slice prelude (`I = Unit : U(0)`). The
  # `vDesc ↔ vMu` conv unfolding at `tc/conv.nix:306-317` reads `iLev`
  # to construct `expectedD = mkDescDescAppV iLev I level`; conv has no
  # `typeOf` access, so `iLev` must travel on VDesc itself.
  vDescAt = level: iLev: I: { tag = "VDesc"; inherit level I iLev; };
  vDesc = level: I: vDescAt level vLevelZero I;
  vMu = I: D: i: { tag = "VMu"; inherit I D i; }; # μ D i — the type at index i : I
  vDescCon = D: i: d: { tag = "VDescCon"; inherit D i d; }; # target index i carried alongside payload
  # Tagged variant of `vDescCon`. `_canonRef = { id; I; L }` stamps a
  # canonical identity on the outer VDescCon. Conv and quote
  # short-circuit on the tag instead of forcing `.D`, breaking the
  # universe-level descent that would otherwise loop when `descDesc`'s
  # own body encodes through itself.
  vDescConTagged = D: i: d: ref:
    { tag = "VDescCon"; inherit D i d; _canonRef = ref; };

  # Flat-chain VDescCon for linearChain Descs. Bijective dual of the
  # canonical N-deep VDescCon: chain-wide fields on the outer Val,
  # per-layer in `_layers` (outer-first), `.d = vTt` (no chain info).
  # Discriminator: `_shape == "linearChain"`. Outer cert is `_layers[0].cert`.
  # LayerRec = { i : Val; heads : [Val]; cert : Cert | null }
  vDescConChain = D: i: payloadTag: payloadLeft: payloadRight: layers: base:
    { tag = "VDescCon"; inherit D i;
      d = vTt;
      _shape = "linearChain";
      _payloadTag = payloadTag;
      _payloadLeft = payloadLeft;
      _payloadRight = payloadRight;
      _layers = layers;
      _base = base;
    };

  # Machine-internal deferred-layer Val for `descInd`'s linear-chain
  # accumulator. Represents one layer of a folded chain as DATA so the
  # CEK driver can expand it via kAppVV frames instead of consuming
  # libnix stack via recursive `vAppF`. Applying a `VLazyDescIndAccLayer`
  # to an argument expands to `step i d (vPair prevAcc vTt) arg` via
  # four kAppVV frames; the cascade through `prevAcc` (itself another
  # `VLazyDescIndAccLayer` for non-base layers) resolves through the
  # driver's kont stack — never through libnix recursion.
  #
  # Invariant: this tag is MACHINE-INTERNAL. The driver's `Done` handler
  # forces any `VLazyDescIndAccLayer` before returning. External code
  # (conv, quote, pretty) never observes it.
  vLazyDescIndAccLayer = step: i: d: prevAcc:
    { tag = "VLazyDescIndAccLayer"; inherit step i d prevAcc; };

  # Machine-internal deferred-Tm Val. `ev` returns this for any
  # non-atomic Tm so sub-Val fields stay unevaluated until tag-checked.
  # Stored sub-Val readers force via a peek helper; the driver's `Done`
  # handler forces any top-level `VThunkTm` before returning by
  # transitioning back to `Eval` (mirrors `VLazyDescIndAccLayer`).
  # The machine's `ev` constructs the record with an extra memoized
  # `forced` field (`machine.nix` `deferTm`); this raw constructor is
  # the field-shape reference and test seam.
  #
  # Invariant: this tag is MACHINE-INTERNAL. External code (conv,
  # quote, pretty, elaborate) never observes a top-level `VThunkTm`;
  # only stored sub-Val fields may carry it, and those are forced at
  # read sites.
  vThunkTm = env: tm:
    { tag = "VThunkTm"; env = envFromList env; inherit tm; };

  # `interpD` / `allD` / `everywhereD` — kernel-primitive interpretation
  # / All-witness / everywhere-recursion over Desc. Carry the same slots
  # as their Tm counterparts (mirroring `mkInterpD`/`mkAllD`/
  # `mkEverywhereD` in `term.nix`). Value-level reduction lives in
  # `eval/desc.nix`; these constructors are surface-form only — canonical
  # reductions return a different Val (Σ/Sum/Eq/Lift) per the on-cases,
  # never these tags themselves. They appear quoted only via the
  # corresponding `eInterpD`/`eAllD`/`eEverywhereD` spine frames on a
  # neutral D scrutinee.
  vInterpD = level: I: D: X: i:
    { tag = "VInterpD"; inherit level I D X i; };
  vAllD = level: I: D: K: X: M: i: d:
    { tag = "VAllD"; inherit level I D K X M i d; };
  vEverywhereD = level: I: D: K: X: M: ih: i: d:
    { tag = "VEverywhereD"; inherit level I D K X M ih i d; };

  # Lift primitive. `Lift l m eq A : U(m)` carries the bound witness
  # `eq : Eq Level (max l m) m` that proves `l ≤ m`. Conv collapses
  # `Lift l l _ A ≡ A`, `lower _ (lift _ a) ≡ a` (β), `lift _ (lower _
  # x) ≡ x` (η), and nested-Lift composition. The `eq` slot is
  # witness-irrelevant — two `vLift`s with matching `l`/`m`/`A` are
  # conv-equal regardless of the proof carried.
  vLift = l: m: eq: A: { tag = "VLift";      inherit l m eq A; };
  vLiftIntro = l: m: eq: A: a: { tag = "VLiftIntro"; inherit l m eq A a; };

  # Level sort (Tarski). `Level : U(0)`. Expressions built from
  # zero/suc/max; canonicalised at conv time.
  vLevel = { tag = "VLevel"; };
  vLevelZero = { tag = "VLevelZero"; };
  vLevelSuc = pred: { tag = "VLevelSuc"; inherit pred; };
  vLevelMax = lhs: rhs: { tag = "VLevelMax"; inherit lhs rhs; };

  # Concrete-level literal as a Level value.
  vLevelLit = n:
    if n <= 0 then vLevelZero
    else vLevelSuc (vLevelLit (n - 1));

  # Universes. Carries a Level value. Callers pass a Level Val
  # directly; integer literals must be wrapped explicitly via
  # `vLevelLit n` (or `vLevelZero` / `vLevelSuc vLevelZero` for the
  # common 0/1 cases).
  vU = level: { tag = "VU"; inherit level; };

  # Axiomatized primitives
  vString = { tag = "VString"; };
  vInt = { tag = "VInt"; };
  vFloat = { tag = "VFloat"; };
  vAttrs = { tag = "VAttrs"; };
  vPath = { tag = "VPath"; };
  vDerivation = { tag = "VDerivation"; };
  vFunction = { tag = "VFunction"; };
  vAny = { tag = "VAny"; };

  # Primitive literals
  vStringLit = s: { tag = "VStringLit"; value = s; };
  vIntLit = n: { tag = "VIntLit"; value = n; };
  vFloatLit = f: { tag = "VFloatLit"; value = f; };
  vAttrsLit = { tag = "VAttrsLit"; };
  vPathLit = { tag = "VPathLit"; };
  vDerivationLit = { tag = "VDerivationLit"; };
  vFnLit = { tag = "VFnLit"; };
  vAnyLit = { tag = "VAnyLit"; };

  # Opaque lambda value: axiomatized trust boundary for Pi.
  # fnBox is the { _fn = nixFn; } wrapper propagated from the HOAS level —
  # never reconstructed, preserving thunk identity for conv.
  # nixFn derived from fnBox for extractInner access. piTy is the evaluated VPi.
  vOpaqueLam = fnBox: piTy: { tag = "VOpaqueLam"; _fnBox = fnBox; nixFn = fnBox._fn; inherit piTy; };

  # -- Neutral spines: skew-binary random-access list (Okasaki). --
  # A spine is snoc-extended one frame at a time (deep) and read back in
  # full (quote / conv / unify). A Nix-list `spine ++ [frame]` is O(len)
  # per snoc → O(N²) memory and an N-deep force. The RAL gives O(1) snoc
  # and O(log N) index; `.spine` materializes in-order via `genList` to a
  # list byte-identical to the old `++` form, so readers are unchanged.
  # trees: cons of { w; t; next } (length O(log N), newest at front);
  # t: complete binary tree { leaf } | { node; l; r } (size 2^k-1). No
  # cached size: it is summed over the O(log N) trees iteratively, never
  # N-deep (the env-spine lesson). ralCons inspects the previous front to
  # decide a carry, so each extension must be forced as it is built
  # (`vNeSnoc` seqs the result; the machine forces each neutral to
  # dispatch on its tag) — else the cons chain is N-deep to force.
  ralCons = x: ts:
    if ts != null && ts.next != null && ts.w == ts.next.w
    then {
      w = ts.w + ts.next.w + 1;
      t = { node = x; l = ts.t; r = ts.next.t; };
      next = ts.next.next;
    }
    else { w = 1; t = { leaf = x; }; next = ts; };
  ralCount = ts:
    if ts == null then 0
    else builtins.foldl' (acc: item: acc + item.cur.w) 0
      (builtins.genericClosure {
        startSet = [ { key = 0; cur = ts; } ];
        operator = item:
          if item.cur.next == null then [ ]
          else [ { key = item.key + 1; cur = item.cur.next; } ];
      });
  ralLookup = ts: i0:
    let
      goTree = t: w: i:
        if t ? leaf then t.leaf
        else if i == 0 then t.node
        else
          let hw = (w - 1) / 2; in
          if i <= hw then goTree t.l hw (i - 1)
          else goTree t.r hw (i - 1 - hw);
      goList = c: i:
        if i < c.w then goTree c.t c.w i
        else goList c.next (i - c.w);
    in goList ts i0;
  ralFromList = xs: builtins.foldl' (acc: x: ralCons x acc) null xs;
  ralToList = ts:
    let n = ralCount ts;
    in builtins.genList (j: ralLookup ts (n - 1 - j)) n;

  # -- Neutrals (stuck computations) --
  # A neutral is a variable (identified by level) applied to a spine of
  # eliminators. `_ral` carries the spine as a RAL for O(1) snoc; `.spine`
  # is the materialized in-order list every reader consumes.
  vNe = level: spine: { tag = "VNe"; inherit level spine; _ral = ralFromList spine; };

  # Extend a neutral's spine by one frame in O(1). Reads `_ral` (never
  # `.spine`, which would re-materialize O(N) per snoc) and seqs the new
  # RAL so the machine forces the cons chain incrementally.
  vNeSnoc = neu: frame:
    let r = ralCons frame neu._ral;
    in builtins.seq r { tag = "VNe"; inherit (neu) level; _ral = r; spine = ralToList r; };

  # Fresh variable at depth d: neutral with empty spine
  freshVar = depth: vNe depth [ ];

  # -- Elimination frames (spine entries) --
  eApp = arg: { tag = "EApp"; inherit arg; };
  eFst = { tag = "EFst"; };
  eSnd = { tag = "ESnd"; };
  eBootSumElim = left: right: motive: onLeft: onRight:
    { tag = "EBootSumElim"; inherit left right motive onLeft onRight; };
  eBootJ = type: lhs: motive: base: rhs:
    { tag = "EBootJ"; inherit type lhs motive base rhs; };
  eStrEq = arg: { tag = "EStrEq"; inherit arg; };
  # intLe non-symmetric: frame tag records the neutral's side (L=lhs, R=rhs),
  # arg holds the other operand. intEq symmetric → one frame.
  eIntLeL = arg: { tag = "EIntLeL"; inherit arg; };
  eIntLeR = arg: { tag = "EIntLeR"; inherit arg; };
  eIntEq = arg: { tag = "EIntEq"; inherit arg; };
  eAbsurd = type: { tag = "EAbsurd"; inherit type; };
  eDescInd = D: motive: step: i:
    { tag = "EDescInd"; inherit D motive step i; };

  # `EInterpD` / `EAllD` / `EEverywhereD` — spine frames recording stuck
  # `interpD` / `allD` / `everywhereD` applications on a neutral D
  # scrutinee. The frame stores every slot OTHER than D (which is the
  # spine head). Quote round-trips a frame to the corresponding
  # `mkInterpD` / `mkAllD` / `mkEverywhereD` Tm. Conv compares frames
  # field-wise.
  eInterpD = level: I: X: i:
    { tag = "EInterpD"; inherit level I X i; };
  eAllD = level: I: K: X: M: i: d:
    { tag = "EAllD"; inherit level I K X M i d; };
  eEverywhereD = level: I: K: X: M: ih: i: d:
    { tag = "EEverywhereD"; inherit level I K X M ih i d; };

  # `ELiftElim` records a stuck `lower` on a neutral `Lift`-typed value.
  # The spine entry carries `l`, `m`, `eq`, `A` so a quoted spine round-
  # trips to `mkLiftElim l m eq A x`.
  eLiftElim = l: m: eq: A: { tag = "ELiftElim"; inherit l m eq A; };

  # `ESquashElim` records a stuck `recTrunc` on a neutral `Squash`-typed
  # value. Carries the motive shape (`A`, `B`) and the case function `f`
  # so a quoted spine round-trips to `mkSquashElim A B f x`.
  eSquashElim = A: B: f: { tag = "ESquashElim"; inherit A B f; };

in
api.namespace {
  description = "fx.tc.value: semantic domain produced by evaluation; values use de Bruijn LEVELS (counting outward) so substitution under binders stays unproblematic.";
  doc = ''
    # fx.tc.value — Value Domain (Val)

    Values are the semantic domain produced by evaluation. They use
    de Bruijn *levels* (counting outward from the top of the context),
    not indices, which makes weakening trivial.

    ## Closures

    `mkClosure : Env → Tm → Closure` — defunctionalized closure.
    No Nix lambdas in the TCB; a closure is `{ env, body }` where
    `body` is a kernel Tm evaluated by `eval.instantiate`.

    ## Value Constructors

    Each `v*` constructor mirrors a term constructor:

    - `vLam`, `vPi` — function values/types (carry name, domain, closure)
    - `vSigma`, `vPair` — pair types/values
    - `vUnit`, `vTt` — unit
    - `vBootSum`, `vBootInl`, `vBootInr` — bootstrap coproduct values
    - `vBootEq`, `vBootRefl` — identity values
    - `vU` — universe values
    - `vString`, `vInt`, `vFloat`, `vAttrs`, `vPath`, `vDerivation`, `vFunction`, `vAny` — primitive types
    - `vStringLit`, `vIntLit`, `vFloatLit`, `vAttrsLit`, `vPathLit`, `vDerivationLit`, `vFnLit`, `vAnyLit` — primitive literals

    ## Neutrals

    `vNe : Level → Spine → Val` — a stuck computation: a variable
    (identified by de Bruijn level) applied to a spine of eliminators.

    `freshVar : Depth → Val` — neutral with empty spine at the given depth.
    Used during type-checking to introduce fresh variables under binders.

    ## Elimination Frames (Spine Entries)

    - `eApp`, `eFst`, `eSnd` — function/pair eliminators
    - `eBootSumElim`, `eBootJ` — inductive eliminators
  '';
  tests = {
    # Closures
    "closure-env" = {
      expr = (mkClosure [ vTt ] { tag = "var"; idx = 0; }).env;
      expected = { head = vTt; tail = null; };
    };
    "closure-body" = {
      expr = (mkClosure [ ] { tag = "var"; idx = 0; }).body.tag;
      expected = "var";
    };

    # Environments
    # envLen must walk the spine iteratively — a cached `depth = tail.depth
    # + 1` field recurses N-deep (lazily at read or strictly at build) and
    # overflows max-call-depth at ~10000 on a deep environment.
    "env-deep-len" = {
      expr = envLen (builtins.foldl' (acc: _: envCons vTt acc) envNil
        (builtins.genList (i: i) 20000));
      expected = 20000;
    };
    # envToList materializes a cons spine index-ordered (head first), is
    # idempotent on a plain Nix list and maps null to [], and walks a
    # 20000-deep spine iteratively without overflow.
    "env-to-list-order" = {
      expr = envToList (envCons (vIntLit 0) (envCons (vIntLit 1) (envCons (vIntLit 2) envNil)));
      expected = [ (vIntLit 0) (vIntLit 1) (vIntLit 2) ];
    };
    "env-to-list-nil" = { expr = envToList envNil; expected = [ ]; };
    "env-to-list-list-verbatim" = {
      expr = envToList [ (vIntLit 7) (vIntLit 8) ];
      expected = [ (vIntLit 7) (vIntLit 8) ];
    };
    "env-to-list-deep" = {
      expr = builtins.length (envToList
        (builtins.foldl' (acc: _: envCons vTt acc) envNil
          (builtins.genList (i: i) 20000)));
      expected = 20000;
    };

    # Values
    "vlam-tag" = { expr = (vLam "x" vUnit (mkClosure [ ] { tag = "var"; idx = 0; })).tag; expected = "VLam"; };
    "vpi-tag" = { expr = (vPi "x" vUnit (mkClosure [ ] { tag = "unit"; })).tag; expected = "VPi"; };
    "vsigma-tag" = { expr = (vSigma "x" vUnit (mkClosure [ ] { tag = "unit"; })).tag; expected = "VSigma"; };
    "vpair-tag" = { expr = (vPair vTt vTt).tag; expected = "VPair"; };
    "vunit-tag" = { expr = vUnit.tag; expected = "VUnit"; };
    "vtt-tag" = { expr = vTt.tag; expected = "VTt"; };
    "vboot-sum-tag" = { expr = (vBootSum vUnit vUnit).tag; expected = "VBootSum"; };
    "vboot-inl-tag" = { expr = (vBootInl vUnit vUnit vTt).tag; expected = "VBootInl"; };
    "vboot-inr-tag" = { expr = (vBootInr vUnit vUnit vTt).tag; expected = "VBootInr"; };
    "veq-tag" = { expr = (vBootEq vUnit vTt vTt).tag; expected = "VBootEq"; };
    "vrefl-tag" = { expr = vBootRefl.tag; expected = "VBootRefl"; };
    "vfunext-tag" = { expr = vFunext.tag; expected = "VFunext"; };
    "vsquash-tag" = { expr = (vSquash vUnit).tag; expected = "VSquash"; };
    "vsquash-A" = { expr = (vSquash vUnit).A.tag; expected = "VUnit"; };
    "vsquashintro-tag" = { expr = (vSquashIntro vTt).tag; expected = "VSquashIntro"; };
    "vsquashintro-a" = { expr = (vSquashIntro vTt).a.tag; expected = "VTt"; };
    "esquashelim-tag" = {
      expr = (eSquashElim vUnit vUnit
        (vLam "a" vUnit (mkClosure [ ] { tag = "tt"; }))).tag;
      expected = "ESquashElim";
    };
    "vu-tag" = { expr = (vU vLevelZero).tag; expected = "VU"; };
    "vu-level-zero" = { expr = (vU vLevelZero).level.tag; expected = "VLevelZero"; };
    "vu-level-suc" = { expr = (vU (vLevelSuc vLevelZero)).level.tag; expected = "VLevelSuc"; };
    "vu-level-suc-pred" = {
      expr = (vU (vLevelSuc vLevelZero)).level.pred.tag;
      expected = "VLevelZero";
    };
    "vu-level-max" = {
      expr = (vU (vLevelMax vLevelZero vLevelZero)).level.tag;
      expected = "VLevelMax";
    };
    "vlevel-tag" = { expr = vLevel.tag; expected = "VLevel"; };
    "vlevel-zero-tag" = { expr = vLevelZero.tag; expected = "VLevelZero"; };
    "vlevel-suc-tag" = { expr = (vLevelSuc vLevelZero).tag; expected = "VLevelSuc"; };
    "vlevel-suc-pred" = { expr = (vLevelSuc vLevelZero).pred.tag; expected = "VLevelZero"; };
    "vlevel-max-tag" = { expr = (vLevelMax vLevelZero vLevelZero).tag; expected = "VLevelMax"; };
    "vlevel-lit-0-tag" = { expr = (vLevelLit 0).tag; expected = "VLevelZero"; };
    "vlevel-lit-2-tag" = { expr = (vLevelLit 2).tag; expected = "VLevelSuc"; };
    "vstring-tag" = { expr = vString.tag; expected = "VString"; };
    "vint-tag" = { expr = vInt.tag; expected = "VInt"; };
    "vfloat-tag" = { expr = vFloat.tag; expected = "VFloat"; };
    "vattrs-tag" = { expr = vAttrs.tag; expected = "VAttrs"; };
    "vpath-tag" = { expr = vPath.tag; expected = "VPath"; };
    "vderivation-tag" = { expr = vDerivation.tag; expected = "VDerivation"; };
    "vfunction-tag" = { expr = vFunction.tag; expected = "VFunction"; };
    "vany-tag" = { expr = vAny.tag; expected = "VAny"; };
    "vstringlit-tag" = { expr = (vStringLit "hi").tag; expected = "VStringLit"; };
    "vstringlit-value" = { expr = (vStringLit "hi").value; expected = "hi"; };
    "vintlit-tag" = { expr = (vIntLit 7).tag; expected = "VIntLit"; };
    "vintlit-value" = { expr = (vIntLit 7).value; expected = 7; };
    "vfloatlit-tag" = { expr = (vFloatLit 2.5).tag; expected = "VFloatLit"; };
    "vfloatlit-value" = { expr = (vFloatLit 2.5).value; expected = 2.5; };
    "vattrslit-tag" = { expr = vAttrsLit.tag; expected = "VAttrsLit"; };
    "vpathlit-tag" = { expr = vPathLit.tag; expected = "VPathLit"; };
    "vderivationlit-tag" = { expr = vDerivationLit.tag; expected = "VDerivationLit"; };
    "vfnlit-tag" = { expr = vFnLit.tag; expected = "VFnLit"; };
    "vanylit-tag" = { expr = vAnyLit.tag; expected = "VAnyLit"; };
    "vopaquelam-tag" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).tag; expected = "VOpaqueLam"; };
    "vopaquelam-piTy" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit).piTy.tag; expected = "VUnit"; };
    "vopaquelam-nixFn" = { expr = builtins.isFunction (vOpaqueLam { _fn = (x: x); } vUnit).nixFn; expected = true; };
    "vopaquelam-fnBox" = { expr = (vOpaqueLam { _fn = (x: x); } vUnit)._fnBox ? _fn; expected = true; };

    # Neutrals
    "vne-tag" = { expr = (vNe 0 [ ]).tag; expected = "VNe"; };
    "vne-level" = { expr = (vNe 3 [ ]).level; expected = 3; };
    "vne-empty-spine" = { expr = (vNe 0 [ ]).spine; expected = [ ]; };
    "freshvar-is-neutral" = { expr = (freshVar 5).tag; expected = "VNe"; };
    "freshvar-level" = { expr = (freshVar 5).level; expected = 5; };
    "freshvar-empty-spine" = { expr = (freshVar 5).spine; expected = [ ]; };

    # Spine RAL. ralToList ∘ ralFromList round-trips in order; the size
    # walk is iterative so a 20000-deep RAL counts without overflow; and
    # vNeSnoc materializes a `.spine` byte-identical to a naive `++` snoc.
    "ral-roundtrip" = {
      expr = let xs = builtins.genList (i: i) 64; in ralToList (ralFromList xs) == xs;
      expected = true;
    };
    "ral-deep-count" = {
      expr = ralCount (ralFromList (builtins.genList (i: i) 20000));
      expected = 20000;
    };
    "vne-snoc-parity" = {
      expr =
        let
          xs = builtins.genList (i: eApp (vIntLit i)) 64;
          snocced = builtins.foldl' vNeSnoc (vNe 0 [ ]) xs;
          naive = builtins.foldl' (acc: f: acc ++ [ f ]) [ ] xs;
        in snocced.spine == naive;
      expected = true;
    };

    # Elimination frames
    "eapp-tag" = { expr = (eApp vTt).tag; expected = "EApp"; };
    "efst-tag" = { expr = eFst.tag; expected = "EFst"; };
    "esnd-tag" = { expr = eSnd.tag; expected = "ESnd"; };
    "eboot-sum-elim-tag" = { expr = (eBootSumElim vUnit vUnit vUnit vTt vTt).tag; expected = "EBootSumElim"; };
    "ej-tag" = { expr = (eBootJ vUnit vTt vUnit vTt vTt).tag; expected = "EBootJ"; };

    # Descriptions (indexed)
    "vdesc-tag" = { expr = (vDesc vLevelZero vUnit).tag; expected = "VDesc"; };
    "vdesc-I" = { expr = (vDesc vLevelZero vUnit).I.tag; expected = "VUnit"; };
    "vdesc-level" = { expr = (vDesc vLevelZero vUnit).level.tag; expected = "VLevelZero"; };
    "vdesc-level-non-zero" = {
      expr = (vDesc (vLevelSuc vLevelZero) vUnit).level.tag;
      expected = "VLevelSuc";
    };
    "vmu-tag" = { expr = (vMu vUnit (freshVar 0) vTt).tag; expected = "VMu"; };
    "vmu-I" = { expr = (vMu vUnit (freshVar 0) vTt).I.tag; expected = "VUnit"; };
    "vmu-D" = { expr = (vMu vUnit (freshVar 0) vTt).D.tag; expected = "VNe"; };
    "vmu-i" = { expr = (vMu vUnit (freshVar 0) vTt).i.tag; expected = "VTt"; };
    "vdesccon-tag" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).tag;
      expected = "VDescCon";
    };
    "vdesccon-D" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).D.tag;
      expected = "VNe";
    };
    "vdesccon-i" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl).i.tag;
      expected = "VTt";
    };
    "vdesccon-tagged-tag" = {
      expr = (vDescConTagged (freshVar 0) vTt vBootRefl
        {
          id = "descDesc";
          params = [ vLevelZero vUnit vLevelZero ];
        }).tag;
      expected = "VDescCon";
    };
    "vdesccon-tagged-canonref-id" = {
      expr = (vDescConTagged (freshVar 0) vTt vBootRefl
        {
          id = "descDesc";
          params = [ vLevelZero vUnit vLevelZero ];
        })._canonRef.id;
      expected = "descDesc";
    };
    "vdesccon-untagged-has-no-canonref" = {
      expr = (vDescCon (freshVar 0) vTt vBootRefl) ? _canonRef;
      expected = false;
    };
    "vdesccon-chain-tag" = {
      expr = (vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit [ ]
        (vDescCon (freshVar 0) vTt vBootRefl)).tag;
      expected = "VDescCon";
    };
    "vdesccon-chain-shape" = {
      expr = (vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit [ ]
        (vDescCon (freshVar 0) vTt vBootRefl))._shape;
      expected = "linearChain";
    };
    "vdesccon-chain-layers-length" = {
      expr = builtins.length
        (vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit
          (builtins.genList
            (_: { i = vTt; heads = [ vTt ]; cert = null; }) 5)
          (vDescCon (freshVar 0) vTt vBootRefl))._layers;
      expected = 5;
    };
    "vdesccon-chain-base-points-to-supplied" = {
      expr = (vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit [ ]
        (vDescConTagged (freshVar 0) vTt vBootRefl
          { id = "nil"; params = [ ]; }))._base._canonRef.id;
      expected = "nil";
    };
    "vdesccon-chain-d-is-stub" = {
      # `.d` is `vTt` regardless of `_layers` length — chain info lives
      # only in `_layers`/`_base`; non-chain-aware code reading `.d.fst`
      # crashes loudly rather than silently observing a 2-step view.
      expr = (vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit
        (builtins.genList (_: { i = vTt; heads = [ vTt ]; cert = null; }) 100)
        (vDescConTagged (freshVar 0) vTt vBootRefl
          { id = "nil"; params = [ ]; })).d.tag;
      expected = "VTt";
    };
    "vdesccon-chain-payload-wrap" = {
      # Chain-wide BootSum wrapper info is preserved verbatim for quote.
      expr =
        let
          v = vDescConChain (freshVar 0) vTt "VBootInr" vUnit vUnit
            [ { i = vTt; heads = [ vTt ]; cert = null; } ]
            (vDescCon (freshVar 0) vTt vBootRefl);
        in
        { tag = v._payloadTag; left = v._payloadLeft.tag; right = v._payloadRight.tag; };
      expected = { tag = "VBootInr"; left = "VUnit"; right = "VUnit"; };
    };
    "vlazydescindacclayer-tag" = {
      expr = (vLazyDescIndAccLayer vTt vTt vTt vTt).tag;
      expected = "VLazyDescIndAccLayer";
    };
    "vlazydescindacclayer-step" = {
      expr = (vLazyDescIndAccLayer
        (vLam "x" vUnit (mkClosure [ ] { tag = "var"; idx = 0; }))
        vTt vTt vTt).step.tag;
      expected = "VLam";
    };
    "vlazydescindacclayer-prevacc" = {
      expr = (vLazyDescIndAccLayer vTt vTt vTt vBootRefl).prevAcc.tag;
      expected = "VBootRefl";
    };
    "vthunktm-tag" = {
      expr = (vThunkTm [ ] { tag = "tt"; }).tag;
      expected = "VThunkTm";
    };
    "vthunktm-env" = {
      expr = (vThunkTm [ vTt ] { tag = "var"; idx = 0; }).env;
      expected = { head = vTt; tail = null; };
    };
    "vthunktm-tm" = {
      expr = (vThunkTm [ ] { tag = "tt"; }).tm.tag;
      expected = "tt";
    };
    "edescind-tag" = { expr = (eDescInd (freshVar 0) vUnit vTt vTt).tag; expected = "EDescInd"; };
    "edescind-i" = { expr = (eDescInd (freshVar 0) vUnit vTt vTt).i.tag; expected = "VTt"; };
    # Lift primitive
    "vlift-tag" = { expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).tag; expected = "VLift"; };
    "vlift-l-zero" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).l.tag;
      expected = "VLevelZero";
    };
    "vlift-m-suc" = {
      expr = (vLift vLevelZero (vLevelSuc vLevelZero) vBootRefl vUnit).m.tag;
      expected = "VLevelSuc";
    };
    "vlift-A" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).A.tag;
      expected = "VUnit";
    };
    "vlift-eq-refl" = {
      expr = (vLift vLevelZero vLevelZero vBootRefl vUnit).eq.tag;
      expected = "VBootRefl";
    };
    "vliftintro-tag" = {
      expr = (vLiftIntro vLevelZero vLevelZero vBootRefl vUnit vTt).tag;
      expected = "VLiftIntro";
    };
    "vliftintro-a" = {
      expr = (vLiftIntro vLevelZero vLevelZero vBootRefl vUnit vTt).a.tag;
      expected = "VTt";
    };
    "eliftelim-tag" = { expr = (eLiftElim vLevelZero vLevelZero vBootRefl vUnit).tag; expected = "ELiftElim"; };
    "eliftelim-l" = { expr = (eLiftElim vLevelZero vLevelZero vBootRefl vUnit).l.tag; expected = "VLevelZero"; };
    # interpD / allD / everywhereD value forms
    "vinterpd-tag" = {
      expr = (vInterpD vLevelZero vUnit (freshVar 0) vUnit vTt).tag;
      expected = "VInterpD";
    };
    "vinterpd-D" = {
      expr = (vInterpD vLevelZero vUnit (freshVar 0) vUnit vTt).D.tag;
      expected = "VNe";
    };
    "valld-tag" = {
      expr = (vAllD vLevelZero vUnit (freshVar 0) vLevelZero vUnit vUnit vTt vBootRefl).tag;
      expected = "VAllD";
    };
    "valld-K" = {
      expr = (vAllD vLevelZero vUnit (freshVar 0)
        (vLevelSuc vLevelZero)
        vUnit
        vUnit
        vTt
        vBootRefl).K.tag;
      expected = "VLevelSuc";
    };
    "veverywhered-tag" = {
      expr = (vEverywhereD vLevelZero vUnit (freshVar 0) vLevelZero
        vUnit
        vUnit
        vUnit
        vTt
        vBootRefl).tag;
      expected = "VEverywhereD";
    };
    "einterpd-tag" = {
      expr = (eInterpD vLevelZero vUnit vUnit vTt).tag;
      expected = "EInterpD";
    };
    "einterpd-level" = {
      expr = (eInterpD vLevelZero vUnit vUnit vTt).level.tag;
      expected = "VLevelZero";
    };
    "ealld-tag" = {
      expr = (eAllD vLevelZero vUnit vLevelZero vUnit vUnit vTt vBootRefl).tag;
      expected = "EAllD";
    };
    "eeverywhered-tag" = {
      expr = (eEverywhereD vLevelZero vUnit vLevelZero vUnit vUnit vUnit vTt vBootRefl).tag;
      expected = "EEverywhereD";
    };
  };
  value = {

    mkClosure = api.leaf {
      value = mkClosure;
      description = "mkClosure: defunctionalised closure `{ env, body }` — captures the evaluation environment and the kernel `Tm` body; instantiated by `eval.instantiate` without Nix lambdas in the TCB.";
      signature = "mkClosure : Env -> Tm -> Closure";
    };

    envNil = api.leaf {
      value = envNil;
      description = "envNil: empty de Bruijn environment (the cons-cell nil).";
    };
    envCons = api.leaf {
      value = envCons;
      description = "envCons: O(1) environment extension — prepend a value as index 0; no list copy, no cached field.";
      signature = "envCons : Val -> Env -> Env";
    };
    envLen = api.leaf {
      value = envLen;
      description = "envLen: environment length (binder depth) via an iterative genericClosure spine walk — O(N) time, O(1) stack (overflow-free); no cached field, which would recurse N-deep at read or build.";
      signature = "envLen : Env -> Int";
    };
    envNth = api.leaf {
      value = envNth;
      description = "envNth: iterative de Bruijn lookup (foldl' over a range) — clears the C-stack and max-call-depth on deep environments; a plain Nix list is indexed verbatim (isList guard) so elaborate-layer list-contexts pass through unchanged.";
      signature = "envNth : Env -> Int -> Val";
    };
    envFromList = api.leaf {
      value = envFromList;
      description = "envFromList: normalize a Nix-list environment to cons cells (index 0 = list head); idempotent on cons (isList guard) so evaluator entry points normalize in O(1) on already-cons inputs.";
      signature = "envFromList : [Val] | Env -> Env";
    };
    envPrepend = api.leaf {
      value = envPrepend;
      description = "envPrepend: prepend a short Nix list of values (index 0 first) onto an environment.";
      signature = "envPrepend : [Val] -> Env -> Env";
    };
    envToList = api.leaf {
      value = envToList;
      description = "envToList: materialize a de Bruijn spine into an index-ordered Nix list (index 0 = most recent) via an iterative genericClosure walk — O(N) time, O(1) stack (overflow-free). For whole-context reads (`any`/`map`/`filter` over every binding); a plain Nix list passes through verbatim (isList guard), null yields the empty list. Inverse of envFromList on cons inputs.";
      signature = "envToList : Env -> [Val]";
    };

    vLam = api.leaf {
      value = vLam;
      description = "vLam: value-domain lambda `λ(name : domain). body` — carries a defunctionalised closure rather than a Nix function, keeping the TCB Nix-lambda-free.";
      signature = "vLam : String -> Val -> Closure -> Val";
    };
    vPi = api.leaf {
      value = vPi;
      description = "vPi: value-domain dependent function type `Π(name : domain). codomain` — carries a closure for the codomain to permit semantic substitution.";
      signature = "vPi : String -> Val -> Closure -> Val";
    };

    vSigma = api.leaf {
      value = vSigma;
      description = "vSigma: value-domain dependent pair type `Σ(name : fst). snd` — carries a closure for the snd component to permit semantic substitution.";
      signature = "vSigma : String -> Val -> Closure -> Val";
    };
    vPair = api.leaf {
      value = vPair;
      description = "vPair: value-domain pair `(fst, snd)` — components held in WHNF, projected by `eFst` / `eSnd` spine frames.";
      signature = "vPair : Val -> Val -> Val";
    };

    vUnit = api.leaf {
      value = vUnit;
      description = "vUnit: value-domain unit type — terminal type with single inhabitant `vTt`; eta-converted in `conv`.";
    };
    vTt = api.leaf {
      value = vTt;
      description = "vTt: value-domain unit value `tt` — sole inhabitant of `vUnit`; conv collapses all Unit-typed values to this.";
    };
    vEmpty = api.leaf {
      value = vEmpty;
      description = "vEmpty: value-domain empty type — initial type with no inhabitants; conv-equal in one step by tag identity.";
    };

    vBootSum = api.leaf {
      value = vBootSum;
      description = "vBootSum: value-domain bootstrap coproduct type `A + B` — used by `descPlus`'s sum-of-descriptions before generic sums become available.";
      signature = "vBootSum : Val -> Val -> Val";
    };
    vBootInl = api.leaf {
      value = vBootInl;
      description = "vBootInl: value-domain left-injection `inl(a) : A + B` — carries `leftTy` and `rightTy` for elaboration shape recovery.";
      signature = "vBootInl : Val -> Val -> Val -> Val  -- leftTy, rightTy, value";
    };
    vBootInr = api.leaf {
      value = vBootInr;
      description = "vBootInr: value-domain right-injection `inr(b) : A + B` — carries `leftTy` and `rightTy` for elaboration shape recovery.";
      signature = "vBootInr : Val -> Val -> Val -> Val  -- leftTy, rightTy, value";
    };

    vBootEq = api.leaf {
      value = vBootEq;
      description = "vBootEq: value-domain bootstrap identity type `Eq(A, a, b)` — propositional equality used by `descRet`'s level transport and by the J eliminator.";
      signature = "vBootEq : Val -> Val -> Val -> Val  -- A, a, b";
    };
    vBootRefl = api.leaf {
      value = vBootRefl;
      description = "vBootRefl: value-domain reflexivity `refl : Eq(A, a, a)` — canonical inhabitant of every reflexive identity; conv collapses all proofs of refl to this.";
    };
    vFunext = api.leaf {
      value = vFunext;
      description = "vFunext: value-domain funext axiom — given pointwise equality, produces equality of functions at `Π(a:A). B a`.";
      signature = "vFunext : Val -> Val -> Val -> Val -> Val -> Val";
    };

    vSquash = api.leaf {
      value = vSquash;
      description = "vSquash: value-domain propositional truncation `Squash A` — quotient of `A` collapsing all inhabitants to one for proof-irrelevant fields.";
      signature = "vSquash : Val -> Val";
    };
    vSquashIntro = api.leaf {
      value = vSquashIntro;
      description = "vSquashIntro: value-domain introduction of `Squash A` — lifts any inhabitant of `A` to the sole inhabitant of `Squash A`.";
      signature = "vSquashIntro : Val -> Val";
    };

    vDesc = api.leaf {
      value = vDesc;
      description = "vDesc: value-domain level-zero description type `Desc I k` at index sort `I : U(0)` and universe level `k`.";
      signature = "vDesc : Val -> Val -> Val  -- level, I";
    };
    vDescAt = api.leaf {
      value = vDescAt;
      description = "vDescAt: value-domain `Desc^k I` carrying an explicit `iLev` for the universe of `I`. The conv unfolding rule reads `iLev` to construct the expected `mkDescDescAppV` D-slot.";
      signature = "vDescAt : Val -> Val -> Val -> Val  -- level, iLev, I";
    };
    vMu = api.leaf {
      value = vMu;
      description = "vMu: value-domain levitated fixpoint `μ I D i` — carrier type of values whose constructors are described by `D` at index `i`.";
      signature = "vMu : Val -> Val -> Val -> Val  -- I, D, i";
    };
    vDescCon = api.leaf {
      value = vDescCon;
      description = "vDescCon: value-domain constructor `descCon(D, i, payload)` — the canonical introducer for `μ I D i` values.";
      signature = "vDescCon : Val -> Val -> Val -> Val  -- D, i, payload";
    };
    vDescConTagged = api.leaf {
      value = vDescConTagged;
      description = "vDescConTagged: value-domain `descCon` carrying a `Squash`-truncated guard certificate — surfaces refinement proofs on `fx.types.Certified` values.";
      signature = "vDescConTagged : Val -> Val -> Val -> Val -> Val  -- D, i, payload, cert";
    };
    vDescConChain = api.leaf {
      value = vDescConChain;
      description = "vDescConChain: flat-chain VDescCon for linearChain Descs. `.d` is stub `vTt`; chain lives in `_layers` (Nix list, outer-first) + `_base`. Chain-wide BootSum wrapper info on `_payloadTag`/`_payloadLeft`/`_payloadRight`. Outer cert is `_layers[0].cert`. O(1) libnix stack on deep force; non-chain-aware consumers crash on `.d.fst` rather than silently mis-reading a degenerate view.";
      signature = "vDescConChain : Val -> Val -> String -> Val -> Val -> [LayerRec] -> Val -> Val  -- D, i, payloadTag, payloadLeft, payloadRight, layers, base";
    };
    vLazyDescIndAccLayer = api.leaf {
      value = vLazyDescIndAccLayer;
      description = "vLazyDescIndAccLayer: MACHINE-INTERNAL deferred accumulator layer of a `descInd` linear chain. Applying expands via four kAppVV frames (step i d (vPair prevAcc vTt) arg); never escapes `runMachineAtF`.";
      signature = "vLazyDescIndAccLayer : Val -> Val -> Val -> Val -> Val  -- step, i, d, prevAcc";
    };
    vThunkTm = api.leaf {
      value = vThunkTm;
      description = "vThunkTm: MACHINE-INTERNAL deferred-Tm Val produced by `ev` on non-atomic Tms. Captures `{ env; tm }`; the driver's `Done` handler forces top-level VThunkTm before returning, so external code observes it only in stored sub-Val fields.";
      signature = "vThunkTm : Env -> Tm -> Val";
    };

    vInterpD = api.leaf {
      value = vInterpD;
      description = "vInterpD: value-domain interpretation `interpD D X i` — yields the payload type for a constructor described by `D` against carrier `X`.";
      signature = "vInterpD : Val -> Val -> Val -> Val -> Val -> Val  -- k, I, D, X, i";
    };
    vAllD = api.leaf {
      value = vAllD;
      description = "vAllD: value-domain induction-hypothesis collector — threads motive `P` through every recursive position in a payload.";
      signature = "vAllD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val";
    };
    vEverywhereD = api.leaf {
      value = vEverywhereD;
      description = "vEverywhereD: value-domain payload-traversal combinator — applies per-node `f` at every recursive position, producing a same-shape derived payload.";
      signature = "vEverywhereD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val -> Val";
    };

    vU = api.leaf {
      value = vU;
      description = "vU: value-domain universe `U(level)` — the type of types at a given Level value.";
      signature = "vU : Val -> Val";
    };

    vLift = api.leaf {
      value = vLift;
      description = "vLift: value-domain Tarski lift `Lift l m A` — non-cumulative cross-level transport of type `A : U(l)` into `U(m)` with `l ≤ m`.";
      signature = "vLift : Val -> Val -> Val -> Val  -- l, m, A";
    };
    vLiftIntro = api.leaf {
      value = vLiftIntro;
      description = "vLiftIntro: value-domain introduction of `Lift l m A` — lifts a term `a : A` at level `l` to a term at level `m`.";
      signature = "vLiftIntro : Val -> Val -> Val -> Val -> Val  -- l, m, A, a";
    };

    vLevel = api.leaf {
      value = vLevel;
      description = "vLevel: value-domain Level type `Level : U(0)`.";
    };
    vLevelZero = api.leaf {
      value = vLevelZero;
      description = "vLevelZero: value-domain level-zero literal `0 : Level`.";
    };
    vLevelSuc = api.leaf {
      value = vLevelSuc;
      description = "vLevelSuc: value-domain successor of a Level expression `suc(l) : Level`.";
      signature = "vLevelSuc : Val -> Val";
    };
    vLevelMax = api.leaf {
      value = vLevelMax;
      description = "vLevelMax: value-domain pointwise max `max(l, r) : Level` — used for universes of dependent products / pairs across distinct levels.";
      signature = "vLevelMax : Val -> Val -> Val  -- l, r";
    };
    vLevelLit = api.leaf {
      value = vLevelLit;
      description = "vLevelLit: value-domain concrete Level literal `n : Level` — derived from a Nix integer at evaluation time.";
      signature = "vLevelLit : Int -> Val";
    };

    vString = api.leaf {
      value = vString;
      description = "vString: value-domain axiomatised primitive `String : U(0)`.";
    };
    vInt = api.leaf {
      value = vInt;
      description = "vInt: value-domain axiomatised primitive `Int : U(0)`.";
    };
    vFloat = api.leaf {
      value = vFloat;
      description = "vFloat: value-domain axiomatised primitive `Float : U(0)`.";
    };
    vAttrs = api.leaf {
      value = vAttrs;
      description = "vAttrs: value-domain axiomatised primitive `Attrs : U(0)` — inhabited by any Nix attrset.";
    };
    vPath = api.leaf {
      value = vPath;
      description = "vPath: value-domain axiomatised primitive `Path : U(0)`.";
    };
    vDerivation = api.leaf {
      value = vDerivation;
      description = "vDerivation: value-domain axiomatised primitive `Derivation : U(0)` — Nix derivation values; the store-producing irreducible value category.";
    };
    vFunction = api.leaf {
      value = vFunction;
      description = "vFunction: value-domain axiomatised primitive `Function : U(0)` — opaque-function carrier.";
    };
    vAny = api.leaf {
      value = vAny;
      description = "vAny: value-domain axiomatised top primitive `Any : U(0)` — accepts every Nix value.";
    };

    vStringLit = api.leaf {
      value = vStringLit;
      description = "vStringLit: value-domain literal carrying a Nix string `s : String`.";
      signature = "vStringLit : String -> Val";
    };
    vIntLit = api.leaf {
      value = vIntLit;
      description = "vIntLit: value-domain literal carrying a Nix integer `n : Int`.";
      signature = "vIntLit : Int -> Val";
    };
    vFloatLit = api.leaf {
      value = vFloatLit;
      description = "vFloatLit: value-domain literal carrying a Nix float `x : Float`.";
      signature = "vFloatLit : Float -> Val";
    };
    vAttrsLit = api.leaf {
      value = vAttrsLit;
      description = "vAttrsLit: value-domain literal carrying an opaque Nix attrset `a : Attrs`.";
      signature = "vAttrsLit : Attrs -> Val";
    };
    vPathLit = api.leaf {
      value = vPathLit;
      description = "vPathLit: value-domain literal carrying a Nix path `p : Path`.";
      signature = "vPathLit : Path -> Val";
    };
    vDerivationLit = api.leaf {
      value = vDerivationLit;
      description = "vDerivationLit: value-domain literal carrying a Nix derivation `d : Derivation` opaquely.";
      signature = "vDerivationLit : Derivation -> Val";
    };
    vFnLit = api.leaf {
      value = vFnLit;
      description = "vFnLit: value-domain literal carrying an opaque Nix function — `fnBox` preserves thunk identity for conv reflexivity.";
      signature = "vFnLit : FnBox -> Val";
    };
    vAnyLit = api.leaf {
      value = vAnyLit;
      description = "vAnyLit: value-domain literal carrying an arbitrary Nix value `v : Any` — used by approximate types whose kernel slot is `vAny`.";
      signature = "vAnyLit : Any -> Val";
    };

    vOpaqueLam = api.leaf {
      value = vOpaqueLam;
      description = "vOpaqueLam: value-domain opaque lambda over a Nix function — kernel never inspects it; `fnBox` thunk identity preserves conv reflexivity.";
      signature = "vOpaqueLam : FnBox -> Val -> Val  -- fnBox, piType";
    };

    vNe = api.leaf {
      value = vNe;
      description = "vNe: neutral value — stuck computation `var^lvl <spine>`; head is a de Bruijn level, spine is a list of elimination frames awaiting reduction.";
      signature = "vNe : Int -> Spine -> Val  -- level, spine";
    };
    freshVar = api.leaf {
      value = freshVar;
      description = "freshVar: introduce a fresh neutral variable at the given depth — used during type-checking to bind a fresh witness under Π / Σ / let binders.";
      signature = "freshVar : Int -> Val  -- depth";
    };
    vNeSnoc = api.leaf {
      value = vNeSnoc;
      description = "vNeSnoc: O(1) neutral-spine extension — append one elimination frame via the skew-binary RAL backing `_ral`, keeping `.spine` a materialized in-order list. Use in place of `vNe lvl (n.spine ++ [frame])` to avoid the O(N²)/overflow-prone Nix-list snoc.";
      signature = "vNeSnoc : Val -> SpineEntry -> Val  -- neutral, frame";
    };

    eApp = api.leaf {
      value = eApp;
      description = "eApp: elimination frame for function application — pushes an argument onto a neutral spine.";
      signature = "eApp : Val -> SpineEntry";
    };
    eFst = api.leaf {
      value = eFst;
      description = "eFst: elimination frame for first-projection on a Σ neutral.";
    };
    eSnd = api.leaf {
      value = eSnd;
      description = "eSnd: elimination frame for second-projection on a Σ neutral.";
    };
    eBootSumElim = api.leaf {
      value = eBootSumElim;
      description = "eBootSumElim: elimination frame for `bootSumElim` on a neutral sum scrutinee — carries motive and case arms.";
      signature = "eBootSumElim : Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eBootJ = api.leaf {
      value = eBootJ;
      description = "eBootJ: elimination frame for the J eliminator on a neutral identity proof — carries A, a, motive, refl-case, b.";
      signature = "eBootJ : Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eStrEq = api.leaf {
      value = eStrEq;
      description = "eStrEq: elimination frame for `strEq` on a neutral string operand — carries the other operand for completion when the neutral resolves.";
      signature = "eStrEq : Val -> Val -> SpineEntry";
    };
    eIntLeL = api.leaf {
      value = eIntLeL;
      description = "eIntLeL: `intLe` frame where the neutral operand is the lhs — carries the rhs.";
      signature = "eIntLeL : Val -> SpineEntry";
    };
    eIntLeR = api.leaf {
      value = eIntLeR;
      description = "eIntLeR: `intLe` frame where the neutral operand is the rhs — carries the lhs.";
      signature = "eIntLeR : Val -> SpineEntry";
    };
    eIntEq = api.leaf {
      value = eIntEq;
      description = "eIntEq: `intEq` frame on a neutral int operand — carries the other operand (symmetric).";
      signature = "eIntEq : Val -> SpineEntry";
    };
    eAbsurd = api.leaf {
      value = eAbsurd;
      description = "eAbsurd: elimination frame for `absurd` on a neutral `Empty`-typed scrutinee — carries the target type `P`; sound because `Empty` has no canonical inhabitants, so this frame can only arise on a stuck spine.";
      signature = "eAbsurd : Val -> SpineEntry  -- type P";
    };
    eDescInd = api.leaf {
      value = eDescInd;
      description = "eDescInd: elimination frame for `descInd` on a neutral `μ`-typed scrutinee — carries `I`, `D`, motive, step.";
      signature = "eDescInd : Val -> Val -> Val -> Val -> SpineEntry";
    };
    eLiftElim = api.leaf {
      value = eLiftElim;
      description = "eLiftElim: elimination frame for `liftElim` on a neutral `Lift l m A` — carries `l`, `m`, `A` for level lowering.";
      signature = "eLiftElim : Val -> Val -> Val -> SpineEntry";
    };

    eInterpD = api.leaf {
      value = eInterpD;
      description = "eInterpD: elimination frame for `interpD` on a neutral description — carries `k`, `I`, `X`, `i` for completion when the neutral resolves.";
      signature = "eInterpD : Val -> Val -> Val -> Val -> SpineEntry";
    };
    eAllD = api.leaf {
      value = eAllD;
      description = "eAllD: elimination frame for `allD` on a neutral description — carries motive `P` plus shape parameters.";
      signature = "eAllD : Val -> Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };
    eEverywhereD = api.leaf {
      value = eEverywhereD;
      description = "eEverywhereD: elimination frame for `everywhereD` on a neutral description — carries per-node `f` plus shape parameters.";
      signature = "eEverywhereD : Val -> Val -> Val -> Val -> Val -> Val -> Val -> SpineEntry";
    };

    eSquashElim = api.leaf {
      value = eSquashElim;
      description = "eSquashElim: elimination frame for `squashElim` on a neutral `Squash`-typed scrutinee — carries motive shape (`A`, `B`) and case function `f`.";
      signature = "eSquashElim : Val -> Val -> Val -> SpineEntry";
    };

  };
}
