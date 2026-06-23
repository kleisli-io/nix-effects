# Type-checking kernel: Conversion (definitional equality)
#
# conv : Depth -> Val -> Val -> Bool
# Checks definitional equality of two values at binding depth d.
# Purely structural on normalized values — no type information used.
# Sigma-eta (⟨fst x, snd x⟩ ≡ x), unit-eta (x ≡ tt for x : ⊤), and
# Pi-eta (f ≡ λx. f x) are all implemented. Cumulativity handled in
# check.nix Sub rule only.
# Pure function — zero effect system imports.
#
# Spec reference: kernel-spec.md §6
{ fx, api, ... }:
let
  V = fx.tc.value;
  E = fx.tc.eval;

  # -- Level normaliser --
  #
  # A Level value reduces to a canonical spine
  #   max (suc^{n_1} b_1) … (suc^{n_k} b_k)
  # where each b_i is either `zero` or a free variable (`VNe`), and
  # duplicates of the same base retain only the max shift. Zero
  # absorption: the `zero` base is dropped when a variable base with
  # non-negative shift dominates it. `suc (max a b) = max (suc a) (suc b)`
  # is realised by threading the pending `shift` outward during flatten.
  #
  # Two Level values are conv-equal iff their canonical spines agree
  # element-wise.
  levelZeroBase = { kind = "zero"; };
  mkVarBase = v: { kind = "var"; level = v.level; spine = v.spine; };
  baseEq = a: b: a == b;

  # Flatten nested max into a list of leaf summands, threading a
  # pending outer shift (number of `suc` layers) down to each leaf.
  #
  # Depth-flat worklist: a `genericClosure` keyed by a round counter (the
  # branching lives in the eagerly-forced frontier vector, not the keys), so
  # the trace is iterative in libnix — O(rounds) C-stack frames, not O(level
  # depth). Each round forces every frontier node, enqueues `VLevelMax`
  # children / the `VLevelSuc` predecessor (shift+1), and emits leaf summands
  # (`VLevelZero`/`VNe`) into the accumulator. Emission order is irrelevant —
  # `normLevel` sorts the summands by `baseCmp` downstream.
  flattenLevel = shift: v0:
    let
      # One round: force every frontier node, enqueue children/predecessor,
      # emit THIS round's leaf summands. Carrying only per-round `emitted`
      # (not a running accumulator) is load-bearing: a threaded `acc ++ emitted`
      # builds an O(depth) lazy `++` chain that overflows the C-stack when
      # forced at the end. Instead the trace is materialized by genericClosure
      # and the summands are gathered once, below, with iterative concatLists.
      roundStep = frontier:
        let
          forced = map (it: { v = E.forceVal it.v; inherit (it) shift; }) frontier;
          children = builtins.concatLists (map
            (it:
              if it.v.tag == "VLevelMax" then
                [ { v = it.v.lhs; inherit (it) shift; } { v = it.v.rhs; inherit (it) shift; } ]
              else if it.v.tag == "VLevelSuc" then
                [ { v = it.v.pred; shift = it.shift + 1; } ]
              else [ ])
            forced);
          emitted = builtins.concatLists (map
            (it:
              if it.v.tag == "VLevelZero" then [ { base = levelZeroBase; inherit (it) shift; } ]
              else if it.v.tag == "VNe" then [ { base = mkVarBase it.v; inherit (it) shift; } ]
              else if it.v.tag == "VLevelMax" || it.v.tag == "VLevelSuc" then [ ]
              else throw "tc: level: unexpected tag '${it.v.tag}' in flattenLevel")
            forced);
          # Force the frontier list spine AND every child's threaded `shift`
          # to a concrete int this round. Both are load-bearing: an unforced
          # spine lazily cascades back through every prior round, and the
          # threaded `shift + 1` is an O(depth) lazy arithmetic chain that
          # overflows when a leaf summand's shift is finally read.
          forceShifts = builtins.foldl' (acc: c: builtins.seq c.shift acc) null children;
        in
        {
          frontier = builtins.seq forceShifts children;
          inherit emitted;
        };
      rounds = builtins.genericClosure {
        startSet = [{ key = 0; st = roundStep [{ v = v0; inherit shift; }]; }];
        operator = item:
          if item.st.frontier == [ ] then [ ]
          else [{ key = item.key + 1; st = roundStep item.st.frontier; }];
      };
    in
    builtins.concatLists (map (it: it.st.emitted) rounds);

  # Dedup adjacent-or-scattered same-base summands, keeping the max shift.
  # The accumulator width is the number of DISTINCT bases (small — bounded by
  # the count of free level variables), but the fold runs once per summand, so
  # a deep `max` tree drives it N times. The rebuilt `{ base = y.base; shift =
  # … }` records must have their `base` (to WHNF — not the neutral's spine) and
  # `shift` forced each step: otherwise they stack into an O(#summands)-deep
  # lazy indirection chain that overflows the C-stack when a field is finally
  # read. Forcing per step keeps it O(#summands × #distinct-bases).
  dedupLevel = summands:
    builtins.foldl'
      (acc: s:
        let
          next =
            if builtins.any (y: baseEq y.base s.base) acc
            then
              map
                (y:
                  if baseEq y.base s.base
                  then { base = y.base; shift = if y.shift > s.shift then y.shift else s.shift; }
                  else y)
                acc
            else acc ++ [ s ];
          forceElems = builtins.foldl' (a: e: builtins.seq e.base (builtins.seq e.shift a)) null next;
        in
        builtins.seq forceElems next
      ) [ ]
      summands;

  # Total order on bases — zero sorts last so it can be absorbed when
  # any variable summand survives. Variables compare by de Bruijn
  # level; equal-level variables (differ only in spine) stay adjacent,
  # which dedup already handles.
  baseCmp = a: b:
    if baseEq a b then 0
    else if a.kind == "zero" then 1
    else if b.kind == "zero" then -1
    else if a.level < b.level then -1
    else if a.level > b.level then 1
    else 0;

  # Drop a `{ base = zero; shift = n }` summand when some variable
  # summand `{ base = var; shift = m }` dominates it (i.e. `m ≥ n`).
  # Sound because every level variable inhabits ℕ, so
  # `var + m ≥ m ≥ n = 0 + n`. Keep `[{zero, n}]` alone (that IS the
  # zero-shifted-n Level value).
  dropZeroIfDominated = merged:
    if builtins.length merged <= 1 then merged
    else
      let
        varShifts = map (s: s.shift)
          (builtins.filter (s: s.base.kind != "zero") merged);
        maxVarShift =
          if varShifts == [ ]
          then 0
          else
            builtins.foldl' (a: b: if a > b then a else b)
              (builtins.head varShifts)
              (builtins.tail varShifts);
        kept = builtins.filter
          (s: !(s.base.kind == "zero"
            && varShifts != [ ]
            && s.shift <= maxVarShift))
          merged;
      in
      if kept == [ ] then merged else kept;

  normLevel = v:
    let
      flat = flattenLevel 0 v;
      deduped = dedupLevel flat;
      sorted = builtins.sort (a: b: baseCmp a.base b.base < 0) deduped;
    in
    dropZeroIfDominated sorted;

  summandEq = x: y: x.shift == y.shift && baseEq x.base y.base;

  # Closed-level fast path: nat denotation of a Level value containing no
  # neutrals, under a node budget. Returns { n; fuel; } or null (neutral
  # hit, foreign tag, or budget exhausted). A closed Level normalises to
  # the single summand [{ base = zero; shift = n }] with n exactly this
  # denotation, so two in-budget closed levels are conv-equal iff their
  # denotations agree — skipping the flatten/dedup/sort pipeline entirely
  # (the Lift smart constructors run that comparison on every collapse
  # check). The budget bounds both native recursion depth and the lazy
  # `n + 1` chains, so deep adversarial levels fall back to the depth-flat
  # pipeline instead of risking the C stack.
  closedLevelNat = fuel: v0:
    if fuel <= 0 then null
    else
      let v = E.forceVal v0; t = v.tag; in
      if t == "VLevelZero" then { n = 0; fuel = fuel - 1; }
      else if t == "VLevelSuc" then
        let r = closedLevelNat (fuel - 1) v.pred; in
        if r == null then null else { n = r.n + 1; inherit (r) fuel; }
      else if t == "VLevelMax" then
        let
          rl = closedLevelNat (fuel - 1) v.lhs;
          rr = if rl == null then null else closedLevelNat rl.fuel v.rhs;
        in
        if rr == null then null
        else { n = if rl.n > rr.n then rl.n else rr.n; inherit (rr) fuel; }
      else null;

  # General comparison — both sides through the full normaliser.
  convLevelSpines = a: b:
    let sa = normLevel a; sb = normLevel b; in
    builtins.length sa == builtins.length sb
    && builtins.all (i: summandEq (builtins.elemAt sa i) (builtins.elemAt sb i))
      (builtins.genList (i: i) (builtins.length sa));

  # Syntactic-equality fast-path: two Level values that are the same
  # Nix value are trivially conv-equal. Skips the normLevel allocations
  # in the common case where both sides come from the same elaboration
  # site (e.g. `kVal` and `ty.level` for a homogeneous-L description).
  # Sound: Nix `==` on values is structural; structural equality of
  # Level values implies their canonical spines agree element-wise.
  # Closed-level fast path next: when both sides denote closed nats
  # within budget, compare the ints; otherwise the full spine pipeline.
  convLevel = a: b:
    a == b
    || (
      let na = closedLevelNat 64 a; in
      if na == null then convLevelSpines a b
      else
        let nb = closedLevelNat 64 b; in
        if nb == null then convLevelSpines a b
        else na.n == nb.n
    );

  listConv = d: xs: ys:
    builtins.length xs == builtins.length ys
    && builtins.foldl'
      (ok: i: ok && conv d (builtins.elemAt xs i) (builtins.elemAt ys i))
      true
      (builtins.genList (i: i) (builtins.length xs));

  descRefConv = d: r1: r2:
    let
      kind = r1.kind or null;
      signatureConv =
        if kind == "datatype-desc"
        then (r1 ? signature) && (r2 ? signature)
          && (r1.signature.complete or false)
          && (r2.signature.complete or false)
          && r1.signature == r2.signature
        else true;
    in
    kind == (r2.kind or null)
    && (r1.name or null) == (r2.name or null)
    && (r1.arity or null) == (r2.arity or null)
    && (r1.indexed or null) == (r2.indexed or null)
    && (r1.constructors or [ ]) == (r2.constructors or [ ])
    && conv d r1.I r2.I
    && convLevel r1.level r2.level
    && listConv d (r1.params or [ ]) (r2.params or [ ])
    && signatureConv;

  # Pi-eta η-reduction detector. Recognises closures of shape `λx. f x`
  # where `f` does not reference the bound `x` — i.e., body is
  # `app (var k) (var 0)` with `k ≥ 1`, so `f = closure.env[k-1]` (env
  # entries shift de Bruijn indices by one under the binder). Returns
  # the η-reduced function value `f`, or `null` if the closure is not
  # such an expansion. Lets the Pi-eta conv rule short-circuit
  # `conv (d+1) (vApp f freshVar) (vApp v2 freshVar)` to `conv d f v2`,
  # saving a `freshVar`+`vApp`+`instantiate` triple and one binder
  # layer of recursion per fire. Sound by congruence of conv under
  # vApp: `conv d f v2 ⇒ conv (d+1) (vApp f w) (vApp v2 w)` for any w.
  etaReducedFn = closure:
    let body = closure.body; in
    if body.tag == "app"
      && body.fn.tag == "var"
      && body.fn.idx >= 1
      && body.arg.tag == "var"
      && body.arg.idx == 0
      && (body.fn.idx - 1) < (V.envLen closure.env)
    then V.envNth closure.env (body.fn.idx - 1)
    else null;

  # -- Conversion step over forced values --
  # Definitional equality of v1 and v2 at depth d; the native arms drive every
  # rule. `convStepForced` requires both sides already WHNF (never `VThunkTm`);
  # `convStep` is the forcing wrapper for callers holding possibly-deferred
  # values (`runConvF` base goals carry lazy spine fields). `conv` forces at
  # entry, so its dispatch skips the wrapper — forceVal is idempotent but each
  # call costs an application.
  convStep = d: v1raw: v2raw: convStepForcedF convDepthFuel d (E.forceVal v1raw) (E.forceVal v2raw);

  convStepForcedF = fuel: d: v1: v2:
    let
      conv = convF fuel;
      convSp = convSpF fuel;
      t1 = v1.tag; t2 = v2.tag;
    in

    # Lift idempotent collapse — short-circuit before any structural
      # rule. `Lift l l _ A ≡ A` keeps homogeneous code transparent under
      # the explicit-Lift discipline. The same shape applies to the
      # introducer: `lift l l _ A a ≡ a`. Both reuse `convLevel`'s
      # semilattice quotient (§6.6) — no new conv mechanism. The witness
      # slot is never inspected.
    if t1 == "VLift" && convLevel v1.l v1.m then conv d v1.A v2
    else if t2 == "VLift" && convLevel v2.l v2.m then conv d v1 v2.A
    else if t1 == "VLiftIntro" && convLevel v1.l v1.m then conv d v1.a v2
    else if t2 == "VLiftIntro" && convLevel v2.l v2.m then conv d v1 v2.a

    # §6.1 Structural rules — simple values
    else if t1 == "VUnit" && t2 == "VUnit" then true
    else if t1 == "VTt" && t2 == "VTt" then true
    else if t1 == "VEmpty" && t2 == "VEmpty" then true
    else if t1 == "VBootRefl" && t2 == "VBootRefl" then true
    else if t1 == "VFunext" && t2 == "VFunext" then true
    else if t1 == "VU" && t2 == "VU" then
    # Fast-path: both levels are the `VLevelZero` singleton — skip
    # the flatten/dedup/sort pipeline. Falls through to `convLevel`
    # for any non-zero level expression.
      if v1.level.tag == "VLevelZero" && v2.level.tag == "VLevelZero"
      then true
      else convLevel v1.level v2.level
    else if t1 == "VLevel" && t2 == "VLevel" then true
    # Level expressions: canonicalise then compare. Fires whenever
    # either side carries a Level constructor; a pure-VNe Level
    # expression (e.g. a bound variable of type Level) falls through
    # to the VNe/VNe rule below. Tags compared inline to avoid
    # per-conv thunk allocation on the hot conv-dispatch path.
    else if t1 == "VLevelZero" || t1 == "VLevelSuc" || t1 == "VLevelMax"
      || t2 == "VLevelZero" || t2 == "VLevelSuc" || t2 == "VLevelMax"
    then convLevel v1 v2
    else if t1 == "VString" && t2 == "VString" then true
    else if t1 == "VInt" && t2 == "VInt" then true
    else if t1 == "VFloat" && t2 == "VFloat" then true
    else if t1 == "VAttrs" && t2 == "VAttrs" then true
    else if t1 == "VPath" && t2 == "VPath" then true
    else if t1 == "VDerivation" && t2 == "VDerivation" then true
    else if t1 == "VFunction" && t2 == "VFunction" then true
    else if t1 == "VAny" && t2 == "VAny" then true
    else if t1 == "VStringLit" && t2 == "VStringLit" then v1.value == v2.value
    else if t1 == "VIntLit" && t2 == "VIntLit" then v1.value == v2.value
    else if t1 == "VFloatLit" && t2 == "VFloatLit" then v1.value == v2.value
    else if t1 == "VAttrsLit" && t2 == "VAttrsLit" then true
    else if t1 == "VPathLit" && t2 == "VPathLit" then true
    else if t1 == "VDerivationLit" && t2 == "VDerivationLit" then true
    else if t1 == "VFnLit" && t2 == "VFnLit" then true
    else if t1 == "VAnyLit" && t2 == "VAnyLit" then true
    # §6.2 Binding forms — compare under binders with fresh var
    else if t1 == "VPi" && t2 == "VPi" then
      conv d v1.domain v2.domain
      && conv (d + 1) (E.instantiate v1.closure (V.freshVar d))
        (E.instantiate v2.closure (V.freshVar d))
    else if t1 == "VLam" && t2 == "VLam" then
      let fv = V.freshVar d; in
      conv (d + 1) (E.instantiate v1.closure fv)
        (E.instantiate v2.closure fv)
    # §6.2a Pi-eta: f ≡ λx. f x for any function f. Fires when exactly
    # one side is a VLam and the other is a non-VLam value (VNe, VPair,
    # etc.) of function type. Symmetric to Sigma-eta below: instantiate
    # the VLam under a fresh var on one side, vApp the other side to
    # the same fresh var, recurse. Sound because conv is called on
    # values sharing a type — if one side is VLam, that type is VPi, and
    # the other side's only inhabitants up to definitional equality are
    # its own eta-expansions. Fires symmetrically (VLam-vs-other and
    # other-vs-VLam) to keep conv reflexive on Pi-typed neutrals.
    # Termination: each rule descends under one binder while consuming
    # one VLam, so the recursive call is on strictly smaller VLam-depth
    # on at least one side; cannot loop. Pre-pass via `etaReducedFn`
    # short-circuits whenever the VLam is a syntactic η-expansion of an
    # in-scope value `f` (body = `app (var k≥1) (var 0)`): the recursive
    # call collapses to `conv d f other` — no fresh var, no `vApp`, no
    # `instantiate`, one fewer binder layer.
    else if t1 == "VLam" && t2 != "VLam" then
      let etaFn = etaReducedFn v1.closure; in
      if etaFn != null then conv d etaFn v2
      else
        let fv = V.freshVar d; in
        conv (d + 1) (E.instantiate v1.closure fv)
          (E.vApp v2 fv)
    else if t1 != "VLam" && t2 == "VLam" then
      let etaFn = etaReducedFn v2.closure; in
      if etaFn != null then conv d v1 etaFn
      else
        let fv = V.freshVar d; in
        conv (d + 1) (E.vApp v1 fv)
          (E.instantiate v2.closure fv)
    else if t1 == "VSigma" && t2 == "VSigma" then
      conv d v1.fst v2.fst
      && conv (d + 1) (E.instantiate v1.closure (V.freshVar d))
        (E.instantiate v2.closure (V.freshVar d))

    # §6.3 Compound values
    else if t1 == "VPair" && t2 == "VPair" then
      conv d v1.fst v2.fst && conv d v1.snd v2.snd
    # §6.3a Sigma-eta: ⟨fst x, snd x⟩ ≡ x for a neutral x.
    # The rule only fires against a neutral RHS: concrete non-pair values
    # of other types (VLam, VU, VUnit, ...) cannot convert with a VPair,
    # so matching them against a VPair harmlessly falls through to `false`.
    else if t1 == "VPair" && t2 == "VNe" then
      conv d v1.fst (E.vFst v2) && conv d v1.snd (E.vSnd v2)
    else if t1 == "VNe" && t2 == "VPair" then
      conv d (E.vFst v1) v2.fst && conv d (E.vSnd v1) v2.snd
    # §6.3b Unit-eta: any inhabitant of ⊤ is ≡ tt. In the type-free conv,
    # VTt vs VNe is sound because conv is always called on values of a
    # shared type; if one side is VTt, that shared type is ⊤ and the VNe's
    # only inhabitant is tt.
    else if t1 == "VTt" && t2 == "VNe" then true
    else if t1 == "VNe" && t2 == "VTt" then true
    else if t1 == "VBootSum" && t2 == "VBootSum" then
      conv d v1.left v2.left && conv d v1.right v2.right
    else if t1 == "VBootInl" && t2 == "VBootInl" then
      conv d v1.left v2.left && conv d v1.right v2.right && conv d v1.val v2.val
    else if t1 == "VBootInr" && t2 == "VBootInr" then
      conv d v1.left v2.left && conv d v1.right v2.right && conv d v1.val v2.val
    else if t1 == "VBootEq" && t2 == "VBootEq" then
      conv d v1.type v2.type && conv d v1.lhs v2.lhs && conv d v1.rhs v2.rhs

    # Descriptions
    else if t1 == "VDesc" && t2 == "VDesc" then
    # Level-zero fast-path: prelude descriptions live at `desc^0`,
    # so skip the full `convLevel` pipeline when both sides are the
    # `VLevelZero` singleton. The `iLev` slot (universe of `I`)
    # defaults to `vLevelZero` for the ⊤-slice and must agree —
    # otherwise the `vDesc ↔ vMu` unfolding rule would synthesise
    # different `mkDescDescAppV` D-slots on each side.
      (if v1.level.tag == "VLevelZero" && v2.level.tag == "VLevelZero"
      then true
      else convLevel v1.level v2.level)
      && convLevel (v1.iLev or V.vLevelZero) (v2.iLev or V.vLevelZero)
      && conv d v1.I v2.I
    else if t1 == "VMu" && t2 == "VMu" then
      conv d v1.I v2.I && conv d v1.D v2.D && conv d v1.i v2.i
    # §6.6 Desc/μ unfolding. `Desc I k ≡ μ ⊤ (descDesc I k) tt`.
    # Bridges the `Desc`-typed surface name and the descDesc-encoded
    # μ-form. `mkDescDescAppV` builds the expected D as a `_canonRef`-
    # tagged value carrying the identity `(descDesc, I, L)` on its
    # outer cell — see the VDescCon × VDescCon branch below for the
    # tag short-circuit. Symmetric in argument order. Decidable:
    # descDesc is closed and reduces to a finite tree, so structural
    # `conv` on the result terminates.
    else if t1 == "VDesc" && t2 == "VMu" then
      let
        iLev = v1.iLev or V.vLevelZero;
        expectedD = E.mkDescDescAppV iLev v1.I v1.level;
      in
      conv d V.vUnit v2.I
      && conv d V.vTt v2.i
      && conv d expectedD v2.D
    else if t1 == "VMu" && t2 == "VDesc" then
      let
        iLev = v2.iLev or V.vLevelZero;
        expectedD = E.mkDescDescAppV iLev v2.I v2.level;
      in
      conv d v1.I V.vUnit
      && conv d v1.i V.vTt
      && conv d v1.D expectedD
    else if t1 == "VDescCon" && t2 == "VDescCon" then
      let
        canonRefConv = r1: r2:
          if !(r1 ? params) || !(r2 ? params) then false
          else
            let
              p1 = r1.params;
              p2 = r2.params;
              n = builtins.length p1;
              descDescArityOk =
                r1.id != "descDesc"
                || (builtins.length p1 == 3 && builtins.length p2 == 3);
              convParam = i:
                conv d (builtins.elemAt p1 i) (builtins.elemAt p2 i);
            in
            r1.id == r2.id
            && descDescArityOk
            && builtins.length p2 == n
            && builtins.all convParam (builtins.genList (x: x) n);
        isDescDescRefD = D:
          builtins.isAttrs D
          && D ? _canonRef
          && (D._canonRef.id or null) == "descDesc";
        decodeDescCase = dVal:
          if (dVal ? _canonRef) || !(dVal ? d) then null
          else
            let
              walk = node: depth:
                if depth >= 4 then { idx = 4; payload = node; }
                else if builtins.isAttrs node && (node.tag or null) == "VBootInl" then { idx = depth; payload = node.val; }
                else if builtins.isAttrs node && (node.tag or null) == "VBootInr" then walk node.val (depth + 1)
                else null;
            in
            walk dVal.d 0;
        canProject = x:
          builtins.isAttrs x
          && ((x.tag or null) == "VPair" || (x.tag or null) == "VNe");
        payloadFields = n: payload:
          if n == 0 then [ ]
          else if !canProject payload then null
          else
            let
              rest = payloadFields (n - 1) (E.vSnd payload);
            in
            if rest == null then null else [ (E.vFst payload) ] ++ rest;
        fieldCount = idx:
          if idx == 0 then 1
          else if idx == 3 then 3
          else 2;
        hasNeutralPayload = c:
          builtins.isAttrs c.payload && (c.payload.tag or null) == "VNe";
        descDescCaseConv = c1: c2:
          if c1 == null || c2 == null || c1.idx != c2.idx then false
          else if !(hasNeutralPayload c1 || hasNeutralPayload c2) then false
          else
            let
              n = fieldCount c1.idx;
              fs1 = payloadFields n c1.payload;
              fs2 = payloadFields n c2.payload;
            in
            fs1 != null
            && fs2 != null
            && builtins.all
              (i: conv d (builtins.elemAt fs1 i) (builtins.elemAt fs2 i))
              (builtins.genList (i: i) n);
        descDescConConv =
          isDescDescRefD v1.D
          && isDescDescRefD v2.D
          && canonRefConv v1.D._canonRef v2.D._canonRef
          && conv d v1.i v2.i
          && descDescCaseConv (decodeDescCase v1) (decodeDescCase v2);
        descDescArgConv =
          isDescDescRefD v1.D
          && isDescDescRefD v2.D
          && canonRefConv v1.D._canonRef v2.D._canonRef
          && conv d v1.i v2.i
          && (
            let
              view1 = E.descView v1;
              view2 = E.descView v2;
              x = V.freshVar d;
            in
            view1 != null
            && view2 != null
            && view1.idx == 1
            && view2.idx == 1
            && conv d view1.sTy view2.sTy
            && conv (d + 1) (E.vApp view1.tFn x) (E.vApp view2.tFn x)
          );
      in
      # Canonical-reference equality compares the stamp instead of forcing
        # the recursively defined description body.
      if (v1 ? _canonRef) && (v2 ? _canonRef)
      then canonRefConv v1._canonRef v2._canonRef
      else if (v1 ? _descRef) && (v2 ? _descRef)
        && descRefConv d v1._descRef v2._descRef
      then true
      else if descDescArgConv then true
      else if descDescConConv then true
      # One side is chain-form (`_shape == "linearChain"`); promote the
      # other on the fly via a `genericClosure` peel driven by the
      # chain-form side's `_payloadTag` + per-layer heads count, then
      # iterate both as chain-form. A direct `V.vDescCon` foldl' chain
      # (no eval-time classifier) and its quote→eval round-tripped
      # sibling meet here.
      else if (v1._shape or null) == "linearChain"
           || (v2._shape or null) == "linearChain" then
        let
          v1IsChain = (v1._shape or null) == "linearChain";
          chainSide = if v1IsChain then v1 else v2;
          payloadTag = chainSide._payloadTag;
          nFields =
            let csLayers = E.effLayers chainSide; in
            if csLayers == [ ] then 0
            else builtins.length (builtins.head csLayers).heads;
          # Canonicalize both operands to a flat layer list + flat base,
          # forcing every sub-Val and flattening nested chain bases. Routing
          # both sides through the same peeler makes layer counts and bases
          # comparable regardless of which side arrived in chain form.
          c1 = E.forceAndPeelChainV payloadTag nFields v1;
          c2 = E.forceAndPeelChainV payloadTag nFields v2;
          layers1 = c1.layers; layers2 = c2.layers;
          n1 = builtins.length layers1; n2 = builtins.length layers2;
          ptag1 = if c1.outerTag != null then c1.outerTag else payloadTag;
          ptag2 = if c2.outerTag != null then c2.outerTag else payloadTag;
          pleft1 = if c1.outerLeft != null then c1.outerLeft else chainSide._payloadLeft;
          pleft2 = if c2.outerLeft != null then c2.outerLeft else chainSide._payloadLeft;
          pright1 = if c1.outerRight != null then c1.outerRight else chainSide._payloadRight;
          pright2 = if c2.outerRight != null then c2.outerRight else chainSide._payloadRight;
          layerConv = k:
            let l1 = builtins.elemAt layers1 k;
                l2 = builtins.elemAt layers2 k;
                h1 = l1.heads; h2 = l2.heads;
                nh = builtins.length h1;
            in conv d l1.i l2.i
               && builtins.length h2 == nh
               && builtins.all
                    (j: conv d (builtins.elemAt h1 j) (builtins.elemAt h2 j))
                    (builtins.genList (j: j) nh);
        in
        n1 == n2
        && ptag1 == ptag2
        && conv d v1.D v2.D
        && conv d pleft1 pleft2
        && conv d pright1 pright2
        && conv d c1.base c2.base
        && builtins.all layerConv (builtins.genList (k: k) n1)
      else
        let
          classifyD = D:
            let view = E.descView D; in
            if view == null || view.idx != 4 then null
            else
              let
                pA = E.linearProfile view.A;
                pB = E.linearProfile view.B;
              in
              if pA != null && pB == null then { profile = pA; side = "VBootInl"; }
              else if pB != null && pA == null then { profile = pB; side = "VBootInr"; }
              else null;
          classify = classifyD v1.D;
          nFields = if classify == null then 0 else builtins.length classify.profile;
          indexConv = a: b:
            if a.tag == "VTt" && b.tag == "VTt"
            then true
            else conv d a b;
          itemDConv = item:
            if (item.a.D ? _descRef) && (item.b.D ? _descRef)
              && descRefConv d item.a.D._descRef item.b.D._descRef
            then true
            else conv d item.a.D item.b.D;
          ctorPayloadConv = a: b:
            if a.tag == "VBootInl" && b.tag == "VBootInl"
            then ctorPayloadConv a.val b.val
            else if a.tag == "VBootInr" && b.tag == "VBootInr"
            then ctorPayloadConv a.val b.val
            else conv d a b;
          baseStructuralConv = item:
            itemDConv item
            && indexConv item.a.i item.b.i
            && conv d item.a.d item.b.d;
          baseCtorConv = item:
            let
              nonRecursiveSide =
                if classify.side == "VBootInl"
                then "VBootInr"
                else "VBootInl";
              injectionVals =
                if classify == null then
                  if item.a.d.tag == item.b.d.tag
                    && (item.a.d.tag == "VBootInl" || item.a.d.tag == "VBootInr")
                  then { a = item.a.d.val; b = item.b.d.val; }
                  else null
                else if item.a.d.tag == nonRecursiveSide
                  && item.b.d.tag == nonRecursiveSide
                then { a = item.a.d.val; b = item.b.d.val; }
                else null;
            in
            injectionVals != null
            && itemDConv item
            && indexConv item.a.i item.b.i
            && ctorPayloadConv injectionVals.a injectionVals.b;
          baseConv = item: baseCtorConv item || baseStructuralConv item;
          # Peel each operand INDEPENDENTLY to linearChain normal form via the
          # canonical force-and-flatten oracle: it forces every sub-Val read
          # (closing the latent VThunkTm under-peel) and splices a chain-form
          # tail. Symmetric normal forms make layer counts and bases directly
          # comparable, replacing the old unforced lockstep dual-peel.
          c1 = E.forceAndPeelChainV classify.side nFields v1;
          c2 = E.forceAndPeelChainV classify.side nFields v2;
          layers1 = c1.layers; layers2 = c2.layers;
          n1 = builtins.length layers1; n2 = builtins.length layers2;
          baseItem = { a = c1.base; b = c2.base; };
          # Per-layer D match follows by transitivity from `conv d v1.D v2.D`
          # over the shared linear-recursive descriptor; boot-sum arm types and
          # the ret-leaf (validated inside the oracle) are determined by that D,
          # so comparing index + heads suffices per layer.
          layerConv = k:
            let
              l1 = builtins.elemAt layers1 k;
              l2 = builtins.elemAt layers2 k;
              h1 = l1.heads; h2 = l2.heads;
            in
            indexConv l1.i l2.i
            && (if builtins.length h1 == 0 && builtins.length h2 == 0
                then true
                else listConv d h1 h2);
        in
        if classify == null then
          baseConv { a = v1; b = v2; }
        else if n1 != n2 then false
        else if n1 == 0 then
          baseConv baseItem
        else
          conv d v1.D v2.D
          && builtins.all layerConv (builtins.genList (k: k) n1)
          && baseConv baseItem

    # Lift type-former — structural with witness-irrelevance. The `eq`
    # slot is not compared: two `VLift`s with matching levels and
    # underlying type are conv-equal regardless of the proof witness
    # carried (sound because `Eq Level a b` over the hSet `Level` is
    # propositional).
    else if t1 == "VLift" && t2 == "VLift" then
      convLevel v1.l v2.l && convLevel v1.m v2.m && conv d v1.A v2.A
    # Lift introducer — structural. Compares carried values; skips
    # `eq` for the same reason.
    else if t1 == "VLiftIntro" && t2 == "VLiftIntro" then
      convLevel v1.l v2.l && convLevel v1.m v2.m
      && conv d v1.A v2.A && conv d v1.a v2.a
    # Lift-eta on stuck neutrals: `lift l m _ A a ≡ x` ⟺
    # `a ≡ lower l m _ A x`. Symmetric to Sigma-eta (VPair vs VNe).
    # Restricted to VNe on the other side: any other shape is not an
    # inhabitant of Lift, so the catch-all `false` is the right answer
    # without forcing `vLiftElimF` to throw.
    else if t1 == "VLiftIntro" && t2 == "VNe" then
      conv d v1.a (E.vLiftElimF v1.l v1.m v1.eq v1.A v2)
    else if t1 == "VNe" && t2 == "VLiftIntro" then
      conv d (E.vLiftElimF v2.l v2.m v2.eq v2.A v1) v2.a

    # Propositional truncation. `Squash A` is the type-former; conv on
    # formers descends into the underlying type. Inhabitants are
    # definitionally irrelevant: any two `VSquashIntro` values at the
    # same expected `Squash A` type are equal regardless of payload, and
    # by the shared-type invariant a stuck `VNe` of `Squash A` shape is
    # equal to any `VSquashIntro` (the neutral has no other inhabitants
    # up to definitional equality).
    else if t1 == "VSquash" && t2 == "VSquash" then
      conv d v1.A v2.A
    else if t1 == "VSquashIntro" && t2 == "VSquashIntro" then true
    else if t1 == "VSquashIntro" && t2 == "VNe" then true
    else if t1 == "VNe" && t2 == "VSquashIntro" then true

    # Opaque lambda: identity on _fnBox (Nix attrset thunk identity) + structural piTy
    else if t1 == "VOpaqueLam" && t2 == "VOpaqueLam" then
      v1._fnBox == v2._fnBox && conv d v1.piTy v2.piTy

    # §6.4 Neutrals — same head variable and convertible spines
    else if t1 == "VNe" && t2 == "VNe" then
      v1.level == v2.level && convSp d v1.spine v2.spine

    # §6.5 Catch-all — different constructors are never equal
    else false;

  # Classifies the d-incrementing binder arms (VPi/VLam/eta/VSigma) for `cPeel`
  # so binder layers peel flat. `a`/`b` already forced. Returns a layer record
  # (na/nb = spine-next at depth nd), or null to fall through to structural/base.
  #
  # Lift guard comes first: a VLam-vs-collapsing-VLift goal collapses via Lift in
  # convStep, so it returns null here rather than being read as eta.
  cPeelBinder = d: a: b:
    let
      ta = a.tag; tb = b.tag;
      goal = x: y: { inherit d; a = x; b = y; };
      layer = goals: na: nb: nd: { kind = "layer"; inherit goals na nb nd; };
      fv = V.freshVar d;
    in
    if (ta == "VLift" && convLevel a.l a.m)
    || (tb == "VLift" && convLevel b.l b.m)
    || (ta == "VLiftIntro" && convLevel a.l a.m)
    || (tb == "VLiftIntro" && convLevel b.l b.m)
    then null
    else if ta == "VPi" && tb == "VPi" then
      layer [ (goal a.domain b.domain) ] (E.instantiate a.closure fv) (E.instantiate b.closure fv) (d + 1)
    else if ta == "VLam" && tb == "VLam" then
      layer [ ] (E.instantiate a.closure fv) (E.instantiate b.closure fv) (d + 1)
    else if ta == "VLam" then
      let etaFn = etaReducedFn a.closure; in
      if etaFn != null then layer [ ] etaFn b d
      else layer [ ] (E.instantiate a.closure fv) (E.vApp b fv) (d + 1)
    else if tb == "VLam" then
      let etaFn = etaReducedFn b.closure; in
      if etaFn != null then layer [ ] a etaFn d
      else layer [ ] (E.vApp a fv) (E.instantiate b.closure fv) (d + 1)
    else if ta == "VSigma" && tb == "VSigma" then
      layer [ (goal a.fst b.fst) ] (E.instantiate a.closure fv) (E.instantiate b.closure fv) (d + 1)
    else null;

  # Classifies the non-binder deep arms (VNe spine, VMu/VDesc/VBootEq towers)
  # for `cPeel` so they peel onto the machine's goal stack instead of recursing
  # natively. `a`/`b` already forced. Returns a layer record, or null to fall
  # through to a base goal (`convStep` then rejects it shallowly — the native
  # arms short-circuit before any deep walk on the failure path).
  #
  # VNe×VNe routes every spine frame's `elimGoals` onto the frontier (one goal
  # designated as the na/nb continuation, the rest siblings); level/length
  # mismatch or a non-matching/guard-failing frame returns null. The compound
  # arms peel one slot as the continuation and emit the others as siblings,
  # matching the native conjunction exactly (a conjunction is order-insensitive
  # and these arms are throw-free, so machine `all` and native `&&` agree).
  cPeelArm = d: a: b:
    let
      ta = a.tag; tb = b.tag;
      goal = x: y: { inherit d; a = x; b = y; };
      layer = goals: na: nb: { kind = "layer"; inherit goals na nb; nd = d; };
    in
    if ta != tb then null
    else if ta == "VNe" then
      if a.level != b.level then null
      else
        let
          sp1 = a.spine; sp2 = b.spine;
          len = builtins.length sp1;
        in
        if len != builtins.length sp2 then null
        else
          let
            frames = builtins.genList
              (i: elimGoals d (builtins.elemAt sp1 i) (builtins.elemAt sp2 i)) len;
            bad = builtins.any (r: r == null || !r.guard) frames;
          in
          if bad then null
          else
            let goals = builtins.concatLists (map (r: r.goals) frames); in
            if goals == [ ] then null
            else
              let
                n = builtins.length goals;
                cont = builtins.elemAt goals (n - 1);
              in
              layer (builtins.genList (i: builtins.elemAt goals i) (n - 1)) cont.a cont.b
    else if ta == "VBootEq" then
      layer [ (goal a.lhs b.lhs) (goal a.rhs b.rhs) ] a.type b.type
    else if ta == "VMu" then
      layer [ (goal a.I b.I) (goal a.i b.i) ] a.D b.D
    else if ta == "VDesc" then
      let
        levOk =
          (a.level.tag == "VLevelZero" && b.level.tag == "VLevelZero")
          || convLevel a.level b.level;
        iLevOk = convLevel (a.iLev or V.vLevelZero) (b.iLev or V.vLevelZero);
      in
      if levOk && iLevOk then layer [ ] a.I b.I
      else null
    else null;

  # Native-recursion C-stack budget. A goal recursing deeper than this bounces
  # to the heap-bounded machine; far above real conversion depths, so shallow
  # goals never bounce.
  convDepthFuel = 512;

  # Definitional equality at binding depth d, and the recursion knot. The native
  # arms run on the C-stack under the recursion budget; on exhaustion the goal
  # bounces to the heap-bounded machine, which handles any remaining depth and
  # any shape (`cPeel` is total — its base fallback hands leaves back to
  # `convStep`). Shallow goals never bounce, so carry no machine cost. Both paths
  # decompose through the shared `cPeel`/`elimGoals` authority, so cannot drift.
  convF = fuel: d: v1: v2:
    let
      a = E.forceVal v1; b = E.forceVal v2;
    in
    if fuel <= 0
    then E.machine.runConvF E.dispatch.defaultFuel d a b
    else convStepForcedF (fuel - 1) d a b;
  conv = convF convDepthFuel;

  # -- Spine conversion --
  convSpF = fuel: d: sp1: sp2:
    let
      convElim = convElimF fuel;
      len1 = builtins.length sp1; len2 = builtins.length sp2;
    in
    if len1 != len2 then false
    else if len1 == 0 then true
    else
      builtins.foldl'
        (acc: i:
          acc && convElim d (builtins.elemAt sp1 i) (builtins.elemAt sp2 i)
        )
        true
        (builtins.genList (i: i) len1);
  convSp = convSpF convDepthFuel;

  # -- Elimination frame decomposition --
  #
  # Single source of truth for frame equality: decomposes a frame pair into
  # `{ guard; goals }` (guard = eager bool prerequisite, goals = sub-`conv`
  # obligations) or `null` when the frame tags cannot match. Native `convElim`
  # and the machine's `cPeelArm` both consume it, so the two encodings cannot
  # drift. Slot levels route as ordinary `conv` goals (a VLevel dispatches to
  # `convLevel`); ELiftElim keeps an explicit `convLevel` guard because
  # `convLevel` and `conv` differ on a stuck Level neutral carrying a spine.
  elimGoals = d: e1: e2:
    let
      t1 = e1.tag; t2 = e2.tag;
      goal = x: y: { inherit d; a = x; b = y; };
      ok = goals: { guard = true; inherit goals; };
    in
    if t1 != t2 then null
    else if t1 == "EApp" then ok [ (goal e1.arg e2.arg) ]
    else if t1 == "EFst" then ok [ ]
    else if t1 == "ESnd" then ok [ ]
    else if t1 == "EBootSumElim" then
      ok [ (goal e1.left e2.left) (goal e1.right e2.right) (goal e1.motive e2.motive)
        (goal e1.onLeft e2.onLeft) (goal e1.onRight e2.onRight) ]
    else if t1 == "EBootJ" then
      ok [ (goal e1.type e2.type) (goal e1.lhs e2.lhs) (goal e1.motive e2.motive)
        (goal e1.base e2.base) (goal e1.rhs e2.rhs) ]
    else if t1 == "EStrEq" then ok [ (goal e1.arg e2.arg) ]
    # Distinct EIntLeL/EIntLeR tags make cross-side spines non-convertible
    # via the `t1 != t2` guard, so intLe operand order is never conflated.
    else if t1 == "EIntEq" then ok [ (goal e1.arg e2.arg) ]
    else if t1 == "EIntLeL" then ok [ (goal e1.arg e2.arg) ]
    else if t1 == "EIntLeR" then ok [ (goal e1.arg e2.arg) ]
    else if t1 == "EAbsurd" then ok [ (goal e1.type e2.type) ]
    else if t1 == "EDescInd" then
      ok [ (goal e1.D e2.D) (goal e1.motive e2.motive) (goal e1.step e2.step) (goal e1.i e2.i) ]
    # EInterpD / EAllD / EEverywhereD spine frames — stuck `interpD` /
    # `allD` / `everywhereD` applications on a neutral D scrutinee.
    # Compare slots field-wise (D is the spine head, compared by
    # `convSp`). Levels delegate to `conv`'s VLevel routing.
    else if t1 == "EInterpD" then
      ok [ (goal e1.level e2.level) (goal e1.I e2.I) (goal e1.X e2.X) (goal e1.i e2.i) ]
    else if t1 == "EAllD" then
      ok [ (goal e1.level e2.level) (goal e1.I e2.I) (goal e1.K e2.K) (goal e1.X e2.X)
        (goal e1.M e2.M) (goal e1.i e2.i) (goal e1.d e2.d) ]
    else if t1 == "EEverywhereD" then
      ok [ (goal e1.level e2.level) (goal e1.I e2.I) (goal e1.K e2.K) (goal e1.X e2.X)
        (goal e1.M e2.M) (goal e1.ih e2.ih) (goal e1.i e2.i) (goal e1.d e2.d) ]
    # ELiftElim spine frame — compare l, m, A. The `eq` slot is not
    # compared, mirroring the witness-irrelevance of the type-former.
    else if t1 == "ELiftElim" then
      { guard = convLevel e1.l e2.l && convLevel e1.m e2.m; goals = [ (goal e1.A e2.A) ]; }
    # ESquashElim spine frame — structural compare of motive shape (A,B)
    # and case function. Two stuck `recTrunc` applications agree iff they
    # agree on metadata; payload irrelevance lives at the value layer
    # (VSquashIntro/VNe rules above), not on the spine frame itself.
    else if t1 == "ESquashElim" then
      ok [ (goal e1.A e2.A) (goal e1.B e2.B) (goal e1.f e2.f) ]
    else null;

  # -- Elimination frame conversion --
  convElimF = fuel: d: e1: e2:
    let
      conv = convF fuel;
      r = elimGoals d e1 e2;
    in r != null && r.guard && builtins.all (g: conv g.d g.a g.b) r.goals;
  convElim = convElimF convDepthFuel;

in
api.namespace {
  description = "fx.tc.conv: structural conversion check on de Bruijn level values; pure TCB component asking whether two values are definitionally equal at a given depth.";
  doc = ''
    # fx.tc.conv — Conversion (Definitional Equality)

    Checks whether two values are definitionally equal at a given
    binding depth. Purely structural — no type information used, no
    eta expansion. Pure function — part of the TCB.

    ## Core Functions

    - `conv : Depth → Val → Val → Bool` — check definitional equality.
    - `convSp : Depth → Spine → Spine → Bool` — check spine equality
      (same length, pairwise `convElim`).
    - `convElim : Depth → Elim → Elim → Bool` — check elimination frame
      equality (same tag, recursively conv on carried values).

    ## Conversion Rules

    - **Structural**: same-constructor values with matching fields.
      Universe levels compared by `==`. Primitive literals by value.
    - **Binding forms**: Pi, Lam, Sigma compared under a fresh
      variable at depth d (instantiate both closures, compare at d+1).
    - **Compound values**: recursive on all components.
    - **Neutrals**: same head level and convertible spines.
    - **Catch-all**: different constructors → false.

    ## Trampolining

    Deep ordinary data is represented by generated `VDescCon` values.
    Conversion stays structural except for explicitly documented
    eta/unfolding rules.

    ## No Eta

    `conv` does not perform eta expansion: a neutral `f` and
    `λx. f(x)` are **not** definitionally equal. Cumulativity
    (`U(i) ≤ U(j)`) is handled in check.nix, not here.
  '';
  tests =
    let
      inherit (V) vPi vLam vSigma vPair
        vUnit vTt vBootSum vBootInl vBootInr vBootEq vBootRefl vU vNe
        vSquash vSquashIntro eSquashElim
        mkClosure eApp eFst eSnd eBootSumElim eBootJ;
      T = fx.tc.term;
      Q = fx.tc.quote;
      H = fx.tc.hoas;
      HI = fx.tc.hoas._internal._indexed;
      elabVal = h: E.eval [ ] (H.elab h);
      natTyVal = elabVal H.nat;
      zeroVal = elabVal H.zero;
      succZeroVal = elabVal (H.succ H.zero);
      unitFn = S: H.ann (H.lam "_" S (_: H.tt)) (H.forall "_" S (_: H.unit));
      retUnitVal = elabVal (H.retI H.unit 0 H.tt);
      retNatZeroVal = elabVal (H.retI H.nat 0 H.zero);
      retNatSuccVal = elabVal (H.retI H.nat 0 (H.succ H.zero));
      argNatVal = elabVal (H.descArg H.unit 0 H.nat (_: H.retI H.unit 0 H.tt));
      argUnitVal = elabVal (H.descArg H.unit 0 H.unit (_: H.retI H.unit 0 H.tt));
      argUOneVal = elabVal (H.descArg H.unit 1 (H.u 0) (_: H.retI H.unit 1 H.tt));
      recRetVal = elabVal (HI.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
      recNatZeroVal = elabVal (HI.recI H.nat 0 H.zero (H.retI H.nat 0 H.zero));
      recNatSuccVal = elabVal (HI.recI H.nat 0 (H.succ H.zero) (H.retI H.nat 0 H.zero));
      piNatVal = elabVal (HI.piI H.unit 0 H.nat (unitFn H.nat) (H.retI H.unit 0 H.tt));
      piUnitVal = elabVal (HI.piI H.unit 0 H.unit (unitFn H.unit) (H.retI H.unit 0 H.tt));
      piNatRecVal = elabVal (HI.piI H.unit 0 H.nat (unitFn H.nat)
        (HI.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt)));
      piUOneVal = elabVal (HI.piI H.unit 1 (H.u 0) (unitFn (H.u 0)) (H.retI H.unit 1 H.tt));
    in
    {
      # §6.1 Structural rules — reflexivity
      "conv-unit" = { expr = conv 0 vUnit vUnit; expected = true; };
      "conv-tt" = { expr = conv 0 vTt vTt; expected = true; };
      "conv-refl" = { expr = conv 0 vBootRefl vBootRefl; expected = true; };
      "conv-funext" = { expr = conv 0 V.vFunext V.vFunext; expected = true; };
      "conv-funext-refl" = { expr = conv 0 V.vFunext vBootRefl; expected = false; };
      "conv-U0" = { expr = conv 0 (vU V.vLevelZero) (vU V.vLevelZero); expected = true; };
      "conv-U1" = { expr = conv 0 (vU (V.vLevelSuc V.vLevelZero)) (vU (V.vLevelSuc V.vLevelZero)); expected = true; };

      # Primitive types
      "conv-string" = { expr = conv 0 V.vString V.vString; expected = true; };
      "conv-int" = { expr = conv 0 V.vInt V.vInt; expected = true; };
      "conv-float" = { expr = conv 0 V.vFloat V.vFloat; expected = true; };
      "conv-attrs" = { expr = conv 0 V.vAttrs V.vAttrs; expected = true; };
      "conv-path" = { expr = conv 0 V.vPath V.vPath; expected = true; };
      "conv-derivation" = { expr = conv 0 V.vDerivation V.vDerivation; expected = true; };
      "conv-derivation-not-path" = { expr = conv 0 V.vDerivation V.vPath; expected = false; };
      "conv-function" = { expr = conv 0 V.vFunction V.vFunction; expected = true; };
      "conv-any" = { expr = conv 0 V.vAny V.vAny; expected = true; };
      "conv-string-int" = { expr = conv 0 V.vString V.vInt; expected = false; };
      "conv-stringlit-eq" = { expr = conv 0 (V.vStringLit "a") (V.vStringLit "a"); expected = true; };
      "conv-stringlit-neq" = { expr = conv 0 (V.vStringLit "a") (V.vStringLit "b"); expected = false; };
      "conv-intlit-eq" = { expr = conv 0 (V.vIntLit 1) (V.vIntLit 1); expected = true; };
      "conv-intlit-neq" = { expr = conv 0 (V.vIntLit 1) (V.vIntLit 2); expected = false; };
      "conv-floatlit-eq" = { expr = conv 0 (V.vFloatLit 1.0) (V.vFloatLit 1.0); expected = true; };
      "conv-floatlit-neq" = { expr = conv 0 (V.vFloatLit 1.0) (V.vFloatLit 2.0); expected = false; };
      "conv-attrslit" = { expr = conv 0 V.vAttrsLit V.vAttrsLit; expected = true; };
      "conv-pathlit" = { expr = conv 0 V.vPathLit V.vPathLit; expected = true; };
      "conv-derivationlit" = { expr = conv 0 V.vDerivationLit V.vDerivationLit; expected = true; };
      "conv-fnlit" = { expr = conv 0 V.vFnLit V.vFnLit; expected = true; };
      "conv-anylit" = { expr = conv 0 V.vAnyLit V.vAnyLit; expected = true; };
      "conv-stringlit-intlit" = { expr = conv 0 (V.vStringLit "1") (V.vIntLit 1); expected = false; };

      # Structural rules — inequality
      "conv-string-unit" = { expr = conv 0 V.vString vUnit; expected = false; };
      "conv-unit-tt" = { expr = conv 0 vUnit vTt; expected = false; };
      "conv-U0-U1" = { expr = conv 0 (vU V.vLevelZero) (vU (V.vLevelSuc V.vLevelZero)); expected = false; };

      # Universe conv uses the Level normaliser on the level argument,
      # so distinct-but-equivalent Level values match at VU.
      "conv-U-max-zero-zero-vs-U0" = {
        expr = conv 0 (vU (V.vLevelMax V.vLevelZero V.vLevelZero)) (vU V.vLevelZero);
        expected = true;
      };
      "conv-U-suc-max-a-a-vs-suc-a" = {
        # `U(suc (max a a)) ≡ U(suc a)` where a = suc zero.
        expr = conv 0
          (vU (V.vLevelSuc
            (V.vLevelMax (V.vLevelSuc V.vLevelZero) (V.vLevelSuc V.vLevelZero))))
          (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)));
        expected = true;
      };
      "conv-U-distinct-levels-rejects" = {
        expr = conv 0
          (vU (V.vLevelSuc V.vLevelZero))
          (vU (V.vLevelSuc (V.vLevelSuc V.vLevelZero)));
        expected = false;
      };

      # Level sort
      "conv-vlevel" = { expr = conv 0 V.vLevel V.vLevel; expected = true; };
      "conv-vlevel-string" = { expr = conv 0 V.vLevel V.vString; expected = false; };
      "conv-level-zero" = {
        expr = conv 0 V.vLevelZero V.vLevelZero;
        expected = true;
      };
      "conv-level-suc-zero" = {
        expr = conv 0 (V.vLevelSuc V.vLevelZero) (V.vLevelSuc V.vLevelZero);
        expected = true;
      };
      "conv-level-suc-neq" = {
        expr = conv 0 V.vLevelZero (V.vLevelSuc V.vLevelZero);
        expected = false;
      };

      # Canonicalisation rules: idempotence, zero absorption, suc
      # distribution over max, sorted spine.
      "level-idempotent-max-a-a" = {
        # max zero zero ≡ zero
        expr = conv 0
          (V.vLevelMax V.vLevelZero V.vLevelZero)
          V.vLevelZero;
        expected = true;
      };
      "level-max-a-zero" = {
        # max (suc zero) zero ≡ suc zero
        expr = conv 0
          (V.vLevelMax (V.vLevelSuc V.vLevelZero) V.vLevelZero)
          (V.vLevelSuc V.vLevelZero);
        expected = true;
      };
      "level-max-zero-a" = {
        # max zero (suc zero) ≡ suc zero
        expr = conv 0
          (V.vLevelMax V.vLevelZero (V.vLevelSuc V.vLevelZero))
          (V.vLevelSuc V.vLevelZero);
        expected = true;
      };
      "level-suc-distributes-over-max" = {
        # suc (max (suc zero) zero) ≡ max (suc (suc zero)) (suc zero)
        expr = conv 0
          (V.vLevelSuc (V.vLevelMax (V.vLevelSuc V.vLevelZero) V.vLevelZero))
          (V.vLevelMax (V.vLevelSuc (V.vLevelSuc V.vLevelZero)) (V.vLevelSuc V.vLevelZero));
        expected = true;
      };
      "level-max-sorted-spine-closed" = {
        # max (suc zero) (suc zero) ≡ suc zero (idempotence collapses the pair)
        expr = conv 0
          (V.vLevelMax (V.vLevelSuc V.vLevelZero) (V.vLevelSuc V.vLevelZero))
          (V.vLevelSuc V.vLevelZero);
        expected = true;
      };
      "level-max-associative" = {
        # max a (max b c) ≡ max (max a b) c — at the canonical-form level
        # this is structural merging, so any 3-arity max expression equates.
        expr = conv 0
          (V.vLevelMax V.vLevelZero
            (V.vLevelMax (V.vLevelSuc V.vLevelZero) V.vLevelZero))
          (V.vLevelMax
            (V.vLevelMax V.vLevelZero (V.vLevelSuc V.vLevelZero))
            V.vLevelZero);
        expected = true;
      };
      "level-max-distinct-shifts-preserved" = {
        # max (suc zero) (suc (suc zero)) ≢ suc zero — different top shifts.
        expr = conv 0
          (V.vLevelMax (V.vLevelSuc V.vLevelZero)
            (V.vLevelSuc (V.vLevelSuc V.vLevelZero)))
          (V.vLevelSuc V.vLevelZero);
        expected = false;
      };
      "level-suc-suc-zero-self" = {
        # suc (suc zero) ≡ suc (suc zero)
        expr = conv 0
          (V.vLevelSuc (V.vLevelSuc V.vLevelZero))
          (V.vLevelSuc (V.vLevelSuc V.vLevelZero));
        expected = true;
      };
      "level-suc-suc-zero-neq-suc-zero" = {
        expr = conv 0
          (V.vLevelSuc (V.vLevelSuc V.vLevelZero))
          (V.vLevelSuc V.vLevelZero);
        expected = false;
      };

      # Closed levels beyond the fast-path node budget fall back to the
      # spine pipeline. `max (suc^100 zero) zero` defeats the syntactic
      # `==` shortcut against `suc^100 zero` while staying equal.
      "level-deep-closed-budget-fallback-eq" = {
        expr =
          let
            suc100 = builtins.foldl' (v: _: V.vLevelSuc v) V.vLevelZero
              (builtins.genList (i: i) 100);
          in
          conv 0 (V.vLevelMax suc100 V.vLevelZero) suc100;
        expected = true;
      };
      "level-deep-closed-budget-fallback-neq" = {
        expr =
          let
            sucN = n: builtins.foldl' (v: _: V.vLevelSuc v) V.vLevelZero
              (builtins.genList (i: i) n);
          in
          conv 0 (sucN 100) (sucN 101);
        expected = false;
      };
      # Neutral-containing levels skip the closed fast path; idempotent
      # max over a level variable still equates via the spine pipeline.
      "level-neutral-max-idempotent" = {
        expr =
          let x = V.freshVar 0; in
          conv 1 (vU (V.vLevelMax x x)) (vU x);
        expected = true;
      };
      "level-closed-vs-neutral-rejects" = {
        expr = conv 1 (vU V.vLevelZero) (vU (V.freshVar 0));
        expected = false;
      };

      # Generated Nat values
      "conv-generated-zero" = { expr = conv 0 zeroVal zeroVal; expected = true; };
      "conv-generated-succ-neq" = { expr = conv 0 zeroVal succZeroVal; expected = false; };
      "conv-generated-succ-self" = {
        expr = conv 0 succZeroVal succZeroVal;
        expected = true;
      };

      # §6.2 Binding forms
      "conv-pi" = {
        # Π(x:Unit).Unit ≡ Π(y:Unit).Unit (names don't matter)
        expr = conv 0
          (vPi "x" vUnit (mkClosure [ ] T.mkUnit))
          (vPi "y" vUnit (mkClosure [ ] T.mkUnit));
        expected = true;
      };
      "conv-pi-diff-domain" = {
        expr = conv 0
          (vPi "x" V.vString (mkClosure [ ] T.mkString))
          (vPi "x" vUnit (mkClosure [ ] T.mkString));
        expected = false;
      };
      "conv-pi-diff-codomain" = {
        expr = conv 0
          (vPi "x" vUnit (mkClosure [ ] T.mkUnit))
          (vPi "x" vUnit (mkClosure [ ] T.mkString));
        expected = false;
      };
      "conv-pi-dependent" = {
        # Π(x:Unit).x ≡ Π(y:Unit).y — both bodies reference the bound var
        expr = conv 0
          (vPi "x" vUnit (mkClosure [ ] (T.mkVar 0)))
          (vPi "y" vUnit (mkClosure [ ] (T.mkVar 0)));
        expected = true;
      };

      # Binding forms with different dependent bodies
      "conv-pi-dep-diff-body" = {
        # Π(x:Unit).x vs Π(x:Unit).Unit — different dependent codomains
        expr = conv 0
          (vPi "x" vUnit (mkClosure [ ] (T.mkVar 0)))
          (vPi "x" vUnit (mkClosure [ ] T.mkUnit));
        expected = false;
      };
      "conv-sigma-dep-diff-body" = {
        # Σ(x:Unit).x vs Σ(x:Unit).Unit — different dependent second components
        expr = conv 0
          (vSigma "x" vUnit (mkClosure [ ] (T.mkVar 0)))
          (vSigma "x" vUnit (mkClosure [ ] T.mkUnit));
        expected = false;
      };
      "conv-ne-multi-spine-diff" = {
        # x₀(tt)(tt) vs x₀(tt)(Unit) — second frame differs
        expr = conv 2
          (vNe 0 [ (eApp vTt) (eApp vTt) ])
          (vNe 0 [ (eApp vTt) (eApp vUnit) ]);
        expected = false;
      };

      "conv-lam" = {
        # λ(x:Unit).x ≡ λ(y:Unit).y
        expr = conv 0
          (vLam "x" vUnit (mkClosure [ ] (T.mkVar 0)))
          (vLam "y" vUnit (mkClosure [ ] (T.mkVar 0)));
        expected = true;
      };
      "conv-lam-diff-body" = {
        expr = conv 0
          (vLam "x" vUnit (mkClosure [ ] T.mkTt))
          (vLam "x" vUnit (mkClosure [ ] T.mkUnit));
        expected = false;
      };
      "conv-sigma" = {
        expr = conv 0
          (vSigma "x" vUnit (mkClosure [ ] T.mkUnit))
          (vSigma "y" vUnit (mkClosure [ ] T.mkUnit));
        expected = true;
      };

      # §6.3 Compound values
      "conv-pair" = { expr = conv 0 (vPair vTt vTt) (vPair vTt vTt); expected = true; };
      "conv-pair-diff" = { expr = conv 0 (vPair vTt vTt) (vPair vTt vUnit); expected = false; };
      "conv-sum" = { expr = conv 0 (vBootSum vUnit vUnit) (vBootSum vUnit vUnit); expected = true; };
      "conv-inl" = {
        expr = conv 0 (vBootInl vUnit vUnit vTt) (vBootInl vUnit vUnit vTt);
        expected = true;
      };
      "conv-inl-diff" = {
        expr = conv 0 (vBootInl vUnit vUnit vTt) (vBootInl vUnit vUnit vUnit);
        expected = false;
      };
      "conv-inr" = {
        expr = conv 0 (vBootInr vUnit vUnit vTt) (vBootInr vUnit vUnit vTt);
        expected = true;
      };
      "conv-eq" = {
        expr = conv 0 (vBootEq vUnit vTt vTt) (vBootEq vUnit vTt vTt);
        expected = true;
      };
      "conv-eq-diff" = {
        expr = conv 0 (vBootEq vUnit vTt vTt) (vBootEq vUnit vTt vUnit);
        expected = false;
      };

      # §6.4 Neutrals
      "conv-ne-same" = { expr = conv 1 (vNe 0 [ ]) (vNe 0 [ ]); expected = true; };
      "conv-ne-diff-level" = { expr = conv 2 (vNe 0 [ ]) (vNe 1 [ ]); expected = false; };
      "conv-ne-app" = {
        expr = conv 1 (vNe 0 [ (eApp vTt) ]) (vNe 0 [ (eApp vTt) ]);
        expected = true;
      };
      "conv-ne-app-diff" = {
        expr = conv 1 (vNe 0 [ (eApp vTt) ]) (vNe 0 [ (eApp vUnit) ]);
        expected = false;
      };
      "conv-ne-fst" = {
        expr = conv 1 (vNe 0 [ eFst ]) (vNe 0 [ eFst ]);
        expected = true;
      };
      "conv-ne-snd" = {
        expr = conv 1 (vNe 0 [ eSnd ]) (vNe 0 [ eSnd ]);
        expected = true;
      };
      "conv-ne-diff-spine-len" = {
        expr = conv 1 (vNe 0 [ (eApp vTt) ]) (vNe 0 [ ]);
        expected = false;
      };
      "conv-ne-diff-elim" = {
        expr = conv 1 (vNe 0 [ eFst ]) (vNe 0 [ eSnd ]);
        expected = false;
      };
      "conv-ne-sum-elim" = {
        expr = conv 1 (vNe 0 [ (eBootSumElim vUnit vUnit vUnit vTt vTt) ]) (vNe 0 [ (eBootSumElim vUnit vUnit vUnit vTt vTt) ]);
        expected = true;
      };
      "conv-ne-j" = {
        expr = conv 1 (vNe 0 [ (eBootJ vUnit vTt vUnit vTt vTt) ]) (vNe 0 [ (eBootJ vUnit vTt vUnit vTt vTt) ]);
        expected = true;
      };

      # Symmetry property
      "conv-sym-string-unit" = {
        expr = (conv 0 V.vString vUnit) == (conv 0 vUnit V.vString);
        expected = true;
      };
      "conv-sym-generated-nat" = {
        expr = let a = zeroVal; b = succZeroVal; in
          (conv 0 a b) == (conv 0 b a);
        expected = true;
      };

      # Pi-eta: f ≡ λx. f x. freshVar(0) is a neutral function value;
      # `λx. f x` is its eta-expansion. Both must convert under the rule.
      "conv-pi-eta-neutral-vs-lam" = {
        expr = conv 1
          (V.freshVar 0)
          (vLam "x" vUnit (mkClosure [ (V.freshVar 0) ] (T.mkApp (T.mkVar 1) (T.mkVar 0))));
        expected = true;
      };
      "conv-pi-eta-lam-vs-neutral" = {
        expr = conv 1
          (vLam "x" vUnit (mkClosure [ (V.freshVar 0) ] (T.mkApp (T.mkVar 1) (T.mkVar 0))))
          (V.freshVar 0);
        expected = true;
      };
      # Pi-eta degenerate case: λx. tt vs a function-typed neutral with
      # codomain ⊤. Under the binder, both reduce to `tt` (via ⊤-eta on
      # the right). Exercises the exact pattern that motivates pi-eta in
      # the levitation iso (descPi's f-slot of type S → ⊤).
      "conv-pi-eta-unit-codomain" = {
        expr = conv 1
          (V.freshVar 0)
          (vLam "_" vUnit (mkClosure [ ] T.mkTt));
        expected = true;
      };

      # §6.3a Sigma-eta: ⟨fst x, snd x⟩ ≡ x for neutral x
      "conv-sigma-eta-pair-vs-neutral" = {
        expr = let x = V.freshVar 0; in
          conv 1 (vPair (E.vFst x) (E.vSnd x)) x;
        expected = true;
      };
      "conv-sigma-eta-neutral-vs-pair" = {
        expr = let x = V.freshVar 0; in
          conv 1 x (vPair (E.vFst x) (E.vSnd x));
        expected = true;
      };
      # Counter-example: fst and snd of DIFFERENT neutrals is NOT sigma-eta on a single x
      "conv-sigma-eta-distinct-neutrals-rejected" = {
        expr = let x = V.freshVar 0; y = V.freshVar 1; in
          conv 2 (vPair (E.vFst x) (E.vSnd y)) x;
        expected = false;
      };
      # Counter-example: comparing a pair against a non-Sigma-typed neutral (e.g. a
      # nat-valued neutral) should fail: VPair components won't conv with vFst/vSnd
      # spine extensions on a neutral whose existing spine is nat-indexed, because
      # the `a ≡ vFst v2` sub-conv returns false structurally.
      "conv-sigma-eta-unrelated-values-rejected" = {
        expr = conv 0 (vPair vTt vUnit) (V.freshVar 0);
        # freshVar 0 is a bare VNe with empty spine; vFst (VNe 0 []) = VNe 0 [EFst],
        # structural-conv with VUnit returns false.
        expected = false;
      };

      # §6.3b Unit-eta: x ≡ tt for neutral x : ⊤
      "conv-unit-eta-tt-vs-neutral" = {
        expr = conv 1 vTt (V.freshVar 0);
        expected = true;
      };
      "conv-unit-eta-neutral-vs-tt" = {
        expr = conv 1 (V.freshVar 0) vTt;
        expected = true;
      };

      # Descriptions
      "conv-desc" = { expr = conv 0 (V.vDesc V.vLevelZero V.vUnit) (V.vDesc V.vLevelZero V.vUnit); expected = true; };
      "conv-desc-diff-I" = {
        expr = conv 0 (V.vDesc V.vLevelZero V.vUnit) (V.vDesc V.vLevelZero natTyVal);
        expected = false;
      };
      "conv-descret" = {
        expr = conv 0 retUnitVal retUnitVal;
        expected = true;
      };
      "conv-descret-diff-j" = {
        # Eta-unit aside: at j : Nat level, two distinct j's don't conv.
        expr = conv 0 retNatZeroVal retNatSuccVal;
        expected = false;
      };
      "conv-descarg" = {
        expr = conv 0 argNatVal argNatVal;
        expected = true;
      };
      "conv-descarg-diff-S" = {
        expr = conv 0 argNatVal argUnitVal;
        expected = false;
      };
      "conv-descarg-diff-k" = {
        expr = conv 0 argNatVal argUOneVal;
        expected = false;
      };
      "conv-descarg-same-k-one" = {
        expr = conv 0 argUOneVal argUOneVal;
        expected = true;
      };
      "conv-descrec" = {
        expr = conv 0 recRetVal recRetVal;
        expected = true;
      };
      "conv-descrec-diff-j" = {
        expr = conv 0 recNatZeroVal recNatSuccVal;
        expected = false;
      };
      "conv-descpi" = {
        expr = conv 0 piNatVal piNatVal;
        expected = true;
      };
      "conv-descpi-diff-S" = {
        expr = conv 0 piNatVal piUnitVal;
        expected = false;
      };
      "conv-descpi-diff-D" = {
        expr = conv 0 piNatVal piNatRecVal;
        expected = false;
      };
      "conv-descpi-diff-k" = {
        expr = conv 0 piNatVal piUOneVal;
        expected = false;
      };
      "conv-mu" = {
        expr = conv 0
          (V.vMu vUnit retUnitVal vTt)
          (V.vMu vUnit retUnitVal vTt);
        expected = true;
      };
      "conv-mu-diff-D" = {
        expr = conv 0
          (V.vMu vUnit retUnitVal vTt)
          (V.vMu vUnit recRetVal vTt);
        expected = false;
      };
      "conv-mu-diff-i" = {
        expr = conv 0
          (V.vMu natTyVal retNatZeroVal zeroVal)
          (V.vMu natTyVal retNatZeroVal succZeroVal);
        expected = false;
      };
      "conv-mu-diff-I" = {
        expr = conv 0
          (V.vMu vUnit retUnitVal vTt)
          (V.vMu natTyVal retUnitVal vTt);
        expected = false;
      };
      "conv-desccon" = {
        expr = conv 0
          (V.vDescCon retUnitVal vTt vBootRefl)
          (V.vDescCon retUnitVal vTt vBootRefl);
        expected = true;
      };
      "conv-generated-nat-100-self" = {
        expr = let n = elabVal (H.natLit 100); in conv 0 n n;
        expected = true;
      };
      "conv-generated-nat-99-100-rejects" = {
        expr = conv 0 (elabVal (H.natLit 99)) (elabVal (H.natLit 100));
        expected = false;
      };
      "conv-ne-desc-ind" = {
        expr = conv 1
          (vNe 0 [ (V.eDescInd retUnitVal vUnit vTt vTt) ])
          (vNe 0 [ (V.eDescInd retUnitVal vUnit vTt vTt) ]);
        expected = true;
      };
      "conv-ne-desc-ind-diff" = {
        expr = conv 1
          (vNe 0 [ (V.eDescInd retUnitVal vUnit vTt vTt) ])
          (vNe 0 [ (V.eDescInd retUnitVal vUnit vUnit vTt) ]);
        expected = false;
      };
      # EInterpD / EAllD / EEverywhereD spine frames — stuck `interpD` /
      # `allD` / `everywhereD` applications on a neutral D scrutinee.
      # Field-wise compare; mismatch on any slot rejects.
      "conv-ne-interp-d" = {
        expr = conv 1
          (vNe 0 [ (V.eInterpD V.vLevelZero vUnit vUnit vTt) ])
          (vNe 0 [ (V.eInterpD V.vLevelZero vUnit vUnit vTt) ]);
        expected = true;
      };
      "conv-ne-interp-d-diff-X" = {
        expr = conv 1
          (vNe 0 [ (V.eInterpD V.vLevelZero vUnit vUnit vTt) ])
          (vNe 0 [ (V.eInterpD V.vLevelZero vUnit V.vString vTt) ]);
        expected = false;
      };
      "conv-ne-interp-d-diff-level" = {
        expr = conv 1
          (vNe 0 [ (V.eInterpD V.vLevelZero vUnit vUnit vTt) ])
          (vNe 0 [ (V.eInterpD (V.vLevelSuc V.vLevelZero) vUnit vUnit vTt) ]);
        expected = false;
      };
      "conv-ne-all-d" = {
        expr = conv 1
          (vNe 0 [ (V.eAllD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vBootRefl) ])
          (vNe 0 [ (V.eAllD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vBootRefl) ]);
        expected = true;
      };
      "conv-ne-all-d-diff-K" = {
        expr = conv 1
          (vNe 0 [ (V.eAllD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vBootRefl) ])
          (vNe 0 [ (V.eAllD V.vLevelZero vUnit (V.vLevelSuc V.vLevelZero) vUnit vUnit vTt vBootRefl) ]);
        expected = false;
      };
      "conv-ne-everywhere-d" = {
        expr = conv 1
          (vNe 0 [ (V.eEverywhereD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vTt vBootRefl) ])
          (vNe 0 [ (V.eEverywhereD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vTt vBootRefl) ]);
        expected = true;
      };
      "conv-ne-everywhere-d-diff-ih" = {
        expr = conv 1
          (vNe 0 [ (V.eEverywhereD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vTt vTt vBootRefl) ])
          (vNe 0 [ (V.eEverywhereD V.vLevelZero vUnit V.vLevelZero vUnit vUnit vUnit vTt vBootRefl) ]);
        expected = false;
      };

      # Desc/μ unfolding. `Desc I k ≡ μ ⊤ (descDesc I k) tt` — the
      # surface name `Desc` keeps working under the descDesc-encoded
      # μ-form. Decidable: descDesc is a closed VLam, vApp on v1.I and
      # v1.level reduces to a finite description tree, and structural
      # conv on the result terminates.
      "conv-desc-mu-unfold-trivial" = {
        # Desc ⊤ 0 ≡ μ ⊤ (descDesc ⊤ 0) tt — prelude slice (k=0, I=⊤).
        expr =
          let
            lhs = V.vDesc V.vLevelZero V.vUnit;
            expectedD = E.mkDescDescAppV V.vLevelZero V.vUnit V.vLevelZero;
            rhs = V.vMu V.vUnit expectedD V.vTt;
          in
          conv 0 lhs rhs;
        expected = true;
      };
      "conv-mu-desc-unfold-trivial" = {
        # Symmetric direction: μ ⊤ (descDesc ⊤ 0) tt ≡ Desc ⊤ 0.
        expr =
          let
            expectedD = E.mkDescDescAppV V.vLevelZero V.vUnit V.vLevelZero;
            lhs = V.vMu V.vUnit expectedD V.vTt;
            rhs = V.vDesc V.vLevelZero V.vUnit;
          in
          conv 0 lhs rhs;
        expected = true;
      };
      "conv-desc-mu-unfold-generated-nat-k0" = {
        # Desc Nat 0 ≡ μ ⊤ (descDesc Nat 0) tt — non-⊤ I slice.
        expr =
          let
            lhs = V.vDesc V.vLevelZero natTyVal;
            expectedD = E.mkDescDescAppV V.vLevelZero natTyVal V.vLevelZero;
            rhs = V.vMu V.vUnit expectedD V.vTt;
          in
          conv 0 lhs rhs;
        expected = true;
      };
      "conv-desc-mu-unfold-suc-k" = {
        # Desc ⊤ 1 ≡ μ ⊤ (descDesc ⊤ 1) tt — non-zero level.
        expr =
          let
            levelOne = V.vLevelSuc V.vLevelZero;
            lhs = V.vDesc levelOne V.vUnit;
            expectedD = E.mkDescDescAppV V.vLevelZero V.vUnit levelOne;
            rhs = V.vMu V.vUnit expectedD V.vTt;
          in
          conv 0 lhs rhs;
        expected = true;
      };
      "conv-desc-mu-mismatch-encoded-I-rejected" = {
        # Desc Nat 0 ≢ μ ⊤ (descDesc ⊤ 0) tt — v2.D encodes I=⊤ but v1
        # demands I=Nat. Structural conv on the descDesc tree distinguishes.
        expr =
          let
            lhs = V.vDesc V.vLevelZero natTyVal;
            expectedD = E.mkDescDescAppV V.vLevelZero V.vUnit V.vLevelZero;
            rhs = V.vMu V.vUnit expectedD V.vTt;
          in
          conv 0 lhs rhs;
        expected = false;
      };
      "conv-desc-mu-mismatch-mu-I-rejected" = {
        # μ Nat (descDesc ⊤ 0) zero ≢ Desc ⊤ 0 — v1's outer I is Nat,
        # not ⊤, so the unfolding's ⊤-slot check fails.
        expr =
          let
            expectedD = E.mkDescDescAppV V.vLevelZero V.vUnit V.vLevelZero;
            lhs = V.vMu natTyVal expectedD zeroVal;
            rhs = V.vDesc V.vLevelZero V.vUnit;
          in
          conv 0 lhs rhs;
        expected = false;
      };

      # Lift primitive — idempotent collapse, structural with
      # witness-irrelevance, eta on stuck neutrals, ELiftElim spine.
      "conv-lift-idempotent-collapse-vs-A" = {
        # Lift l l _ A ≡ A — homogeneous lift idempotence.
        expr = conv 0 (V.vLift V.vLevelZero V.vLevelZero V.vBootRefl vUnit) vUnit;
        expected = true;
      };
      "conv-lift-idempotent-collapse-A-vs" = {
        # Symmetric direction — A ≡ Lift l l _ A.
        expr = conv 0 vUnit (V.vLift V.vLevelZero V.vLevelZero V.vBootRefl vUnit);
        expected = true;
      };
      "conv-lift-intro-idempotent-collapse-vs-a" = {
        # lift l l _ A a ≡ a.
        expr = conv 0 (V.vLiftIntro V.vLevelZero V.vLevelZero V.vBootRefl vUnit vTt) vTt;
        expected = true;
      };
      "conv-lift-intro-idempotent-collapse-a-vs" = {
        expr = conv 0 vTt (V.vLiftIntro V.vLevelZero V.vLevelZero V.vBootRefl vUnit vTt);
        expected = true;
      };
      "conv-lift-structural-equal" = {
        # Lift 0 1 _ Unit ≡ Lift 0 1 _ Unit at distinct levels.
        expr = conv 0
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit)
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit);
        expected = true;
      };
      "conv-lift-structural-diff-A" = {
        # Differing underlying types do not convert.
        expr = conv 0
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit)
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl V.vString);
        expected = false;
      };
      "conv-lift-structural-diff-m" = {
        expr = conv 0
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit)
          (V.vLift V.vLevelZero (V.vLevelSuc (V.vLevelSuc V.vLevelZero)) V.vBootRefl vUnit);
        expected = false;
      };
      "conv-lift-witness-irrelevance" = {
        # The `eq` slot is not compared — two `VLift`s with structurally
        # different but propositionally-equal witnesses convert.
        # vBootRefl vs (vBootRefl) is a degenerate case; substitute distinct
        # placeholder values to confirm the eq slot is not consulted.
        expr = conv 0
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit)
          (V.vLift V.vLevelZero (V.vLevelSuc V.vLevelZero) vTt vUnit);
        expected = true;
      };
      "conv-lift-intro-structural-equal" = {
        expr = conv 0
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit vTt)
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit vTt);
        expected = true;
      };
      "conv-lift-intro-structural-diff-a" = {
        expr = conv 0
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl V.vString (V.vStringLit "a"))
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl V.vString (V.vStringLit "b"));
        expected = false;
      };
      "conv-lift-intro-witness-irrelevance" = {
        expr = conv 0
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) V.vBootRefl vUnit vTt)
          (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero) vTt vUnit vTt);
        expected = true;
      };
      "conv-lift-eta-intro-vs-neutral" = {
        # lift _ _ a ≡ x for stuck x : Lift — fires by η applied to the
        # neutral on the right. Construct: the neutral `x` is a fresh var
        # standing for an inhabitant of `Lift 0 1 _ Unit`. The intro side
        # pairs `a = lower x`. Both should convert.
        expr =
          let
            x = V.freshVar 0;
            loweredX = E.vLiftElimF V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit
              x;
          in
          conv 1
            (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit
              loweredX)
            x;
        expected = true;
      };
      "conv-lift-eta-neutral-vs-intro" = {
        # Symmetric direction.
        expr =
          let
            x = V.freshVar 0;
            loweredX = E.vLiftElimF V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit
              x;
          in
          conv 1
            x
            (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit
              loweredX);
        expected = true;
      };
      "conv-ne-lift-elim" = {
        # Two stuck `lower`s with matching params convert.
        expr = conv 1
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit)
          ])
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit)
          ]);
        expected = true;
      };
      "conv-ne-lift-elim-diff-A" = {
        expr = conv 1
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit)
          ])
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              V.vString)
          ]);
        expected = false;
      };
      "conv-ne-lift-elim-witness-irrelevance" = {
        # The `eq` slot is not compared in the spine frame.
        expr = conv 1
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              V.vBootRefl
              vUnit)
          ])
          (vNe 0 [
            (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
              vTt
              vUnit)
          ]);
        expected = true;
      };

      # Squash — definitional proof irrelevance. Formers descend on .A;
      # introducers and stuck neutrals at Squash type are unconditionally
      # convertible by the shared-type invariant. ESquashElim spine frames
      # compare structurally on motive shape and case function.
      "conv-squash-formers-equal" = {
        expr = conv 0 (vSquash vUnit) (vSquash vUnit);
        expected = true;
      };
      "conv-squash-formers-diff-A" = {
        expr = conv 0 (vSquash vUnit) (vSquash V.vString);
        expected = false;
      };
      "conv-squash-irrelevance" = {
        # Two distinct introducers at the same Squash type are conv-equal
        # regardless of payload identity.
        expr = conv 1 (vSquashIntro vTt) (vSquashIntro (V.freshVar 0));
        expected = true;
      };
      "conv-squash-eta-vne-left" = {
        # VSquashIntro vs stuck VNe at shared Squash type: irrelevant.
        expr = conv 1 (vSquashIntro vTt) (V.freshVar 0);
        expected = true;
      };
      "conv-squash-eta-vne-right" = {
        # Symmetric direction.
        expr = conv 1 (V.freshVar 0) (vSquashIntro vTt);
        expected = true;
      };
      "conv-ne-squash-elim" = {
        # Two stuck recTrunc spines with matching motive (A,B) and case
        # function f convert.
        expr =
          let
            f = vLam "_" vUnit (mkClosure [ ] T.mkTt);
          in
          conv 1
            (vNe 0 [ (eSquashElim vUnit vUnit f) ])
            (vNe 0 [ (eSquashElim vUnit vUnit f) ]);
        expected = true;
      };
      "conv-ne-squash-elim-diff-A" = {
        # Distinct motive types refuse conv on the spine frame.
        expr =
          let
            f = vLam "_" vUnit (mkClosure [ ] T.mkTt);
          in
          conv 1
            (vNe 0 [ (eSquashElim vUnit vUnit f) ])
            (vNe 0 [ (eSquashElim V.vString vUnit f) ]);
        expected = false;
      };

      # Stress tests — generated ordinary data
      "conv-generated-nat-5000" = {
        expr =
          let
            deep = E.eval [ ] (H.elab (H.natLit 5000));
          in
          conv 0 deep deep;
        expected = true;
      };
      "conv-generated-list-5000" = {
        expr =
          let
            deep = E.eval [ ] (H.elab (builtins.foldl'
              (acc: _:
                HI.consAtExplicit H.nat H.zero acc
              )
              (HI.nilAtExplicit H.nat)
              (builtins.genList (x: x) 5000)));
          in
          conv 0 deep deep;
        expected = true;
      };

      # Mixed-encoding arm: nested `V.vDescCon` foldl' chain (no
      # eval-time classifier, so no chain-form promotion) vs its
      # quote→eval round-tripped chain-form sibling. Exercises the
      # promote-on-the-fly path in the chain-form arm.
      "conv-crossform-roundtrip-100" = {
        expr =
          let
            unit = vUnit;
            tt   = vTt;
            listDescVal = E.eval [ ] (H.elab (H.listDesc H.nat));
            leftTy  = vBootEq unit tt tt;
            rightTy = vU V.vLevelZero;
            zV      = E.eval [ ] (H.elab H.zero);
            nilLayer = V.vDescCon listDescVal tt
              (vBootInl leftTy rightTy vBootRefl);
            consLayer = head_: tail_:
              V.vDescCon listDescVal tt
                (vBootInr leftTy rightTy
                  (vPair head_ (vPair tail_ vBootRefl)));
            v1 = builtins.foldl'
              (acc: _: consLayer zV acc)
              nilLayer
              (builtins.genList (x: x) 100);
            v2 = E.eval [ ] (Q.quote 0 v1);
          in
          conv 0 v1 v2;
        expected = true;
      };

      # Raw-vs-raw classify-peel arm where one operand's recursive TAIL is
      # chain-form (mixed encoding). Both tops are raw, so this lands in the
      # classify-peel else-arm, NOT the linearChain arm. A chain-form tail has
      # `.d = vTt` (tag "VTt" != the recursive side); the pre-oracle lockstep
      # peel treated it as a base and wrongly returned `false` on two equal
      # lists. `forceAndPeelChainV` splices the chain-form tail, flattening
      # both operands to the same N layers.
      "conv-rawtop-chainform-tail-100" = {
        expr =
          let
            unit = vUnit;
            tt   = vTt;
            listDescVal = E.eval [ ] (H.elab (H.listDesc H.nat));
            leftTy  = vBootEq unit tt tt;
            rightTy = vU V.vLevelZero;
            zV      = E.eval [ ] (H.elab H.zero);
            nilLayer = V.vDescCon listDescVal tt
              (vBootInl leftTy rightTy vBootRefl);
            consLayer = head_: tail_:
              V.vDescCon listDescVal tt
                (vBootInr leftTy rightTy
                  (vPair head_ (vPair tail_ vBootRefl)));
            innerRaw = builtins.foldl'
              (acc: _: consLayer zV acc)
              nilLayer
              (builtins.genList (x: x) 99);
            innerChain = E.eval [ ] (Q.quote 0 innerRaw);
            vRaw   = consLayer zV innerRaw;
            vMixed = consLayer zV innerChain;
          in
          conv 0 vRaw vMixed;
        expected = true;
      };

      # `_canonRef` short-circuit at VDescCon × VDescCon. Equality reduces
      # to conv on the carried `(id, params)`; `.D` is never forced.
      "conv-descDescApp-tag-self" = {
        expr =
          let
            v = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
          in
          conv 0 v v;
        expected = true;
      };
      "conv-descDescApp-tag-distinct-id-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "alpha";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "beta";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-descDescApp-tag-distinct-I-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero natTyVal V.vLevelZero ];
              };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-descDescApp-tag-distinct-L-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero V.vUnit (V.vLevelSuc V.vLevelZero) ];
              };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-descDescApp-cyclic-D-self" = {
        # The `.D` slot points back at the value itself; the tag check
        # decides equality without descending. A no-tag value with the
        # same shape would loop on the structural fall-through.
        expr =
          let
            cyclic =
              let
                v = {
                  tag = "VDescCon";
                  D = v;
                  i = vTt;
                  d = vTt;
                  _canonRef = {
                    id = "descDesc";
                    params = [ V.vLevelZero V.vUnit V.vLevelZero ];
                  };
                };
              in
              v;
          in
          conv 0 cyclic cyclic;
        expected = true;
      };
      "conv-descDescApp-cyclic-D-mismatch-rejects" = {
        expr =
          let
            mk = idStr:
              let
                v = {
                  tag = "VDescCon";
                  D = v;
                  i = vTt;
                  d = vTt;
                  _canonRef = { id = idStr; I = V.vUnit; L = V.vLevelZero; };
                };
              in
              v;
          in
          conv 0 (mk "alpha") (mk "beta");
        expected = false;
      };
      "conv-descDesc-ret-payload-neutral-leaf-irrelevant" = {
        expr =
          let
            dDesc = E.mkDescDescAppV V.vLevelZero V.vUnit V.vLevelZero;
            r = vNe 0 [ ];
            lhs = V.vDescCon dDesc vTt (vBootInl vUnit vUnit r);
            rhs = V.vDescCon dDesc vTt
              (vBootInl vUnit vUnit (vPair (E.vFst r) vBootRefl));
          in
          conv 1 lhs rhs;
        expected = true;
      };

      # `params`-shape `_canonRef` stamps. Generalised to a variadic
      # params list so canonical references with arity ≠ 3
      # (freer monad, kontQueue, ...) can use the same short-circuit.
      "conv-canonRef-params-self" = {
        expr =
          let
            v = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ V.vUnit V.vUnit V.vUnit ]; };
          in
          conv 0 v v;
        expected = true;
      };
      "conv-canonRef-params-distinct-id-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ V.vUnit V.vUnit V.vUnit ]; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "kontQueue"; params = [ V.vUnit V.vUnit V.vUnit ]; };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-canonRef-params-distinct-param-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ V.vUnit V.vUnit V.vUnit ]; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ natTyVal V.vUnit V.vUnit ]; };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-canonRef-params-arity-mismatch-rejects" = {
        expr =
          let
            v1 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ V.vUnit V.vUnit V.vUnit ]; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "freeFx"; params = [ V.vUnit V.vUnit ]; };
          in
          conv 0 v1 v2;
        expected = false;
      };
      "conv-canonRef-params-cyclic-D-self" = {
        # 4-param canon-stamped value with its `.D` slot referencing
        # itself. Tag-based comparison decides equality without
        # descending into `.D`; a no-tag value with the same shape would
        # loop on the structural fall-through.
        expr =
          let
            cyclic =
              let
                v = {
                  tag = "VDescCon";
                  D = v;
                  i = vTt;
                  d = vTt;
                  _canonRef = {
                    id = "kontQueue";
                    params = [ V.vUnit V.vUnit V.vUnit V.vUnit ];
                  };
                };
              in
              v;
          in
          conv 0 cyclic cyclic;
        expected = true;
      };
      "conv-canonRef-legacy-IL-rejects" = {
        expr =
          let
            legacy = V.vDescConTagged vTt vTt V.vBootRefl
              { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; };
            generic = V.vDescConTagged vTt vTt V.vBootRefl
              {
                id = "descDesc";
                params = [ V.vLevelZero V.vUnit V.vLevelZero ];
              };
          in
          conv 0 legacy generic;
        expected = false;
      };
    };

  value = {
    conv = api.leaf {
      value = conv;
      description = "conv: definitional equality on values at binding `depth` — purely structural with Σ/Unit/Π-eta; foundation of `Sub` in `check` and the kernel TCB.";
      signature = "conv : Depth -> Val -> Val -> Bool";
    };
    convStep = api.leaf {
      value = convStep;
      description = "convStep: single conversion step over forced values — the conv dispatch body, called by the `runConvF` machine for non-structural goals.";
      signature = "convStep : Depth -> Val -> Val -> Bool";
    };
    cPeelBinder = api.leaf {
      value = cPeelBinder;
      description = "cPeelBinder: binder-arm classifier for `cPeel` — mirrors convStep's VPi/VLam/eta/VSigma arms (and the preceding Lift-collapse guard) so binder layers peel flat. Returns a layer record or null.";
      signature = "cPeelBinder : Depth -> Val -> Val -> ({ kind; goals; na; nb; nd; } | null)";
    };
    cPeelArm = api.leaf {
      value = cPeelArm;
      description = "cPeelArm: deep-arm classifier for `cPeel` — peels VNe spines and VMu/VDesc/VBootEq towers onto the machine frontier via the shared `elimGoals` decomposition. Returns a layer record or null.";
      signature = "cPeelArm : Depth -> Val -> Val -> ({ kind; goals; na; nb; nd; } | null)";
    };
    convSp = api.leaf {
      value = convSp;
      description = "convSp: spine equality at binding `depth` — same length plus pairwise `convElim` on each frame; used to compare two neutral-value spines.";
      signature = "convSp : Depth -> Spine -> Spine -> Bool";
    };
    convElim = api.leaf {
      value = convElim;
      description = "convElim: elimination-frame equality at binding `depth` — same tag and recursively `conv` on every carried value; building block of `convSp`.";
      signature = "convElim : Depth -> Elim -> Elim -> Bool";
    };
    normLevel = api.leaf {
      value = normLevel;
      description = "normLevel: normalise a Level expression to canonical form — `levelMax`/`levelSuc` collapsed via the algebraic laws so two equivalent forms compare equal under `convLevel`.";
      signature = "normLevel : Val -> Val";
    };
    convLevel = api.leaf {
      value = convLevel;
      description = "convLevel: definitional equality on Level expressions — `normLevel` both sides, then structural compare; required because `convLevel` is non-trivial under `levelMax` associativity.";
      signature = "convLevel : Val -> Val -> Bool";
    };

  };
}
