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
  inherit (api) mk;
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
  flattenLevel = shift: v:
    if v.tag == "VLevelMax" then
      flattenLevel shift v.lhs ++ flattenLevel shift v.rhs
    else if v.tag == "VLevelSuc" then
      flattenLevel (shift + 1) v.pred
    else if v.tag == "VLevelZero" then
      [{ base = levelZeroBase; inherit shift; }]
    else if v.tag == "VNe" then
      [{ base = mkVarBase v; inherit shift; }]
    else throw "tc: level: unexpected tag '${v.tag}' in flattenLevel";

  # Dedup adjacent-or-scattered same-base summands, keeping the max
  # shift. O(N²) but N is small (bounded by Level expression depth).
  dedupLevel = summands:
    builtins.foldl' (acc: s:
      if builtins.any (y: baseEq y.base s.base) acc
      then map (y:
        if baseEq y.base s.base
        then { base = y.base; shift = if y.shift > s.shift then y.shift else s.shift; }
        else y) acc
      else acc ++ [ s ]
    ) [] summands;

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
        maxVarShift = if varShifts == []
          then 0
          else builtins.foldl' (a: b: if a > b then a else b)
                              (builtins.head varShifts)
                              (builtins.tail varShifts);
        kept = builtins.filter
          (s: !(s.base.kind == "zero"
                && varShifts != []
                && s.shift <= maxVarShift)) merged;
      in if kept == [] then merged else kept;

  normLevel = v:
    let
      flat = flattenLevel 0 v;
      deduped = dedupLevel flat;
      sorted = builtins.sort (a: b: baseCmp a.base b.base < 0) deduped;
    in dropZeroIfDominated sorted;

  summandEq = x: y: x.shift == y.shift && baseEq x.base y.base;

  # Syntactic-equality fast-path: two Level values that are the same
  # Nix value are trivially conv-equal. Skips the normLevel allocations
  # in the common case where both sides come from the same elaboration
  # site (e.g. `kVal` and `ty.level` for a homogeneous-L description).
  # Sound: Nix `==` on values is structural; structural equality of
  # Level values implies their canonical spines agree element-wise.
  convLevel = a: b:
    a == b
    || (let sa = normLevel a; sb = normLevel b; in
        builtins.length sa == builtins.length sb
        && builtins.all (i: summandEq (builtins.elemAt sa i) (builtins.elemAt sb i))
             (builtins.genList (i: i) (builtins.length sa)));

  listConv = d: xs: ys:
    builtins.length xs == builtins.length ys
    && builtins.foldl'
      (ok: i: ok && conv d (builtins.elemAt xs i) (builtins.elemAt ys i))
      true
      (builtins.genList (i: i) (builtins.length xs));

  descRefConv = d: r1: r2:
    (r1.kind or null) == (r2.kind or null)
    && (r1.arity or null) == (r2.arity or null)
    && (r1.indexed or null) == (r2.indexed or null)
    && (r1.constructors or []) == (r2.constructors or [])
    && conv d r1.I r2.I
    && convLevel r1.level r2.level
    && listConv d (r1.params or []) (r2.params or []);

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
       && (body.fn.idx - 1) < (builtins.length closure.env)
    then builtins.elemAt closure.env (body.fn.idx - 1)
    else null;

  # -- Main conversion checker --
  # Returns true if v1 and v2 are definitionally equal at depth d.
  conv = d: v1: v2:
    let t1 = v1.tag; t2 = v2.tag; in

    # Lift idempotent collapse — short-circuit before any structural
    # rule. `Lift l l _ A ≡ A` is the load-bearing backward-compat rule
    # that keeps homogeneous code transparent under the explicit-Lift
    # discipline. The same shape applies to the introducer:
    # `lift l l _ A a ≡ a`. Both reuse `convLevel`'s semilattice
    # quotient (§6.6) — no new conv mechanism. The witness slot is
    # never inspected.
    if t1 == "VLift" && convLevel v1.l v1.m then conv d v1.A v2
    else if t2 == "VLift" && convLevel v2.l v2.m then conv d v1 v2.A
    else if t1 == "VLiftIntro" && convLevel v1.l v1.m then conv d v1.a v2
    else if t2 == "VLiftIntro" && convLevel v2.l v2.m then conv d v1 v2.a

    # §6.1 Structural rules — simple values
    else if t1 == "VUnit" && t2 == "VUnit" then true
    else if t1 == "VTt" && t2 == "VTt" then true
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
    else if t1 == "VFunction" && t2 == "VFunction" then true
    else if t1 == "VAny" && t2 == "VAny" then true
    else if t1 == "VStringLit" && t2 == "VStringLit" then v1.value == v2.value
    else if t1 == "VIntLit" && t2 == "VIntLit" then v1.value == v2.value
    else if t1 == "VFloatLit" && t2 == "VFloatLit" then v1.value == v2.value
    else if t1 == "VAttrsLit" && t2 == "VAttrsLit" then true
    else if t1 == "VPathLit" && t2 == "VPathLit" then true
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
      # `VLevelZero` singleton.
      (if v1.level.tag == "VLevelZero" && v2.level.tag == "VLevelZero"
       then true
       else convLevel v1.level v2.level)
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
        expectedD = E.mkDescDescAppV v1.I v1.level;
      in conv d V.vUnit v2.I
         && conv d V.vTt v2.i
         && conv d expectedD v2.D
    else if t1 == "VMu" && t2 == "VDesc" then
      let
        expectedD = E.mkDescDescAppV v2.I v2.level;
      in conv d v1.I V.vUnit
         && conv d v1.i V.vTt
         && conv d v1.D expectedD
    else if t1 == "VDescCon" && t2 == "VDescCon" then
      # Canonical-identity short-circuit. When both sides carry a
      # `_canonRef = { id; I; L; }` stamp, equality reduces to conv on
      # the stamp itself. Forcing `.D` here would descend through
      # `descDesc ⊤ (suc L)` recursively with no termination at any
      # universe level: Nix structural `==` loops on cyclic VDescCon
      # values, and `tryEval` cannot recover.
      if (v1 ? _canonRef) && (v2 ? _canonRef)
      then
        v1._canonRef.id == v2._canonRef.id
        && conv d v1._canonRef.I v2._canonRef.I
        && conv d v1._canonRef.L v2._canonRef.L
      else if (v1 ? _descRef) && (v2 ? _descRef)
              && descRefConv d v1._descRef v2._descRef
      then true
      else
        let
          classifyD = D:
            let view = E.descView D; in
            if view == null || view.idx != 4 then null
            else
              let pA = E.linearProfile view.A;
                  pB = E.linearProfile view.B;
              in if pA != null && pB == null then { profile = pA; side = "VBootInl"; }
                 else if pB != null && pA == null then { profile = pB; side = "VBootInr"; }
                 else null;
          classify = classifyD v1.D;
          nFields = if classify == null then 0 else builtins.length classify.profile;
          isRetLeaf = p:
            p.tag == "VBootRefl"
            || (p.tag == "VLiftIntro" && p.a.tag == "VBootRefl");
          sameD = D:
            if (D ? _descRef) && (v1.D ? _descRef)
            then descRefConv d D._descRef v1.D._descRef
            else conv d D v1.D;
          collectPairs = p:
            let
              collect = k: node: acc:
                if k == nFields then
                  if node.tag != "VPair" then null
                  else if !(isRetLeaf node.snd) then null
                  else if node.fst.tag != "VDescCon" then null
                  else { heads = acc; tail = node.fst; leaf = node.snd; }
                else if node.tag != "VPair" then null
                else collect (k + 1) node.snd (acc ++ [ node.fst ]);
            in collect 0 p [];
          peel = node:
            if classify == null then null
            else if node.tag != "VDescCon" then null
            else if !(sameD node.D) then null
            else if node.d.tag != classify.side then null
            else
              let inner = collectPairs node.d.val; in
              if inner == null then null
              else inner;
          chain = builtins.genericClosure {
            startSet = [{ key = 0; a = v1; b = v2; pa = peel v1; pb = peel v2; }];
            operator = item:
              if item.pa == null || item.pb == null then []
              else
                let a = item.pa.tail; b = item.pb.tail; in
                [{ key = item.key + 1; inherit a b; pa = peel a; pb = peel b; }];
          };
          n = builtins.length chain - 1;
          base = builtins.elemAt chain n;
          basePeelA = base.pa;
          basePeelB = base.pb;
          layerConv = item:
            let pa = item.pa; pb = item.pb; in
            if pa == null || pb == null then false
            else
              # `peel` already proved both layer descriptions match the
              # same outer D; transitivity gives the per-layer D match.
              # The boot-sum arm types are determined by that D.
              let
                indexOk =
                  if item.a.i.tag == "VTt" && item.b.i.tag == "VTt"
                  then true
                  else conv d item.a.i item.b.i;
                leafOk =
                  if pa.leaf.tag == "VBootRefl" && pb.leaf.tag == "VBootRefl"
                  then true
                  else conv d pa.leaf pb.leaf;
                headsOk =
                  if builtins.length pa.heads == 0 && builtins.length pb.heads == 0
                  then true
                  else listConv d pa.heads pb.heads;
              in indexOk && leafOk && headsOk;
        in
          if classify == null || n == 0 then
            conv d v1.D v2.D && conv d v1.i v2.i && conv d v1.d v2.d
          else if (basePeelA == null) != (basePeelB == null) then false
          else
            builtins.foldl' (ok: i:
              ok && layerConv (builtins.elemAt chain i)
            ) true (builtins.genList (i: i) n)
            && conv d base.a.D base.b.D
            && conv d base.a.i base.b.i
            && conv d base.a.d base.b.d

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

  # -- Spine conversion --
  convSp = d: sp1: sp2:
    let len1 = builtins.length sp1; len2 = builtins.length sp2; in
    if len1 != len2 then false
    else if len1 == 0 then true
    else builtins.foldl' (acc: i:
      acc && convElim d (builtins.elemAt sp1 i) (builtins.elemAt sp2 i)
    ) true (builtins.genList (i: i) len1);

  # -- Elimination frame conversion --
  convElim = d: e1: e2:
    let t1 = e1.tag; t2 = e2.tag; in
    if t1 != t2 then false
    else if t1 == "EApp" then conv d e1.arg e2.arg
    else if t1 == "EFst" then true
    else if t1 == "ESnd" then true
    else if t1 == "EBootSumElim" then
      conv d e1.left e2.left && conv d e1.right e2.right
      && conv d e1.motive e2.motive && conv d e1.onLeft e2.onLeft
      && conv d e1.onRight e2.onRight
    else if t1 == "EBootJ" then
      conv d e1.type e2.type && conv d e1.lhs e2.lhs
      && conv d e1.motive e2.motive && conv d e1.base e2.base
      && conv d e1.rhs e2.rhs
    else if t1 == "EStrEq" then conv d e1.arg e2.arg
    else if t1 == "EDescInd" then
      conv d e1.D e2.D && conv d e1.motive e2.motive
      && conv d e1.step e2.step && conv d e1.i e2.i
    # EInterpD / EAllD / EEverywhereD spine frames — stuck `interpD` /
    # `allD` / `everywhereD` applications on a neutral D scrutinee.
    # Compare slots field-wise (D is the spine head, compared by
    # `convSp`). Levels delegate to `conv`'s VLevel routing.
    else if t1 == "EInterpD" then
      conv d e1.level e2.level && conv d e1.I e2.I
      && conv d e1.X e2.X && conv d e1.i e2.i
    else if t1 == "EAllD" then
      conv d e1.level e2.level && conv d e1.I e2.I
      && conv d e1.K e2.K && conv d e1.X e2.X
      && conv d e1.M e2.M && conv d e1.i e2.i && conv d e1.d e2.d
    else if t1 == "EEverywhereD" then
      conv d e1.level e2.level && conv d e1.I e2.I
      && conv d e1.K e2.K && conv d e1.X e2.X
      && conv d e1.M e2.M && conv d e1.ih e2.ih
      && conv d e1.i e2.i && conv d e1.d e2.d
    # ELiftElim spine frame — compare l, m, A. The `eq` slot is not
    # compared, mirroring the witness-irrelevance of the type-former.
    else if t1 == "ELiftElim" then
      convLevel e1.l e2.l && convLevel e1.m e2.m && conv d e1.A e2.A
    # ESquashElim spine frame — structural compare of motive shape (A,B)
    # and case function. Two stuck `recTrunc` applications agree iff they
    # agree on metadata; payload irrelevance lives at the value layer
    # (VSquashIntro/VNe rules above), not on the spine frame itself.
    else if t1 == "ESquashElim" then
      conv d e1.A e2.A && conv d e1.B e2.B && conv d e1.f e2.f
    else false;

in mk {
  doc = ''
    # fx.tc.conv — Conversion (Definitional Equality)

    Checks whether two values are definitionally equal at a given
    binding depth. Purely structural — no type information used, no
    eta expansion. Pure function — part of the TCB.

    Spec reference: kernel-spec.md §6.

    ## Core Functions

    - `conv : Depth → Val → Val → Bool` — check definitional equality.
    - `convSp : Depth → Spine → Spine → Bool` — check spine equality
      (same length, pairwise `convElim`).
    - `convElim : Depth → Elim → Elim → Bool` — check elimination frame
      equality (same tag, recursively conv on carried values).

    ## Conversion Rules

    - §6.1 **Structural**: same-constructor values with matching fields.
      Universe levels compared by `==`. Primitive literals by value.
    - §6.2 **Binding forms**: Pi, Lam, Sigma compared under a fresh
      variable at depth d (instantiate both closures, compare at d+1).
    - §6.3 **Compound values**: recursive on all components.
    - §6.4 **Neutrals**: same head level and convertible spines.
    - §6.5 **Catch-all**: different constructors → false.

    ## Trampolining

    Deep ordinary data is represented by generated `VDescCon` values.
    Conversion stays structural except for explicitly documented
    eta/unfolding rules.

    ## No Eta

    `conv` does not perform eta expansion: a neutral `f` and
    `λx. f(x)` are **not** definitionally equal. Cumulativity
    (`U(i) ≤ U(j)`) is handled in check.nix, not here.
  '';
  value = { inherit conv convSp convElim normLevel convLevel; };
  tests = let
    inherit (V) vPi vLam vSigma vPair
      vUnit vTt vBootSum vBootInl vBootInr vBootEq vBootRefl vU vNe
      vSquash vSquashIntro eSquashElim
      mkClosure eApp eFst eSnd eBootSumElim eBootJ;
    T = fx.tc.term;
    H = fx.tc.hoas;
    elabVal = h: E.eval [] (H.elab h);
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
    recRetVal = elabVal (H.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt));
    recNatZeroVal = elabVal (H.recI H.nat 0 H.zero (H.retI H.nat 0 H.zero));
    recNatSuccVal = elabVal (H.recI H.nat 0 (H.succ H.zero) (H.retI H.nat 0 H.zero));
    piNatVal = elabVal (H.piI H.unit 0 H.nat (unitFn H.nat) (H.retI H.unit 0 H.tt));
    piUnitVal = elabVal (H.piI H.unit 0 H.unit (unitFn H.unit) (H.retI H.unit 0 H.tt));
    piNatRecVal = elabVal (H.piI H.unit 0 H.nat (unitFn H.nat)
      (H.recI H.unit 0 H.tt (H.retI H.unit 0 H.tt)));
    piUOneVal = elabVal (H.piI H.unit 1 (H.u 0) (unitFn (H.u 0)) (H.retI H.unit 1 H.tt));
  in {
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
        (vPi "x" vUnit (mkClosure [] T.mkUnit))
        (vPi "y" vUnit (mkClosure [] T.mkUnit));
      expected = true;
    };
    "conv-pi-diff-domain" = {
      expr = conv 0
        (vPi "x" V.vString (mkClosure [] T.mkString))
        (vPi "x" vUnit (mkClosure [] T.mkString));
      expected = false;
    };
    "conv-pi-diff-codomain" = {
      expr = conv 0
        (vPi "x" vUnit (mkClosure [] T.mkUnit))
        (vPi "x" vUnit (mkClosure [] T.mkString));
      expected = false;
    };
    "conv-pi-dependent" = {
      # Π(x:Unit).x ≡ Π(y:Unit).y — both bodies reference the bound var
      expr = conv 0
        (vPi "x" vUnit (mkClosure [] (T.mkVar 0)))
        (vPi "y" vUnit (mkClosure [] (T.mkVar 0)));
      expected = true;
    };

    # Binding forms with different dependent bodies
    "conv-pi-dep-diff-body" = {
      # Π(x:Unit).x vs Π(x:Unit).Unit — different dependent codomains
      expr = conv 0
        (vPi "x" vUnit (mkClosure [] (T.mkVar 0)))
        (vPi "x" vUnit (mkClosure [] T.mkUnit));
      expected = false;
    };
    "conv-sigma-dep-diff-body" = {
      # Σ(x:Unit).x vs Σ(x:Unit).Unit — different dependent second components
      expr = conv 0
        (vSigma "x" vUnit (mkClosure [] (T.mkVar 0)))
        (vSigma "x" vUnit (mkClosure [] T.mkUnit));
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
        (vLam "x" vUnit (mkClosure [] (T.mkVar 0)))
        (vLam "y" vUnit (mkClosure [] (T.mkVar 0)));
      expected = true;
    };
    "conv-lam-diff-body" = {
      expr = conv 0
        (vLam "x" vUnit (mkClosure [] T.mkTt))
        (vLam "x" vUnit (mkClosure [] T.mkUnit));
      expected = false;
    };
    "conv-sigma" = {
      expr = conv 0
        (vSigma "x" vUnit (mkClosure [] T.mkUnit))
        (vSigma "y" vUnit (mkClosure [] T.mkUnit));
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
    "conv-ne-same" = { expr = conv 1 (vNe 0 []) (vNe 0 []); expected = true; };
    "conv-ne-diff-level" = { expr = conv 2 (vNe 0 []) (vNe 1 []); expected = false; };
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
      expr = conv 1 (vNe 0 [ (eApp vTt) ]) (vNe 0 []);
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
      expr = let
        lhs = V.vDesc V.vLevelZero V.vUnit;
        expectedD = E.mkDescDescAppV V.vUnit V.vLevelZero;
        rhs = V.vMu V.vUnit expectedD V.vTt;
      in conv 0 lhs rhs;
      expected = true;
    };
    "conv-mu-desc-unfold-trivial" = {
      # Symmetric direction: μ ⊤ (descDesc ⊤ 0) tt ≡ Desc ⊤ 0.
      expr = let
        expectedD = E.mkDescDescAppV V.vUnit V.vLevelZero;
        lhs = V.vMu V.vUnit expectedD V.vTt;
        rhs = V.vDesc V.vLevelZero V.vUnit;
      in conv 0 lhs rhs;
      expected = true;
    };
    "conv-desc-mu-unfold-generated-nat-k0" = {
      # Desc Nat 0 ≡ μ ⊤ (descDesc Nat 0) tt — non-⊤ I slice.
      expr = let
        lhs = V.vDesc V.vLevelZero natTyVal;
        expectedD = E.mkDescDescAppV natTyVal V.vLevelZero;
        rhs = V.vMu V.vUnit expectedD V.vTt;
      in conv 0 lhs rhs;
      expected = true;
    };
    "conv-desc-mu-unfold-suc-k" = {
      # Desc ⊤ 1 ≡ μ ⊤ (descDesc ⊤ 1) tt — non-zero level.
      expr = let
        levelOne = V.vLevelSuc V.vLevelZero;
        lhs = V.vDesc levelOne V.vUnit;
        expectedD = E.mkDescDescAppV V.vUnit levelOne;
        rhs = V.vMu V.vUnit expectedD V.vTt;
      in conv 0 lhs rhs;
      expected = true;
    };
    "conv-desc-mu-mismatch-encoded-I-rejected" = {
      # Desc Nat 0 ≢ μ ⊤ (descDesc ⊤ 0) tt — v2.D encodes I=⊤ but v1
      # demands I=Nat. Structural conv on the descDesc tree distinguishes.
      expr = let
        lhs = V.vDesc V.vLevelZero natTyVal;
        expectedD = E.mkDescDescAppV V.vUnit V.vLevelZero;
        rhs = V.vMu V.vUnit expectedD V.vTt;
      in conv 0 lhs rhs;
      expected = false;
    };
    "conv-desc-mu-mismatch-mu-I-rejected" = {
      # μ Nat (descDesc ⊤ 0) zero ≢ Desc ⊤ 0 — v1's outer I is Nat,
      # not ⊤, so the unfolding's ⊤-slot check fails.
      expr = let
        expectedD = E.mkDescDescAppV V.vUnit V.vLevelZero;
        lhs = V.vMu natTyVal expectedD zeroVal;
        rhs = V.vDesc V.vLevelZero V.vUnit;
      in conv 0 lhs rhs;
      expected = false;
    };

    # Lift primitive — idempotent collapse, structural with
    # witness-irrelevance, eta on stuck neutrals, ELiftElim spine.
    "conv-lift-idempotent-collapse-vs-A" = {
      # Lift l l _ A ≡ A — load-bearing backward-compat rule.
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
      expr = let
        x = V.freshVar 0;
        loweredX = E.vLiftElimF V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl vUnit x;
      in conv 1
        (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl vUnit loweredX)
        x;
      expected = true;
    };
    "conv-lift-eta-neutral-vs-intro" = {
      # Symmetric direction.
      expr = let
        x = V.freshVar 0;
        loweredX = E.vLiftElimF V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl vUnit x;
      in conv 1
        x
        (V.vLiftIntro V.vLevelZero (V.vLevelSuc V.vLevelZero)
          V.vBootRefl vUnit loweredX);
      expected = true;
    };
    "conv-ne-lift-elim" = {
      # Two stuck `lower`s with matching params convert.
      expr = conv 1
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   V.vBootRefl vUnit) ])
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   V.vBootRefl vUnit) ]);
      expected = true;
    };
    "conv-ne-lift-elim-diff-A" = {
      expr = conv 1
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   V.vBootRefl vUnit) ])
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   V.vBootRefl V.vString) ]);
      expected = false;
    };
    "conv-ne-lift-elim-witness-irrelevance" = {
      # The `eq` slot is not compared in the spine frame.
      expr = conv 1
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   V.vBootRefl vUnit) ])
        (vNe 0 [ (V.eLiftElim V.vLevelZero (V.vLevelSuc V.vLevelZero)
                   vTt vUnit) ]);
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
      expr = let
        f = vLam "_" vUnit (mkClosure [] T.mkTt);
      in conv 1
        (vNe 0 [ (eSquashElim vUnit vUnit f) ])
        (vNe 0 [ (eSquashElim vUnit vUnit f) ]);
      expected = true;
    };
    "conv-ne-squash-elim-diff-A" = {
      # Distinct motive types refuse conv on the spine frame.
      expr = let
        f = vLam "_" vUnit (mkClosure [] T.mkTt);
      in conv 1
        (vNe 0 [ (eSquashElim vUnit vUnit f) ])
        (vNe 0 [ (eSquashElim V.vString vUnit f) ]);
      expected = false;
    };

    # Stress tests — generated ordinary data
    "conv-generated-nat-5000" = {
      expr = let
        deep = E.eval [] (H.elab (H.natLit 5000));
      in conv 0 deep deep;
      expected = true;
    };
    "conv-generated-list-5000" = {
      expr = let
        deep = E.eval [] (H.elab (builtins.foldl' (acc: _:
          H.cons H.nat H.zero acc
        ) (H.nil H.nat) (builtins.genList (x: x) 5000)));
      in conv 0 deep deep;
      expected = true;
    };

    # `_canonRef` short-circuit at VDescCon × VDescCon. Equality reduces
    # to conv on the carried `(id, I, L)`; `.D` is never forced.
    "conv-descDescApp-tag-self" = {
      expr =
        let v = V.vDescConTagged vTt vTt V.vBootRefl
                  { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; };
        in conv 0 v v;
      expected = true;
    };
    "conv-descDescApp-tag-distinct-id-rejects" = {
      expr =
        let v1 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "alpha"; I = V.vUnit; L = V.vLevelZero; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "beta";  I = V.vUnit; L = V.vLevelZero; };
        in conv 0 v1 v2;
      expected = false;
    };
    "conv-descDescApp-tag-distinct-I-rejects" = {
      expr =
        let v1 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "descDesc"; I = natTyVal;  L = V.vLevelZero; };
        in conv 0 v1 v2;
      expected = false;
    };
    "conv-descDescApp-tag-distinct-L-rejects" = {
      expr =
        let v1 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; };
            v2 = V.vDescConTagged vTt vTt V.vBootRefl
                   { id = "descDesc"; I = V.vUnit; L = V.vLevelSuc V.vLevelZero; };
        in conv 0 v1 v2;
      expected = false;
    };
    "conv-descDescApp-cyclic-D-self" = {
      # The `.D` slot points back at the value itself; the tag check
      # decides equality without descending. A no-tag value with the
      # same shape would loop on the structural fall-through.
      expr =
        let cyclic = let v = {
              tag = "VDescCon";
              D = v;
              i = vTt;
              d = vTt;
              _canonRef = { id = "descDesc"; I = V.vUnit; L = V.vLevelZero; };
            }; in v;
        in conv 0 cyclic cyclic;
      expected = true;
    };
    "conv-descDescApp-cyclic-D-mismatch-rejects" = {
      expr =
        let mk = idStr: let v = {
              tag = "VDescCon";
              D = v;
              i = vTt;
              d = vTt;
              _canonRef = { id = idStr; I = V.vUnit; L = V.vLevelZero; };
            }; in v;
        in conv 0 (mk "alpha") (mk "beta");
      expected = false;
    };
  };
}
