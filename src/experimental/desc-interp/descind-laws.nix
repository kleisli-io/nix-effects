# Kernel-level laws derived via `descInd kontQueueApp` at the indexed
# slice. Recursive children remain `recI U² k (X, M)` /
# `recI U² k (M, A)`, so a `descInd kontQueueApp` consumer gets a
# per-recursive-position IH at the right index.
#
# `qAppKernel` is the kernel-resident transposition of
# `trampoline.nix:qApp` — same algorithm at the description layer,
# every step body discharged by the kernel checker. At the Identity
# branch it returns `λx. pureCon X x` (Identity collapses to pure);
# at the Leaf branch `λx. fn x` (the leaf's continuation is the
# computation); at the Node branch
# `λx. bind (ih_l x) (λy. ih_r y)` (the seam M's intermediate result
# threads through `bind`, cashing in BOTH indexed IHs at `(X, M)` and
# `(M, A)`). Trampoline-side `qApp` and kernel-side `qAppKernel` produce
# the same `μ freeFxApp` values; the kernel version exists so we can
# write laws inside the kernel rather than only observe them.
#
# Mathematical scaffold per branch. `kontQueue`'s three summands carry
# existential index witnesses reified via `descArgAt(X)` / `descArgAt(A)`
# / `descArgAt(M)`. The retI tail of each summand has its `j` slot at
# the schematic index `(X', X')` (Identity) / `(X', A')` (Leaf, Node) —
# `interpD`'s descRet rule reduces this to `Lift 1 1 _ (Eq U² j i)`
# where `i` is the descInd-supplied index. The step body's J-transport
# on this Eq witness propagates the schematic-index information through
# to the motive's `fst_(i) → μ freeFx (snd_(i))` codomain.
#
# `qAppIdLaw` is the verification gate. Stated as
# `Π(X:U). Π(x:X). bootEq (μ freeFx X) (qAppKernel (X,X) (qIdentity X) x)
#                                (pureCon Eff Resp X x)`.
# Proof is `λX. λx. bootRefl`. Typechecks because
# the kernel's conv sees `qAppKernel (X,X) (qIdentity X) x` β-reducing
# through descInd → Identity step → bootJ on refl → liftAt → lowerAt → β
# down to `pureCon Eff Resp X x`. Demonstrates the indexed IH is
# operationally usable: the lemma's well-typedness depends essentially
# on `descInd kontQueueApp` (an unindexed `descInd` cannot project
# `fst_(i)` and `snd_(i)` for the motive's codomain).
#
# Refs: Chapman/Dagand/McBride/Morris (ICFP'10) §6 indexed descriptions;
# Atkey (LICS'18) §3 QTT-erasure (background — the seam witness here is
# intensional, not quantity-0); CDFM 2010 §5 Gentle Art of Levitation.
{ fx, lib, api, ... }:
let
  H = fx.tc.hoas;
  HI = fx.tc.hoas._internal;
  HII = fx.tc.hoas._internal._indexed;
  G = fx.tc.generic.desc;
  D = fx.experimental.desc-interp.desc;
  Elab = fx.tc.elaborate;
  E = fx.tc.eval;
  C = fx.tc.conv;
  Q = fx.tc.quote;
  CH = fx.tc.check;

  inherit (D) freeFxApp freeFx kontQueue kontQueueApp pureCon impureCon
    qIdentity qLeaf qNode;

  # Index type and convenience builder. Mirror of `desc.nix:28-29`.
  u2 = H.sigma "_" (H.u 0) (_: H.u 0);
  iLev1 = H.levelSuc H.levelZero;
  pairXY = X: Y: H.ann (H.pair X Y) u2;

  # `k = 1` matches `kontQueue`'s binding universe. `descLevelTm` is its
  # HOAS Level form, used to thread the universe through `LiftAt` /
  # `lowerAt` Tm sites. `motiveLevelTm` is also `U(1)`: `freeFx`
  # contains a queue field indexed over `U²`, so its μ-carrier lives at
  # U(1).
  k = 1;
  descLevelTm = H.levelSuc H.levelZero;
  motiveLevelTm = H.levelSuc H.levelZero;

  # Per-summand descriptions — re-derived locally (sibling import would
  # require a default.nix). These match `desc.nix:167-196` verbatim.
  qIdentitySummand =
    HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (X:
      HII.retIAtI iLev1 u2 k (pairXY X X));

  qLeafSummand = Eff: Resp:
    HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (X:
      HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (A:
        HII.descArgAtAtI iLev1 u2 1 k
          (H.forall "_" X (_: H.mu (freeFxApp Eff Resp A) H.tt))
          (_fn:
            HII.retIAtI iLev1 u2 k (pairXY X A))));

  qNodeSummand = Eff: Resp:
    HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (X:
      HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (M:
        HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (A:
          HII.recIAtI iLev1 u2 k (pairXY X M)
            (HII.recIAtI iLev1 u2 k (pairXY M A)
              (HII.retIAtI iLev1 u2 k (pairXY X A))))));

  qLeafOrNodeSummand = Eff: Resp:
    HII.plusIAtI iLev1 u2 k (qLeafSummand Eff Resp) (qNodeSummand Eff Resp);

  # The kontQueue description itself, re-derived for clarity at this
  # site. Note: descInd's D-slot accepts the raw description (not the
  # canon-app wrapper) — `qIdentity` / `qLeaf` / `qNode` build their
  # descCons against `kontQueue Eff Resp`, so the schemata align.
  #
  # The trusted annotation gives the encoded plus-chain its primitive
  # `Desc^1 U²` ascription without re-checking the recursive body.
  kontQueueRaw = Eff: Resp:
    H.annTrusted
      (HII.plusIAtI iLev1 u2 k qIdentitySummand (qLeafOrNodeSummand Eff Resp))
      (HII.descIAtAtI iLev1 descLevelTm u2);

  # `muFam` — the recursive-position family. `descInd`'s evaluator
  # threads this as the X-parameter of `interpD` / `allD`.
  muFam = Eff: Resp:
    H.lam "_j" u2 (j: HII.muIAtI iLev1 u2 (kontQueueApp Eff Resp) j);

  # ── motive ────────────────────────────────────────────────────────
  # `Pp` — the lifted motive for `descInd`. `freeFx` contains a queue
  # field indexed over `U²`, so `Π(x:fst_(i)). μ freeFx (snd_(i)) tt`
  # lives at U(1). `LiftAt 1 1` keeps the descInd motive shape aligned
  # with the generic eliminator path while reducing definitionally to
  # the underlying function type.
  #
  # The codomain is inlined rather than factored through a separate `P`:
  # `H.app (P Eff Resp) iVar` would require inferring a bare HOAS
  # lambda's type (lambdas are check-only against Π). Inlining keeps the
  # motive body in CHECK mode end-to-end. The xVar binder remains —
  # the motive's signature requires Π(i) → Π(scrut) → U, even though
  # qApp's type doesn't depend on the queue.
  Pp = Eff: Resp:
    H.lam "i" u2 (iVar:
      H.lam "_x" (HII.muIAtI iLev1 u2 (kontQueueApp Eff Resp) iVar) (_:
        HII.LiftAt motiveLevelTm descLevelTm
          (H.forall "_x" (H.fst_ iVar) (_:
            H.mu (freeFxApp Eff Resp (H.snd_ iVar)) H.tt))));

  # The lifted codomain type at `iVar` — convenience for step bodies.
  PpCodomAt = Eff: Resp: iVar:
    HII.LiftAt motiveLevelTm descLevelTm
      (H.forall "_x" (H.fst_ iVar) (_:
        H.mu (freeFxApp Eff Resp (H.snd_ iVar)) H.tt));

  # The underlying U(1) function type at `iVar` (before lifting). The
  # step bodies build values of this type, then wrap with `liftAt 1 1`
  # to land in `PpCodomAt`.
  funAt = Eff: Resp: iVar:
    H.forall "_x" (H.fst_ iVar) (_:
      H.mu (freeFxApp Eff Resp (H.snd_ iVar)) H.tt);

  # ── step bodies ───────────────────────────────────────────────────
  # Each step receives the schematic `iArg : U²` and the summand's
  # interpD payload `d`. The payload's trailing `Eq U² j_schema iArg` —
  # wrapped by interpD's descRet rule at the index universe — here
  # `Lift 1 1 _ (Eq …)`, which collapses to the raw Eq — and is fed
  # through `lowerAt 1 1` before `bootJ`. J's motive carries the
  # `iArg`-parameterised target type; J's base case lives at the
  # schematic index where conv-reduction sees concrete pair components.

  # Identity step.
  #   d_id : Σ(X':U). Lift 1 1 _ (Eq U² (X', X') iArg)
  #   ih_id : Unit
  #   Goal: PpCodomAt Eff Resp iArg
  #       ≡ LiftAt 1 1 (Π x:fst_(iArg). μ freeFx (snd_(iArg)) tt)
  #
  # J on the lowered Eq witness from (X', X') to iArg. Base case at
  # j = (X', X') reduces fst_ / snd_ to X' by Σ-β, so the body's type
  # collapses to Π x:X'. μ freeFx X' tt — inhabited by pureCon.
  identityStep = Eff: Resp: iArg: d_id:
    let
      Xv = H.fst_ d_id;
      eqLifted = H.snd_ d_id;
      eqRaw = HII.lowerAt iLev1 descLevelTm
        (HI.bootEq u2 (pairXY Xv Xv) iArg)
        eqLifted;
      # `boot-j` checker (infer.nix:boot-j) demands the motive's codomain
      # be a type — `funAt Eff Resp jVar` is `Π x:fst_(jVar). μ freeFx …`
      # at U(1). `liftAt 1 1` keeps the value in the Pp carrier.
      jMotive =
        H.lam "j" u2 (jVar:
          H.lam "_eq" (HI.bootEq u2 (pairXY Xv Xv) jVar) (_:
            HII.LiftAt motiveLevelTm descLevelTm (funAt Eff Resp jVar)));
      jBase =
        HII.liftAt motiveLevelTm descLevelTm
          (funAt Eff Resp (pairXY Xv Xv))
          (H.lam "x" Xv (xv: pureCon Eff Resp Xv xv));
    in
    HI.bootJ u2 (pairXY Xv Xv) jMotive jBase iArg eqRaw;

  # Leaf step.
  #   d_lf : Σ(X':U). Σ(A':U). Σ(fn:X'→μ freeFx A' tt). Lift 1 1 _ (Eq U² (X',A') iArg)
  #   ih_lf : Unit
  #   Goal: PpCodomAt Eff Resp iArg
  #
  # J base at j = (X', A'): Π x:X'. μ freeFx A' tt — inhabited by `app fn x`.
  leafStep = Eff: Resp: iArg: d_lf:
    let
      Xv = H.fst_ d_lf;
      d_lf_1 = H.snd_ d_lf;
      Av = H.fst_ d_lf_1;
      d_lf_2 = H.snd_ d_lf_1;
      fn = H.fst_ d_lf_2;
      eqLifted = H.snd_ d_lf_2;
      eqRaw = HII.lowerAt iLev1 descLevelTm
        (HI.bootEq u2 (pairXY Xv Av) iArg)
        eqLifted;
      jMotive =
        H.lam "j" u2 (jVar:
          H.lam "_eq" (HI.bootEq u2 (pairXY Xv Av) jVar) (_:
            HII.LiftAt motiveLevelTm descLevelTm (funAt Eff Resp jVar)));
      jBase =
        HII.liftAt motiveLevelTm descLevelTm
          (funAt Eff Resp (pairXY Xv Av))
          (H.lam "x" Xv (xv: H.app fn xv));
    in
    HI.bootJ u2 (pairXY Xv Av) jMotive jBase iArg eqRaw;

  qLeafKernel = Eff: Resp: X: A: fn:
    let i = pairXY X A; in
    H.descCon (kontQueueRaw Eff Resp) i
      (HI.bootInr
        (interpIdentityAt Eff Resp i)
        (interpLeafOrNodeAt Eff Resp i)
        (HI.bootInl
          (interpLeafAt Eff Resp i)
          (interpNodeAt Eff Resp i)
          (H.pair X (H.pair A (H.pair fn HI.bootRefl)))));

  qNodeKernel = Eff: Resp: X: M: A: l: r:
    let i = pairXY X A; in
    H.descCon (kontQueueRaw Eff Resp) i
      (HI.bootInr
        (interpIdentityAt Eff Resp i)
        (interpLeafOrNodeAt Eff Resp i)
        (HI.bootInr
          (interpLeafAt Eff Resp i)
          (interpNodeAt Eff Resp i)
          (H.pair X (H.pair M (H.pair A
            (H.pair l (H.pair r HI.bootRefl)))))));

  freeMuFam = Eff: Resp: A:
    H.lam "_j" H.unit (_: H.mu (freeFxApp Eff Resp A) H.tt);

  freeMotive = Eff: Resp: A: B:
    H.lam "_i" H.unit (_:
      H.lam "_m" (H.mu (freeFxApp Eff Resp A) H.tt) (_:
        H.mu (freeFxApp Eff Resp B) H.tt));

  freePureSummand = A:
    HII.descArgAt H.unit 0 k A (_:
      H.retI H.unit k H.tt);

  freeImpureSummand = Eff: Resp: A:
    HII.descArgAt H.unit 0 k Eff (op:
      HII.descArgAt H.unit k k
        (HII.muIAtI iLev1 u2 (kontQueueApp Eff Resp) (pairXY (H.app Resp op) A))
        (_: H.retI H.unit k H.tt));

  bindKernel = Eff: Resp: A: B: m: f:
    let
      resultTy = H.mu (freeFxApp Eff Resp B) H.tt;
      motive = freeMotive Eff Resp A B;
      muFamA = freeMuFam Eff Resp A;
      step = H.lam "_i" H.unit (_:
        H.lam "d" (H.interpD k H.unit (freeFx Eff Resp A) muFamA H.tt) (d:
          H.lam "_ih" (H.allD k H.unit (freeFx Eff Resp A) descLevelTm
            muFamA motive H.tt d) (_:
            let
              pC = H.interpD k H.unit (freePureSummand A) muFamA H.tt;
              iC = H.interpD k H.unit (freeImpureSummand Eff Resp A) muFamA H.tt;
              branchMotive = H.lam "_s" (HI.bootSum pC iC) (_: resultTy);
              onPure = H.lam "d_pure" pC (d_pure:
                let
                  xLifted = H.fst_ d_pure;
                  x = HII.lowerAt H.levelZero descLevelTm A xLifted;
                in f x);
              onImpure = H.lam "d_imp" iC (d_imp:
                let
                  opLifted = H.fst_ d_imp;
                  op = HII.lowerAt H.levelZero descLevelTm Eff opLifted;
                  q = H.fst_ (H.snd_ d_imp);
                  respTy = H.app Resp op;
                  leaf = qLeafKernel Eff Resp A B (H.lam "y" A (y: f y));
                  newQ = qNodeKernel Eff Resp respTy A B q leaf;
                in impureCon Eff Resp B op newQ);
            in
              HI.bootSumElim pC iC branchMotive onPure onImpure d)));
    in
      H.descInd (freeFx Eff Resp A) motive step H.tt m;

  # Node step.
  #   d_nd : Σ(X':U). Σ(M':U). Σ(A':U). Σ(_:μ kontQueue (X',M')).
  #          Σ(_:μ kontQueue (M',A')). Lift 1 1 _ (Eq U² (X',A') iArg)
  #   ih_nd : Σ ih_l: Lift 1 1 (Π x:X'. μ freeFx M' tt).
  #           Σ ih_r: Lift 1 1 (Π x:M'. μ freeFx A' tt). Unit
  #   Goal: PpCodomAt Eff Resp iArg
  #
  # Cashes in BOTH indexed IHs at their respective indices (X', M') and
  # (M', A'). J base at j = (X', A'): Π x:X'. μ freeFx A' tt. The body
  # `bind (ih_l x) (λy. ih_r y)` is the seam-threading composition the
  # indexing is precisely there to support — without `kontQueue`'s
  # indexing the IHs would type at (X', X') (Identity slice) and would
  # not compose through `M'`.
  nodeStep = Eff: Resp: iArg: d_nd: ih_nd:
    let
      Xv = H.fst_ d_nd;
      d_nd_1 = H.snd_ d_nd;
      Mv = H.fst_ d_nd_1;
      d_nd_2 = H.snd_ d_nd_1;
      Av = H.fst_ d_nd_2;
      d_nd_3 = H.snd_ d_nd_2;
      _l = H.fst_ d_nd_3;
      d_nd_4 = H.snd_ d_nd_3;
      _r = H.fst_ d_nd_4;
      eqLifted = H.snd_ d_nd_4;
      eqRaw = HII.lowerAt iLev1 descLevelTm
        (HI.bootEq u2 (pairXY Xv Av) iArg)
        eqLifted;
      # `allD` at `(recI U² k (X,M); recI U² k (M,A); retI U² k (X,A))`
      # is `Σ(_:Pp (X,M) l). Σ(_:Pp (M,A) r). Unit` — the two recI
      # positions inhabit their Pp-applied types (already lifted).
      ih_l_lifted = H.fst_ ih_nd;
      ih_r_lifted = H.fst_ (H.snd_ ih_nd);
      ih_l = HII.lowerAt motiveLevelTm descLevelTm
        (funAt Eff Resp (pairXY Xv Mv))
        ih_l_lifted;
      ih_r = HII.lowerAt motiveLevelTm descLevelTm
        (funAt Eff Resp (pairXY Mv Av))
        ih_r_lifted;
      jMotive =
        H.lam "j" u2 (jVar:
          H.lam "_eq" (HI.bootEq u2 (pairXY Xv Av) jVar) (_:
            HII.LiftAt motiveLevelTm descLevelTm (funAt Eff Resp jVar)));
      jBase =
        HII.liftAt motiveLevelTm descLevelTm
          (funAt Eff Resp (pairXY Xv Av))
          (H.lam "x" Xv (xv:
            bindKernel Eff Resp Mv Av (H.app ih_l xv) (y: H.app ih_r y)));
    in
    HI.bootJ u2 (pairXY Xv Av) jMotive jBase iArg eqRaw;

  # ── step dispatcher ───────────────────────────────────────────────
  # The kontQueue's interpD at iArg is
  # `bootSum L (bootSum L_lf L_nd)` where
  #   L     = interpD 1 u2 qIdentitySummand muFam iArg
  #   L_lf  = interpD 1 u2 qLeafSummand muFam iArg
  #   L_nd  = interpD 1 u2 qNodeSummand muFam iArg
  # We dispatch via `bootSumElim` on the outer plus, then nested on the
  # inner plus for Leaf vs Node.
  interpIdentityAt = Eff: Resp: iArg:
    H.interpD k u2 qIdentitySummand (muFam Eff Resp) iArg;
  interpLeafAt = Eff: Resp: iArg:
    H.interpD k u2 (qLeafSummand Eff Resp) (muFam Eff Resp) iArg;
  interpNodeAt = Eff: Resp: iArg:
    H.interpD k u2 (qNodeSummand Eff Resp) (muFam Eff Resp) iArg;
  interpLeafOrNodeAt = Eff: Resp: iArg:
    H.interpD k u2 (qLeafOrNodeSummand Eff Resp) (muFam Eff Resp) iArg;

  # `allD` types for each summand. Identity / Leaf are retI-tailed
  # without recursive positions → `allD ≡ Lift 0 1 _ Unit`, which
  # evaluates to Unit.
  # Node has two recursive positions; `allD` projects out the per-recI
  # IH pair followed by a trailing Unit.
  allIdentityAt = Eff: Resp: iArg: d:
    H.allD k u2 qIdentitySummand descLevelTm
      (muFam Eff Resp)
      (Pp Eff Resp)
      iArg
      d;
  allLeafAt = Eff: Resp: iArg: d:
    H.allD k u2 (qLeafSummand Eff Resp) descLevelTm
      (muFam Eff Resp)
      (Pp Eff Resp)
      iArg
      d;
  allNodeAt = Eff: Resp: iArg: d:
    H.allD k u2 (qNodeSummand Eff Resp) descLevelTm
      (muFam Eff Resp)
      (Pp Eff Resp)
      iArg
      d;
  allLeafOrNodeAt = Eff: Resp: iArg: d:
    H.allD k u2 (qLeafOrNodeSummand Eff Resp) descLevelTm
      (muFam Eff Resp)
      (Pp Eff Resp)
      iArg
      d;

  # Inner dispatch: Leaf vs Node, with the all-d dispatching in parallel
  # via the same plus-on-bootSum case rule.
  innerStep = Eff: Resp: iArg: d_lon:
    let
      L_lf = interpLeafAt Eff Resp iArg;
      L_nd = interpNodeAt Eff Resp iArg;
      # The bootSumElim's motive must accept any `s : bootSum L_lf L_nd`
      # and return the per-summand goal type. Both branches inhabit
      # `PpCodomAt Eff Resp iArg → ...`, but the IH binder is summand-
      # specific (Unit for Leaf, Σ-pair for Node). We thread the ih as
      # a Π in the motive: `s → allD-at-summand s → PpCodomAt`.
      sumMot = H.lam "s" (HI.bootSum L_lf L_nd) (s:
        H.forall "_ih" (allLeafOrNodeAt Eff Resp iArg s) (_:
          PpCodomAt Eff Resp iArg));
      onLeaf = H.lam "d_lf" L_lf (d_lf:
        H.lam "_ih" (allLeafAt Eff Resp iArg d_lf) (_:
          leafStep Eff Resp iArg d_lf));
      onNode = H.lam "d_nd" L_nd (d_nd:
        H.lam "ih_nd" (allNodeAt Eff Resp iArg d_nd) (ih_nd:
          nodeStep Eff Resp iArg d_nd ih_nd));
    in
    HI.bootSumElim L_lf L_nd sumMot onLeaf onNode d_lon;

  step = Eff: Resp:
    H.lam "iArg" u2 (iArg:
      H.lam "d"
        (H.interpD k u2 (kontQueueRaw Eff Resp)
          (muFam Eff Resp)
          iArg)
        (d:
          H.lam "ih"
            (H.allD k u2 (kontQueueRaw Eff Resp)
              descLevelTm
              (muFam Eff Resp)
              (Pp Eff Resp)
              iArg
              d)
            (ih:
              let
                L_id = interpIdentityAt Eff Resp iArg;
                L_lon = interpLeafOrNodeAt Eff Resp iArg;
                sumMot = H.lam "s" (HI.bootSum L_id L_lon) (s:
                  H.forall "_ih" (allLeafOrNodeOrIdentityAt Eff Resp iArg s) (_:
                    PpCodomAt Eff Resp iArg));
                onIdentity = H.lam "d_id" L_id (d_id:
                  H.lam "_ih" (allIdentityAt Eff Resp iArg d_id) (_:
                    identityStep Eff Resp iArg d_id));
                onRest = H.lam "d_lon" L_lon (d_lon:
                  H.lam "ih_lon" (allLeafOrNodeAt Eff Resp iArg d_lon) (ih_lon:
                    H.app (innerStep Eff Resp iArg d_lon) ih_lon));
              in
              H.app (HI.bootSumElim L_id L_lon sumMot onIdentity onRest d) ih)));

  # Helper for the outer sumMot — at the outer plus, all-d dispatches on
  # the outer bootSum: inl → allIdentityAt, inr → allLeafOrNodeAt.
  allLeafOrNodeOrIdentityAt = Eff: Resp: iArg: s:
    H.allD k u2 (kontQueueRaw Eff Resp) descLevelTm
      (muFam Eff Resp)
      (Pp Eff Resp)
      iArg
      s;

  # ── qAppKernel: kernel-level qApp ────────────────────────────────
  # `qAppKernel Eff Resp i q x` — apply queue `q : μI U² kontQueueApp i`
  # to value `x : fst_(i)`, producing `μ freeFx (snd_(i)) tt`. The
  # `lowerAt` removes the lift wrapper Pp introduced; the inner `descInd`
  # produces a `Lift 1 1 _ (funAt iArg)` carrier.
  #
  # `iAnn = ann i u2` is required because `funAt` projects with
  # `H.fst_` / `H.snd_`; the kernel's `fst`/`snd` rules INFER the pair,
  # but `pair` has no inference rule (it's a check-only constructor
  # against a Sigma type). Annotating once at entry pins `i`'s type so
  # both projections elaborate cleanly when the caller supplies a literal
  # `H.pair X Y`. Variable indices (e.g. `iArg` bound inside step bodies)
  # are inferable directly; only externally-supplied indices need this.
  qAppKernel = Eff: Resp: i: q: x:
    let
      iAnn = H.ann i u2;
      indResult =
        H.descInd (kontQueueRaw Eff Resp) (Pp Eff Resp) (step Eff Resp) iAnn q;
      lowered = HII.lowerAt motiveLevelTm descLevelTm (funAt Eff Resp iAnn) indResult;
    in
    H.app lowered x;

  # ── qAppIdLaw: the Identity-collapse law ─────────────────────────
  # Stated and proved at type `Π(X:U). Π(x:X). bootEq (μ freeFx X)
  # (qAppKernel (X,X) (qIdentity X) x) (pureCon X x)`. Proof: refl. The
  # kernel's conv sees the LHS β-reduce through descInd-on-descCon →
  # Identity step → bootJ-on-refl → liftAt → lowerAt → Σ-β down to the
  # RHS.
  qAppIdLawTy = Eff: Resp:
    H.forall "X" (H.u 0) (X:
      H.forall "x" X (x:
        HI.bootEq
          (H.mu (freeFxApp Eff Resp X) H.tt)
          (qAppKernel Eff Resp (pairXY X X) (qIdentity Eff Resp X) x)
          (pureCon Eff Resp X x)));

  qAppIdLaw = Eff: Resp:
    H.lam "X" (H.u 0) (X:
      H.lam "x" X (x:
        HI.bootRefl));

  # ── test fixtures ────────────────────────────────────────────────
  testEff = H.bool;
  testResp = H.ann
    (H.lam "_" testEff (_: H.nat))
    (H.forall "_" testEff (_: H.u 0));

in
{
  scope = {
    "descind-laws" = api.namespace {
      description = "fx.experimental.desc-interp.descind-laws: kernel-level laws derived via `descInd kontQueueApp` at the indexed slice. Hosts qAppKernel (kernel-resident transposition of trampoline.qApp) and qAppIdLaw (qApp qIdentity x ≡ pure x as a kernel conv-witness).";

      value = {
        qAppKernel = api.leaf {
          value = qAppKernel;
          description = "qAppKernel Eff Resp i q x — kernel-resident `qApp` defined via `descInd kontQueueApp`. Identity branch returns `pureCon X x` (X = fst_(i) = snd_(i) forced by index); Leaf branch returns `fn x`; Node branch returns `bind (ih_l x) ih_r` cashing in both indexed IHs at (X,M) and (M,A). Mirrors `trampoline.qApp` but at the kernel layer.";
          signature = "qAppKernel : Hoas U -> Hoas (U -> U) -> Hoas U² -> Hoas (μI U² kontQueueApp i) -> Hoas (fst_(i)) -> Hoas (μ freeFxApp Eff Resp (snd_(i)) tt)";
          tests = {
            "qAppKernel-on-qIdentity-at-Nat-checks" = {
              # `qAppKernel _ _ (Nat, Nat) (qIdentity Nat) (natLit 5) : μ freeFx Nat tt`
              # — the term must be well-typed under check.nix. Conv-reduces
              # through descInd-on-descCon (β to Identity step) and bootJ-on-
              # refl (eliminates the index transport) down to `pureCon Nat 5`.
              expr =
                let
                  ty = H.mu (freeFxApp testEff testResp H.nat) H.tt;
                  tm = qAppKernel testEff testResp (pairXY H.nat H.nat)
                    (qIdentity testEff testResp H.nat)
                    (H.natLit 5);
                in
                (H.checkHoas ty tm).tag;
              expected = "app";
            };

            "qAppKernel-on-qIdentity-conv-equals-pure" = {
              # Conv test: the LHS evaluates to the same VDescCon as
              # `pureCon Eff Resp Nat (natLit 5)`. Both sides Pure-shaped, so
              # conv decides them.
              expr =
                let
                  lhs = qAppKernel testEff testResp (pairXY H.nat H.nat)
                    (qIdentity testEff testResp H.nat)
                    (H.natLit 5);
                  rhs = pureCon testEff testResp H.nat (H.natLit 5);
                  lhsVal = E.eval [ ] (H.elab lhs);
                  rhsVal = E.eval [ ] (H.elab rhs);
                in
                C.conv 0 lhsVal rhsVal;
              expected = true;
            };
          };
        };

        qAppIdLaw = api.leaf {
          value = qAppIdLaw;
          description = "qAppIdLaw : Π(X:U). Π(x:X). bootEq (μ freeFx X) (qAppKernel (X,X) (qIdentity X) x) (pureCon X x). The Identity-collapse law as a kernel conv-witness; the proof is `bootRefl`, justified by descInd-on-descCon β through the Identity step body. Demonstrates that the indexed inductive hypothesis is operationally usable — the lemma's well-typedness depends essentially on `descInd kontQueueApp` projecting `fst_(i)` / `snd_(i)`.";
          signature = "qAppIdLaw : Π(X:U). Π(x:X). bootEq (μ freeFx X) (qAppKernel (X,X) (qIdentity X) x) (pureCon X x)";
          tests = {
            "qAppIdLaw-checks" = {
              # Verification gate: the lemma's expression typechecks under
              # check.nix against its stated type. `bootRefl`
              # is accepted only because the kernel's conv-equality sees
              # `qAppKernel (X,X) (qIdentity X) x ≡ pureCon X x`.
              expr = (H.checkHoas
                (qAppIdLawTy testEff testResp)
                (qAppIdLaw testEff testResp)).tag;
              expected = "lam";
            };
          };
        };
        qAppIdLawTy = api.leaf {
          value = qAppIdLawTy;
          description = "qAppIdLawTy Eff Resp: Π-type generated for the qApp identity law at one effect signature.";
        };
      };
    };
  };
}
