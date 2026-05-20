# FreeFx Eff Resp A : Desc¹ ⊤ — freer monad encoded as a `plus` of two
# summands. Pure is `arg A (\_v → ret)`; Impure is
# `arg Eff (\op → arg (μI U² (kontQueueApp Eff Resp) (Resp op, A)) (\_q → ret))`.
# The continuation slot is a queue value — an inhabitant of the indexed
# carrier `μI U² (kontQueueApp …) (X, A)` — rather than a meta-level
# Nix function: linear bind chains compose by `qSnoc` on the queue,
# sidestepping Nix's call-stack ceiling. This is the description-side
# transposition of Kiselyov & Ishii's FTCQueue (`nix/nix-effects/src/
# queue.nix`). The smart-constructors `freeFxApp` / `kontQueueApp` wrap
# the bare descriptions in `H.canonApp` so conv / quote short-circuit on
# the canonical identity (`_canonRef = { id; params; }`) without forcing
# the recursive `.D` slot.
# Refs: Swierstra (JFP'08); Kiselyov & Ishii (Haskell'15); Abbott/
# Altenkirch/Ghani (FoSSaCS'03); Chapman/Dagand/McBride/Morris (ICFP'10);
# Xia et al. (POPL'20); Dagand/McBride (POPL'14); Atkey (LICS'18).
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  HI = fx.tc.hoas._internal;
  HII = fx.tc.hoas._internal._indexed;
  G = fx.tc.generic.desc;

  # ── Index type U² = U × U at universe 1 ──────────────────────────────
  # An indexed description over `I : U(iLev)` reifies an existential
  # type-equality binder as a non-uniform index parameter (CDMM 2010
  # §6). For kontQueue, the seam M in qNode is reified through descArgAt
  # rather than a GADT-level equality constraint.
  u2 = H.sigma "_" (H.u 0) (_: H.u 0);
  iLev1 = H.levelSuc H.levelZero;
  pairXY = X: Y: H.ann (H.pair X Y) u2;

  # `k = 1` is the description's binding universe. The existential
  # X-binder takes sort `H.u 0 : U(1)` (sort-universe = 1); the
  # continuation slot returns `μ freeFx`, and the queue field itself is
  # indexed over `U²`, so both live at U(1). The retI/recI leaves at
  # I:U(1) all fit under k=1.
  k = 1;

  # ── freeFx ────────────────────────────────────────────────────────────

  freeLevel = 1;
  freeLevelTm = H.levelSuc H.levelZero;
  sidecarKeys = [ "_opTag" "payload" "arg" "_inner" ];
  carrySidecars = x: y:
    if builtins.isAttrs x then
      y // builtins.listToAttrs
        (builtins.filter (kv: kv != null)
          (map
            (k:
              if builtins.hasAttr k x
              then { name = k; value = builtins.getAttr k x; }
              else null)
            sidecarKeys))
    else y;
  liftFreeField = A: x:
    carrySidecars x (HII.liftAt H.levelZero freeLevelTm A x);
  freeRetRefl =
    HII.liftAt H.levelZero freeLevelTm
      (HI.bootEq H.unit H.tt H.tt)
      HI.bootRefl;

  pureSummand = A:
    HII.descArgAt H.unit 0 freeLevel A (_v:
      H.retI H.unit freeLevel H.tt);

  # `impureSummand Eff Resp A` — `arg Eff (\op → arg (μI U² (kontQueueApp
  # Eff Resp) (Resp op, A)) (\_q → ret))`. The queue's μ lives at the U²
  # slice: `kontQueueApp Eff Resp : IDesc(U × U)` with the index
  # `(Resp op, A)` pinning where the continuation chain starts
  # (X = Resp op) and ends (A). The indexing is intrinsic to the family;
  # the wrapper takes only (Eff, Resp).
  impureSummand = Eff: Resp: A:
    HII.descArgAt H.unit 0 freeLevel Eff (op:
      HII.descArgAt H.unit freeLevel freeLevel
        (HII.muIAtI iLev1 u2 (kontQueueApp Eff Resp) (pairXY (H.app Resp op) A))
        (_q: H.retI H.unit freeLevel H.tt));

  # Self-reference is safe under Nix laziness: `H.mu` / `H.muI`'s D field
  # is a thunk.
  freeFx = Eff: Resp: A:
    HII.plusI H.unit freeLevel (pureSummand A) (impureSummand Eff Resp A);

  # Identity-tagged HOAS form of `freeFx Eff Resp A`. Wrap call sites that
  # need conv/quote to short-circuit on the `("freeFx", [Eff, Resp, A])`
  # tag rather than walk `.D`. The body re-introduces E/R/A as HOAS
  # lambda parameters; canonApp applies the body to the params at eval
  # time and stamps the resulting VDescCon with `_canonRef`.
  #
  # The body is annotated with its Π-type so canon-app's infer rule can
  # synthesise the body's type via the bidirectional `Annot` switch
  # rather than recurse into a bare λ-chain. Without the annotation,
  # using `freeFxApp` in a type position (e.g. inside `μ(freeFxApp …)`
  # at a Π-domain) hits `infer ctx tm.body` on a bare lambda.
  #
  # `annTrusted` is the δ-rule analogue: the body's well-typedness is
  # established once at the smart-constructor's definition site (the
  # body is a closed expression built from kernel-typed combinators
  # whose composition produces a `Desc¹ ⊤`). At use sites the
  # annotation propagates the type without re-elaborating the body —
  # mandatory here because `freeFxApp` and `kontQueueApp` are mutually
  # recursive (`freeFx`'s `impureSummand` references `μI(kontQueueApp)`
  # at a U² index and `kontQueue`'s leaf summand references
  # `μ(freeFxApp)` at the inner index `(tt, A)`), so a non-trusted
  # re-check would diverge. Conv on canon-app compares the `(id,
  # params)` stamp only — the annotation is invisible to equality.
  freeFxAppBodyTy =
    H.forall "E" (H.u 0) (E:
      H.forall "R" (H.forall "_" E (_: H.u 0)) (_R:
        H.forall "A" (H.u 0) (_A:
          HII.descAt freeLevel)));

  freeFxApp = Eff: Resp: A:
    let
      body =
        H.lam "E" (H.u 0) (E:
          H.lam "R" (H.forall "_" E (_: H.u 0)) (R:
            H.lam "A" (H.u 0) (A:
              freeFx E R A)));
    in
    H.canonApp "freeFx" [ Eff Resp A ] (H.annTrusted body freeFxAppBodyTy);

  motiveFor = Eff: Resp: A:
    H.lam "_i" H.unit (_: H.mu (freeFxApp Eff Resp A) H.tt);
  pureCarrier = Eff: Resp: A:
    H.interpD freeLevel H.unit (pureSummand A) (motiveFor Eff Resp A) H.tt;
  impureCarrier = Eff: Resp: A:
    H.interpD freeLevel H.unit (impureSummand Eff Resp A) (motiveFor Eff Resp A) H.tt;

  # `pureCon Eff Resp A` evaluates the (Eff, Resp, A)-dependent
  # descriptions / carriers ONCE and returns a closure `v ↦ descCon …`.
  # `kernel.pure` is a direct alias and the trampoline's leaf-application
  # branch invokes `pure_RA = K.pure E R A` then `pure_RA v` many times;
  # the outer let shares `D`/`pC`/`iC` across all of those.
  pureCon = Eff: Resp: A:
    let
      D = freeFx Eff Resp A;
      pC = pureCarrier Eff Resp A;
      iC = impureCarrier Eff Resp A;
    in
    v:
    H.descCon D H.tt
      (HI.bootInl pC iC (H.pair (liftFreeField A v) freeRetRefl));

  # `impureCon Eff Resp A op q` — `op : Eff` and `q : μI U² (kontQueueApp
  # Eff Resp) (Resp op, A)` (a queue value at the indexed slice, not a
  # function). U0 fields are stored through `LiftAt 0 1`; host-only op
  # sidecars are copied onto the wrapper for dispatch caches. Not
  # memoised: callers (`kernel.send`, `kernel.bind`) invoke it once per
  # Impure node without let-binding the partial app, so the outer-let
  # pattern from `pureCon` would not share — only add overhead.
  impureCon = Eff: Resp: A: op: q:
    H.descCon (freeFx Eff Resp A) H.tt
      (HI.bootInr (pureCarrier Eff Resp A) (impureCarrier Eff Resp A)
        (H.pair (liftFreeField Eff op) (H.pair q freeRetRefl)));

  # ── kontQueue (description-side FTCQueue at IDesc(U × U)) ─────────────
  #
  # `kontQueue Eff Resp : IDesc(U × U)` — three-summand plus encoding the
  # Kiselyov-Ishii catenable queue at the indexed-description layer:
  #
  #   Identity : ∃ X. retI U² k (X, X)
  #     The queue holding only the identity continuation. The existential
  #     X is reified via descArgAt; the leaf indexes at (X, X) so the
  #     queue's input and output types coincide.
  #
  #   Leaf : ∃ X. ∃ A. (X → μ(freeFxApp Eff Resp A) tt) → retI U² k (X, A)
  #     A single continuation X → A reified as data. The continuation
  #     produces a freer-monad value at the inner ⊤-slice (the freeFx's
  #     own index type), targeting result A.
  #
  #   Node : ∃ X. ∃ M. ∃ A. recI U² k (X, M); recI U² k (M, A);
  #                         retI U² k (X, A)
  #     Two recursive sub-queues joined at the seam M. CDMM 2010 §6's
  #     translation of Kiselyov-Ishii's GADT existential: M is the
  #     "intermediate type" that lives in Haskell's type system; here
  #     it is reified as an index witness and threaded through `recI`'s
  #     j-slot. The `_index = { X; A; }` sidecar carried by every smart
  #     constructor stores Xv/Av at the Nix-meta layer so qSnoc / qApp
  #     / qAppend can recover the index without parameter ceremony.
  #
  # Citations:
  #   CDMM 2010 §6 — indexed descriptions become non-uniform parameters
  #     (`Chapman, Dagand, McBride, Morris — The Gentle Art of Levitation`).
  #   Kiselyov-Ishii 2015 §3.1 — the FTCQueue GADT being ported
  #     (`Kiselyov, Ishii — Freer Monads, More Extensible Effects`).
  #   Dagand-McBride 2014 — ornament theory justifying the encoding
  #     (`Dagand, McBride — Transporting functions across ornaments`).
  #   Atkey 2018 — QTT erasure as future-work pointer for the residual
  #     ~q convergence (`Atkey — Syntax and Semantics of Quantitative TT`).
  #
  # H.plusI is binary, so the 3-way encoding nests as
  # `plusI(Identity, plusI(Leaf, Node))`.

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

  # Sub-queues are recursive children of the kontQueue carrier under the
  # indexed identity carrier. `recI U² k (X, M)` interprets to the IH at
  # that index — i.e. `descInd kontQueueApp` gets the proper indexed IH
  # at each sub-queue, with the index witnesses (X, M, A) recovered from
  # the encoder payload's descArgAt slots.
  qNodeSummand = Eff: Resp:
    HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (X:
      HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (M:
        HII.descArgAtAtI iLev1 u2 1 k (H.u 0) (A:
          HII.recIAtI iLev1 u2 k (pairXY X M)
            (HII.recIAtI iLev1 u2 k (pairXY M A)
              (HII.retIAtI iLev1 u2 k (pairXY X A))))));

  qLeafOrNodeSummand = Eff: Resp:
    HII.plusIAtI iLev1 u2 k (qLeafSummand Eff Resp) (qNodeSummand Eff Resp);

  kontQueue = Eff: Resp:
    HII.plusIAtI iLev1 u2 k qIdentitySummand (qLeafOrNodeSummand Eff Resp);

  # Annotated body — same δ-discipline as `freeFxApp` (`annTrusted` so
  # the mutually recursive body isn't re-checked on every use). The
  # queue's μI appears in type position (e.g. as the second `descArg`
  # sort in `impureSummand`). The body type is
  # `Π(E:U)(R:E→U). descIAt k U²`; the index is supplied at the muI use
  # site rather than threaded through the wrapper.
  kontQueueAppBodyTy =
    H.forall "E" (H.u 0) (E:
      H.forall "R" (H.forall "_" E (_: H.u 0)) (_R:
        HII.descIAtAtI iLev1 k u2));

  kontQueueApp = Eff: Resp:
    let
      body =
        H.lam "E" (H.u 0) (E:
          H.lam "R" (H.forall "_" E (_: H.u 0)) (R:
            kontQueue E R));
    in
    H.canonApp "kontQueue" [ Eff Resp ]
      (H.annTrusted body kontQueueAppBodyTy);

  qMotiveFor = Eff: Resp:
    H.lam "i" u2 (i: HII.muIAtI iLev1 u2 (kontQueueApp Eff Resp) i);

  qIdentityCarrier = Eff: Resp: i:
    H.interpD k u2 qIdentitySummand (qMotiveFor Eff Resp) i;
  qLeafCarrier = Eff: Resp: i:
    H.interpD k u2 (qLeafSummand Eff Resp) (qMotiveFor Eff Resp) i;
  qNodeCarrier = Eff: Resp: i:
    H.interpD k u2 (qNodeSummand Eff Resp) (qMotiveFor Eff Resp) i;
  qLeafOrNodeCarrier = Eff: Resp: i:
    H.interpD k u2 (qLeafOrNodeSummand Eff Resp) (qMotiveFor Eff Resp) i;

  # `qIdentity Eff Resp X` — `bootInl` of the outer plus, payload =
  # `(X, refl)`. The Identity contract `_index.X = _index.A = X` is the
  # canonical seam-aligned identity: a queue at (X, X) with no work.
  qIdentity = Eff: Resp: X:
    let i = pairXY X X; in
    (H.descCon (kontQueue Eff Resp) i
      (HI.bootInl
        (qIdentityCarrier Eff Resp i)
        (qLeafOrNodeCarrier Eff Resp i)
        (H.pair X HI.bootRefl)))
    // { _index = { inherit X; A = X; }; };

  # `qLeaf Eff Resp X A fn` — `bootInr` outer, `bootInl` inner, payload =
  # `(X, (A, (fn, refl)))`. `fn` is a HOAS lam `X → μ(freeFxApp Eff Resp
  # A) tt` and `fn.domain == X` is asserted host-level — the Nix-meta
  # surrogate for the descArgAt(X)-instantiation equality the kernel
  # would demand, mirroring qNode's `_index` seam check. Not memoised:
  # callers (`kernel.qSnoc`, `kernel.send`) don't share the
  # (Eff,Resp,X,A) partial application.
  qLeaf = Eff: Resp: X: A: fn:
    let
      i = pairXY X A;
      domainOk = (fn._htag or null) == "lam" && fn.domain == X;
    in
    if !domainOk
    then
      throw
        ("experimental.desc-interp.desc.qLeaf: continuation "
          + "domain mismatch — fn.domain ≠ X (host-level == is "
          + "the Nix-meta surrogate for the descArgAt(X)-binder "
          + "obligation; mirrors qNode's seam check).")
    else
      (H.descCon (kontQueue Eff Resp) i
        (HI.bootInr
          (qIdentityCarrier Eff Resp i)
          (qLeafOrNodeCarrier Eff Resp i)
          (HI.bootInl
            (qLeafCarrier Eff Resp i)
            (qNodeCarrier Eff Resp i)
            (H.pair X (H.pair A (H.pair fn HI.bootRefl))))))
      // { _index = { inherit X A; }; };

  # `qNode Eff Resp l r` — `bootInr` outer, `bootInr` inner, payload =
  # `(X, (M, (A, (l, (r, refl)))))`. `l` and `r` are queue values; their
  # `_index` sidecars carry the index witnesses. The seam M is
  # `l._index.A` (= `r._index.X`, enforced via Nix-level equality on the
  # sidecar — the kernel has no metavariables/unification at the surface,
  # so the principled Nix-meta equivalent of the kernel's universal
  # quantification over M is a host-level == on the constructed values).
  # Not memoised for the same reason as `qLeaf`.
  qNode = Eff: Resp: l: r:
    let
      Xv = l._index.X;
      Mv = l._index.A;
      Av = r._index.A;
      seamOk = Mv == r._index.X;
      i = pairXY Xv Av;
    in
    if !seamOk
    then
      throw
        ("experimental.desc-interp.desc.qNode: seam mismatch — "
          + "l._index.A vs r._index.X (left ends at index, right "
          + "starts at index — must agree)")
    else
      (H.descCon (kontQueue Eff Resp) i
        (HI.bootInr
          (qIdentityCarrier Eff Resp i)
          (qLeafOrNodeCarrier Eff Resp i)
          (HI.bootInr
            (qLeafCarrier Eff Resp i)
            (qNodeCarrier Eff Resp i)
            (H.pair Xv (H.pair Mv (H.pair Av
              (H.pair l (H.pair r HI.bootRefl))))))))
      // { _index = { X = Xv; A = Av; }; };

  # ── test fixtures ─────────────────────────────────────────────────────

  testEff = H.bool;
  testResp = H.lam "_" H.bool (_: H.unit);
  testA = H.nat;
  testX = H.unit; # `Resp true_ = unit`
  testDesc = freeFx testEff testResp testA;
  testQueueDesc = kontQueue testEff testResp;

in
{
  scope = {
    desc = api.namespace {
      description = "fx.experimental.desc-interp.desc: freer monad encoded as a levitated Desc (freeFx = pure + impure plus continuation queue); the substrate descInterp runs.";

      value = {
        freeFx = api.leaf {
          value = freeFx;
          description = "freeFx Eff Resp A : Desc¹ ⊤ — freer monad as a plus-of-two-summands description; the Impure summand's continuation slot is a queue value `μI U² (kontQueueApp Eff Resp) (Resp op, A)` rather than a meta-level fn.";
          signature = "freeFx : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (Desc¹ ⊤)";
          tests = {
            "freeFx-root-idx" = {
              expr = (G.descView testDesc).idx;
              expected = 4;
            };
            "freeFx-root-kind" = {
              expr = (G.descView testDesc).kind;
              expected = "plus";
            };
            "freeFx-pure-summand-kind" = {
              expr = (G.descView (pureSummand testA)).kind;
              expected = "arg";
            };
            "freeFx-impure-summand-kind" = {
              expr = (G.descView (impureSummand testEff testResp testA)).kind;
              expected = "arg";
            };
            "freeFx-pure-summand-mapDesc-identity" = {
              expr = G.deepEqualDesc
                (G.mapDesc (x: x.default) (pureSummand testA))
                (pureSummand testA);
              expected = true;
            };
          };
        };
        freeFxApp = api.leaf {
          value = freeFxApp;
          description = "freeFxApp Eff Resp A — identity-tagged HOAS form of `freeFx Eff Resp A`; canonApp wrapper that stamps the resulting VDescCon with `_canonRef = { id = \"freeFx\"; params = [Eff, Resp, A]; }` so conv/quote short-circuit on the canonical identity.";
          signature = "freeFxApp : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (Desc¹ ⊤)";
          tests = {
            "freeFxApp-htag" = {
              expr = (freeFxApp testEff testResp testA)._htag;
              expected = "canon-app";
            };
            "freeFxApp-canonRef-id" = {
              # Canonical-stamp identity: conv/quote short-circuit on this
              # rather than walk `.D`.
              expr = (freeFxApp testEff testResp testA).id;
              expected = "freeFx";
            };
            "freeFxApp-canonRef-params-length" = {
              # (Eff, Resp, A) — three index witnesses pin the family
              # member; A is intrinsic to freeFx (the return type), not
              # promoted out as kontQueue's (X, A) is.
              expr = builtins.length (freeFxApp testEff testResp testA).params;
              expected = 3;
            };
            "freeFxApp-self-equal" = {
              expr = G.deepEqualDesc
                (freeFxApp testEff testResp testA)
                (freeFxApp testEff testResp testA);
              expected = true;
            };
          };
        };
        pureCon = api.leaf {
          value = pureCon;
          description = "pureCon Eff Resp A v — smart constructor for the Pure summand; emits a desc-con HOAS form with a Desc¹ inl payload storing `v` and the ret witness through `LiftAt 0 1`.";
          signature = "pureCon : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas A -> Hoas (FreeFx Eff Resp A)";
          tests = {
            "pureCon-emits-desc-con" = {
              expr = (pureCon testEff testResp testA (H.intLit 5))._htag;
              expected = "desc-con";
            };
            "pureCon-summand-is-boot-inl" = {
              # Pure inhabits the left summand of freeFx's outer plus —
              # the structural fact distinguishing Pure from Impure at the
              # μ-tree's top.
              expr = (pureCon testEff testResp testA (H.intLit 5)).d._htag;
              expected = "boot-inl";
            };
          };
        };
        impureCon = api.leaf {
          value = impureCon;
          description = "impureCon Eff Resp A op q — smart constructor for the Impure summand; `q : μI U² (kontQueueApp Eff Resp) (Resp op, A)` is a queue value carrying the continuation. Emits a desc-con HOAS form with a Desc¹ inr payload storing `op` and the ret witness through `LiftAt 0 1`.";
          signature = "impureCon : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas Eff -> Hoas (μI U² kontQueueApp …) -> Hoas (FreeFx Eff Resp A)";
          tests = {
            "impureCon-emits-desc-con" = {
              expr = (impureCon testEff testResp testA H.true_
                (qIdentity testEff testResp testX))._htag;
              expected = "desc-con";
            };
            "impureCon-summand-is-boot-inr" = {
              # Impure inhabits the right summand of freeFx's outer plus.
              expr = (impureCon testEff testResp testA H.true_
                (qIdentity testEff testResp testX)).d._htag;
              expected = "boot-inr";
            };
            "impureCon-preserves-queue-index" = {
              # The queue threaded into the Impure summand retains its
              # `_index` sidecar — impureCon does not strip or rewrite the
              # indexing carried by `q`.
              expr =
                let
                  q = qIdentity testEff testResp testX;
                  m = impureCon testEff testResp testA H.true_ q;
                  qOut = m.d.term.snd.fst;
                in
                qOut._index.X == q._index.X
                && qOut._index.A == q._index.A;
              expected = true;
            };
          };
        };
        kontQueue = api.leaf {
          value = kontQueue;
          description = "kontQueue Eff Resp : IDesc(U × U) — description-side FTCQueue (Kiselyov & Ishii 2015, section 3.1) at the indexed slice; three-summand plus encoding Identity / Leaf / Node where ∃M existentials are reified as descArgAt-bound index witnesses (CDMM 2010, section 6). Levitation transposition of `nix/nix-effects/src/queue.nix`.";
          signature = "kontQueue : Hoas U -> Hoas (U -> U) -> Hoas (IDesc (U × U))";
          tests = {
            "kontQueue-root-idx" = {
              expr = (G.descView testQueueDesc).idx;
              expected = 4;
            };
            "kontQueue-root-kind" = {
              expr = (G.descView testQueueDesc).kind;
              expected = "plus";
            };
            "kontQueue-identity-summand-kind" = {
              expr = (G.descView qIdentitySummand).kind;
              expected = "arg";
            };
            "kontQueue-leaf-summand-kind" = {
              expr = (G.descView (qLeafSummand testEff testResp)).kind;
              expected = "arg";
            };
            "kontQueue-node-summand-kind" = {
              expr = (G.descView (qNodeSummand testEff testResp)).kind;
              expected = "arg";
            };
          };
        };
        kontQueueApp = api.leaf {
          value = kontQueueApp;
          description = "kontQueueApp Eff Resp — identity-tagged HOAS form of `kontQueue Eff Resp`; canonApp wrapper that stamps the resulting VDescCon with `_canonRef = { id = \"kontQueue\"; params = [Eff, Resp]; }` so conv on μI(kontQueueApp …) self-equality short-circuits without forcing `.D`. X and A are dropped from the wrapper's params — the indexing is intrinsic to `IDesc(U × U)`.";
          signature = "kontQueueApp : Hoas U -> Hoas (U -> U) -> Hoas (IDesc (U × U))";
          tests = {
            "kontQueueApp-htag" = {
              expr = (kontQueueApp testEff testResp)._htag;
              expected = "canon-app";
            };
            "kontQueueApp-canonRef-id" = {
              # Canonical-stamp identity: μI(kontQueueApp …) self-equality
              # short-circuits on this without forcing `.D`.
              expr = (kontQueueApp testEff testResp).id;
              expected = "kontQueue";
            };
            "kontQueueApp-canonRef-params-length" = {
              # (Eff, Resp) only — X and A are intrinsic to `IDesc(U × U)`,
              # supplied at the muI use site as the index witness.
              expr = builtins.length (kontQueueApp testEff testResp).params;
              expected = 2;
            };
            "kontQueueApp-self-equal" = {
              expr = G.deepEqualDesc
                (kontQueueApp testEff testResp)
                (kontQueueApp testEff testResp);
              expected = true;
            };
          };
        };
        qIdentity = api.leaf {
          value = qIdentity;
          description = "qIdentity Eff Resp X — smart constructor for the Identity summand of `kontQueue`; emits a desc-con HOAS form at index (X, X) with payload `bootInl (X, refl)` of the outer plus. Carries `_index = { X; A = X; }` sidecar.";
          signature = "qIdentity : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (μI U² kontQueueApp …)";
          tests = {
            "qIdentity-emits-desc-con" = {
              expr = (qIdentity testEff testResp testX)._htag;
              expected = "desc-con";
            };
            "qIdentity-index-X-equals-A" = {
              # The Identity contract: a queue with `_index.X == _index.A`
              # is seam-aligned for any (X = A) instantiation.
              expr =
                let q = qIdentity testEff testResp testX;
                in q._index.X == q._index.A;
              expected = true;
            };
            "qIdentity-summand-is-boot-inl" = {
              # qIdentity inhabits the left summand of kontQueue's outer
              # plus (Identity vs Leaf-or-Node) — the structural witness
              # at the queue's top that distinguishes Identity from any
              # non-empty queue.
              expr = (qIdentity testEff testResp testX).d._htag;
              expected = "boot-inl";
            };
          };
        };
        qLeaf = api.leaf {
          value = qLeaf;
          description = "qLeaf Eff Resp X A fn — smart constructor for the Leaf summand; `fn : X → μ(freeFxApp Eff Resp A)` is a HOAS lam with `fn.domain == X` (host-level `==` is the principled Nix-meta surrogate for the descArgAt(X)-instantiation equality the kernel checker would enforce, mirroring qNode's seam check on `_index`). Emits a desc-con HOAS form at index (X, A) with payload `bootInr (bootInl (X, (A, (fn, refl))))` of the nested plus. Carries `_index = { X; A; }` sidecar.";
          signature = "qLeaf : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (X -> μ freeFx) -> Hoas (μI U² kontQueueApp …)";
          tests = {
            "qLeaf-emits-desc-con" = {
              expr = (qLeaf testEff testResp testX testA
                (H.lam "_" testX (_:
                  pureCon testEff testResp testA (H.intLit 0))))._htag;
              expected = "desc-con";
            };
            "qLeaf-index-X-is-X" = {
              # qLeaf X A fn carries _index.X = X (input type of the leaf
              # continuation, the queue's starting point).
              expr =
                let
                  q = qLeaf testEff testResp testX testA
                    (H.lam "_" testX (_:
                      pureCon testEff testResp testA (H.intLit 0)));
                in
                q._index.X == testX;
              expected = true;
            };
            "qLeaf-index-A-is-A" = {
              # qLeaf X A fn carries _index.A = A (output type of the leaf
              # continuation, the queue's ending point).
              expr =
                let
                  q = qLeaf testEff testResp testX testA
                    (H.lam "_" testX (_:
                      pureCon testEff testResp testA (H.intLit 0)));
                in
                q._index.A == testA;
              expected = true;
            };
            "qLeaf-outer-summand-is-boot-inr" = {
              # qLeaf inhabits the right summand of the outer plus
              # (Identity-vs-rest): not the Identity branch.
              expr =
                (qLeaf testEff testResp testX testA
                  (H.lam "_" testX (_:
                    pureCon testEff testResp testA (H.intLit 0)))).d._htag;
              expected = "boot-inr";
            };
            "qLeaf-inner-summand-is-boot-inl" = {
              # Within the Leaf-or-Node inner plus, qLeaf inhabits the
              # left summand.
              expr =
                (qLeaf testEff testResp testX testA
                  (H.lam "_" testX (_:
                    pureCon testEff testResp testA (H.intLit 0)))).d.term._htag;
              expected = "boot-inl";
            };

            "qLeaf-domain-aligned-at-Nat-Bool-accepts" = {
              # qLeaf at (X = Nat, A = Bool) with continuation domain Nat:
              # accepts. The `_index` sidecar records the seam-aligned
              # indices that qSnoc / qNode read for chain-seam discipline.
              expr =
                let
                  cont = H.lam "_n" H.nat (_:
                    pureCon testEff testResp H.bool H.true_);
                  q = qLeaf testEff testResp H.nat H.bool cont;
                in
                q._index.X == H.nat && q._index.A == H.bool;
              expected = true;
            };

            "qLeaf-domain-mismatch-at-Nat-Bool-throws" = {
              # qLeaf at (X = Nat, A = Bool) with continuation domain String:
              # rejected at construction by host-level `fn.domain == X`. The
              # leaf summand's descArg sort
              # `forall _ X (_: μ freeFxApp Eff Resp A)` demands fn's domain
              # be the X bound by the enclosing descArgAt(X).
              expr =
                let
                  cont = H.lam "_s" H.string (_:
                    pureCon testEff testResp H.bool H.true_);
                in
                (builtins.tryEval
                  (qLeaf testEff testResp H.nat H.bool cont)._htag).success;
              expected = false;
            };

            "qLeaf-bypass-fails-qNode-seam-check-Nat-Bool-vs-Nat-String" = {
              # qNode's `l._index.A == r._index.X` seam check fires when a
              # leaf at (Nat, String) is composed after a chain ending at
              # Bool — Bool ≠ Nat. The seam-alignment obligation is enforced
              # at the qNode boundary regardless of how the children were
              # built; qSnoc threads `q._index.A` into the new leaf's domain
              # so this state is unreachable through qSnoc.
              expr =
                let
                  l = qLeaf testEff testResp H.nat H.bool
                    (H.lam "_n" H.nat (_:
                      pureCon testEff testResp H.bool H.true_));
                  misaligned = qLeaf testEff testResp H.nat H.string
                    (H.lam "_n" H.nat (_:
                      pureCon testEff testResp H.string
                        (H.stringLit "out")));
                in
                (builtins.tryEval
                  (qNode testEff testResp l misaligned).d._htag).success;
              expected = false;
            };
          };
        };
        qNode = api.leaf {
          value = qNode;
          description = "qNode Eff Resp l r — smart constructor for the Node summand; `l` and `r` are queue values whose `_index` sidecars supply the index witnesses. Seam M = l._index.A is asserted equal to r._index.X via Nix-level == (kernel has no surface metavariables; the host-level check is the principled enforcement). Emits a desc-con HOAS form at index (l._index.X, r._index.A) with payload `bootInr (bootInr (X, (M, (A, (l, (r, refl))))))` of the nested plus. Carries `_index = { X; A; }` sidecar.";
          signature = "qNode : Hoas U -> Hoas (U -> U) -> Hoas (μI U² kontQueueApp …) -> Hoas (μI U² kontQueueApp …) -> Hoas (μI U² kontQueueApp …)";
          tests = {
            "qNode-emits-desc-con" = {
              expr =
                let
                  l = qIdentity testEff testResp testX;
                  r = qIdentity testEff testResp testX;
                in
                (qNode testEff testResp l r)._htag;
              expected = "desc-con";
            };
            "qNode-index-extremes-from-children" = {
              # qNode l r contracts: _index.X = l._index.X (queue starts
              # where l starts) and _index.A = r._index.A (queue ends where
              # r ends), with the seam M = l._index.A = r._index.X joining
              # the two children at their shared intermediate type.
              expr =
                let
                  l = qLeaf testEff testResp testX testA
                    (H.lam "_" testX (_:
                      pureCon testEff testResp testA (H.intLit 0)));
                  r = qIdentity testEff testResp testA;
                  n = qNode testEff testResp l r;
                in
                n._index.X == l._index.X
                && n._index.A == r._index.A
                && l._index.A == r._index.X;
              expected = true;
            };
            "qNode-outer-summand-is-boot-inr" = {
              # qNode inhabits the right summand of the outer plus
              # (Identity-vs-rest): not the Identity branch.
              expr =
                let
                  l = qIdentity testEff testResp testX;
                  r = qIdentity testEff testResp testX;
                in
                (qNode testEff testResp l r).d._htag;
              expected = "boot-inr";
            };
            "qNode-inner-summand-is-boot-inr" = {
              # Within the Leaf-or-Node inner plus, qNode inhabits the
              # right summand.
              expr =
                let
                  l = qIdentity testEff testResp testX;
                  r = qIdentity testEff testResp testX;
                in
                (qNode testEff testResp l r).d.term._htag;
              expected = "boot-inr";
            };
            "qNode-seam-mismatch-throws" = {
              # The seam alignment `l._index.A == r._index.X` is the
              # principled Nix-meta equivalent of CDMM 2010 §6's
              # existential-equality constraint on the M witness. Host-level
              # `==` enforces it; mismatched children abort construction.
              expr =
                let
                  l = qLeaf testEff testResp testX testA
                    (H.lam "_" testX (_:
                      pureCon testEff testResp testA (H.intLit 0)));
                  r = qLeaf testEff testResp testEff testA
                    (H.lam "_" testEff (_:
                      pureCon testEff testResp testA (H.intLit 1)));
                in
                (builtins.tryEval
                  (qNode testEff testResp l r).d._htag).success;
              expected = false;
            };
          };
        };
      };
    };
  };
}
