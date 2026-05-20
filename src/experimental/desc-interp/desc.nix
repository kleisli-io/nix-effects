# FreeFx Eff Resp A : Desc U U — freer monad encoded as a `plus` of two
# summands. Pure is `arg A (\_v → ret)`; Impure is
# `arg Eff (\op → arg (mu (kontQueue Eff Resp (Resp op) A)) (\_q → ret))`.
# The continuation slot is a queue value — a `μ(kontQueue …)` inhabitant —
# rather than a meta-level Nix function: linear bind chains compose by
# `qSnoc` on the queue, sidestepping Nix's call-stack ceiling. This is
# the description-side transposition of Kiselyov & Ishii's FTCQueue
# (`nix/nix-effects/src/queue.nix`). The smart-constructors `freeFxApp`
# / `kontQueueApp` wrap the bare descriptions in `H.canonApp` so conv /
# quote short-circuit on the canonical identity (`_canonRef = { id;
# params; }`) without forcing the recursive `.D` slot.
# Refs: Swierstra (JFP'08); Kiselyov & Ishii (Haskell'15); Abbott/
# Altenkirch/Ghani (FoSSaCS'03); Chapman/Dagand/McBride/Morris (ICFP'10);
# Xia et al. (POPL'20).
{ fx, ... }:
let
  H  = fx.tc.hoas;
  HI = fx.tc.hoas._internal;
  G  = fx.tc.generic.desc;

  # ---- freeFx ----------------------------------------------------------

  pureSummand = A: H.descArg H.unit 0 A (_v: H.descRet);

  # `impureSummand Eff Resp A` — `arg Eff (\op → arg (μ kontQueue) (\_q → ret))`.
  # The second `arg`'s sort is the queue's μ — at this slot, the freer monad's
  # continuation is reified as a queue value rather than a meta-level fn.
  impureSummand = Eff: Resp: A:
    H.descArg H.unit 0 Eff (op:
      H.descArg H.unit 0
        (H.mu (kontQueueApp Eff Resp (H.app Resp op) A) H.tt)
        (_q: H.descRet));

  # Self-reference is safe under Nix laziness: `H.mu`'s `D` field is a thunk.
  freeFx = Eff: Resp: A:
    H.plus (pureSummand A) (impureSummand Eff Resp A);

  # Identity-tagged HOAS form of `freeFx Eff Resp A`. Wrap call sites that
  # need conv/quote to short-circuit on the `("freeFx", [Eff, Resp, A])`
  # tag rather than walk `.D`. The body re-introduces E/R/A as HOAS
  # lambda parameters; canonApp applies the body to the params at eval
  # time and stamps the resulting VDescCon with `_canonRef`.
  freeFxApp = Eff: Resp: A:
    H.canonApp "freeFx" [ Eff Resp A ] (
      H.lam "E" (H.u 0) (E:
      H.lam "R" (H.forall "_" E (_: H.u 0)) (R:
      H.lam "A" (H.u 0) (A:
        freeFx E R A))));

  motiveFor = Eff: Resp: A:
    H.lam "_i" H.unit (_: H.mu (freeFxApp Eff Resp A) H.tt);
  pureCarrier = Eff: Resp: A:
    H.interpD 0 H.unit (pureSummand A) (motiveFor Eff Resp A) H.tt;
  impureCarrier = Eff: Resp: A:
    H.interpD 0 H.unit (impureSummand Eff Resp A) (motiveFor Eff Resp A) H.tt;

  # `pureCon Eff Resp A` evaluates the (Eff, Resp, A)-dependent
  # descriptions / carriers ONCE and returns a closure `v ↦ descCon …`.
  # `kernel.pure` is a direct alias and the trampoline's leaf-application
  # branch invokes `pure_RA = K.pure E R A` then `pure_RA v` many times;
  # the outer let shares `D`/`pC`/`iC` across all of those.
  pureCon = Eff: Resp: A:
    let
      D  = freeFx Eff Resp A;
      pC = pureCarrier Eff Resp A;
      iC = impureCarrier Eff Resp A;
    in v:
      H.descCon D H.tt
        (HI.bootInl pC iC (H.pair v HI.bootRefl));

  # `impureCon Eff Resp A op q` — `op : Eff` and `q : μ(kontQueue Eff Resp
  # (Resp op) A)` (a queue value, not a function). Build the inr payload
  # `(op, (q, refl))`. Not memoised: callers (`kernel.send`, `kernel.bind`)
  # invoke it once per Impure node without let-binding the partial app,
  # so the outer-let pattern from `pureCon` would not share — only add
  # overhead.
  impureCon = Eff: Resp: A: op: q:
    H.descCon (freeFx Eff Resp A) H.tt
      (HI.bootInr (pureCarrier Eff Resp A) (impureCarrier Eff Resp A)
        (H.pair op (H.pair q HI.bootRefl)));

  # ---- kontQueue (description-side FTCQueue) ---------------------------
  #
  # `kontQueue Eff Resp X A : Desc U U` — three-summand plus encoding the
  # Kiselyov-Ishii catenable queue at the description layer:
  #   Identity : queue with only the identity continuation (`descRet`).
  #   Leaf     : queue holding a single fn `X → μ(freeFxApp Eff Resp A)`.
  #   Node     : queue holding two recursive sub-queues.
  # We don't type-align the Node's two children (the production FTCQueue's
  # "intermediate type" lives in the Haskell GADT; Nix descriptions can't
  # encode it). Both children are `μ(kontQueueApp Eff Resp X A) tt`.
  #
  # H.plus is binary, so the 3-way encoding nests as `plus(Identity, plus
  # (Leaf, Node))`.

  qIdentitySummand = H.descRet;

  qLeafSummand = Eff: Resp: X: A:
    H.descArg H.unit 0
      (H.forall "_" X (_: H.mu (freeFxApp Eff Resp A) H.tt))
      (_fn: H.descRet);

  qNodeSummand = Eff: Resp: X: A:
    H.descArg H.unit 0 (H.mu (kontQueueApp Eff Resp X A) H.tt) (_l:
      H.descArg H.unit 0 (H.mu (kontQueueApp Eff Resp X A) H.tt) (_r:
        H.descRet));

  qLeafOrNodeSummand = Eff: Resp: X: A:
    H.plus (qLeafSummand Eff Resp X A) (qNodeSummand Eff Resp X A);

  kontQueue = Eff: Resp: X: A:
    H.plus qIdentitySummand (qLeafOrNodeSummand Eff Resp X A);

  kontQueueApp = Eff: Resp: X: A:
    H.canonApp "kontQueue" [ Eff Resp X A ] (
      H.lam "E" (H.u 0) (E:
      H.lam "R" (H.forall "_" E (_: H.u 0)) (R:
      H.lam "X" (H.u 0) (X:
      H.lam "A" (H.u 0) (A:
        kontQueue E R X A)))));

  qMotiveFor = Eff: Resp: X: A:
    H.lam "_i" H.unit (_: H.mu (kontQueueApp Eff Resp X A) H.tt);

  qIdentityCarrier = Eff: Resp: X: A:
    H.interpD 0 H.unit qIdentitySummand (qMotiveFor Eff Resp X A) H.tt;
  qLeafCarrier = Eff: Resp: X: A:
    H.interpD 0 H.unit (qLeafSummand Eff Resp X A)
      (qMotiveFor Eff Resp X A) H.tt;
  qNodeCarrier = Eff: Resp: X: A:
    H.interpD 0 H.unit (qNodeSummand Eff Resp X A)
      (qMotiveFor Eff Resp X A) H.tt;
  qLeafOrNodeCarrier = Eff: Resp: X: A:
    H.interpD 0 H.unit (qLeafOrNodeSummand Eff Resp X A)
      (qMotiveFor Eff Resp X A) H.tt;

  # `qIdentity Eff Resp X A` — `bootInl` of the outer plus, payload = `refl`.
  qIdentity = Eff: Resp: X: A:
    H.descCon (kontQueue Eff Resp X A) H.tt
      (HI.bootInl (qIdentityCarrier Eff Resp X A)
                 (qLeafOrNodeCarrier Eff Resp X A)
        HI.bootRefl);

  # `qLeaf Eff Resp X A fn` — `bootInr` outer, `bootInl` inner, payload =
  # `(fn, refl)`. `fn` is a HOAS function `X → μ(freeFxApp Eff Resp A) tt`.
  # Not memoised: callers (`kernel.qSnoc`, `kernel.send`) do not let-bind
  # the (Eff,Resp,X,A) partial application, so the outer-let pattern from
  # `pureCon` would not share — only add overhead.
  qLeaf = Eff: Resp: X: A: fn:
    H.descCon (kontQueue Eff Resp X A) H.tt
      (HI.bootInr (qIdentityCarrier Eff Resp X A)
                 (qLeafOrNodeCarrier Eff Resp X A)
        (HI.bootInl (qLeafCarrier Eff Resp X A)
                   (qNodeCarrier Eff Resp X A)
          (H.pair fn HI.bootRefl)));

  # `qNode Eff Resp X A l r` — `bootInr` outer, `bootInr` inner, payload =
  # `(l, (r, refl))`. `l` and `r` are queue values. Not memoised for the
  # same reason as `qLeaf`.
  qNode = Eff: Resp: X: A: l: r:
    H.descCon (kontQueue Eff Resp X A) H.tt
      (HI.bootInr (qIdentityCarrier Eff Resp X A)
                 (qLeafOrNodeCarrier Eff Resp X A)
        (HI.bootInr (qLeafCarrier Eff Resp X A)
                   (qNodeCarrier Eff Resp X A)
          (H.pair l (H.pair r HI.bootRefl))));

  # ---- test fixtures ---------------------------------------------------

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.unit);
  testA    = H.nat;
  testX    = H.unit;                    # `Resp true_ = unit`
  testDesc = freeFx testEff testResp testA;
  testQueueDesc = kontQueue testEff testResp testX testA;

in {
  inherit freeFx freeFxApp pureCon impureCon
          kontQueue kontQueueApp qIdentity qLeaf qNode;

  __docs = {
    freeFx = {
      description = "freeFx Eff Resp A : Desc U U — freer monad as a plus-of-two-summands description; the Impure summand's continuation slot is a queue value `μ(kontQueue Eff Resp (Resp op) A)` rather than a meta-level fn.";
      signature = "freeFx : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (Desc U U)";
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

    freeFxApp = {
      description = "freeFxApp Eff Resp A — identity-tagged HOAS form of `freeFx Eff Resp A`; canonApp wrapper that stamps the resulting VDescCon with `_canonRef = { id = \"freeFx\"; params = [Eff, Resp, A]; }` so conv/quote short-circuit on the canonical identity.";
      signature = "freeFxApp : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (Desc U U)";
      tests = {
        "freeFxApp-htag" = {
          expr = (freeFxApp testEff testResp testA)._htag;
          expected = "canon-app";
        };
        "freeFxApp-self-equal" = {
          expr = G.deepEqualDesc
                   (freeFxApp testEff testResp testA)
                   (freeFxApp testEff testResp testA);
          expected = true;
        };
      };
    };

    pureCon = {
      description = "pureCon Eff Resp A v — smart constructor for the Pure summand; emits a desc-con HOAS form with an inl payload `(v, refl)`.";
      signature = "pureCon : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas A -> Hoas (FreeFx Eff Resp A)";
      tests = {
        "pureCon-emits-desc-con" = {
          expr = (pureCon testEff testResp testA (H.intLit 5))._htag;
          expected = "desc-con";
        };
      };
    };

    impureCon = {
      description = "impureCon Eff Resp A op q — smart constructor for the Impure summand; `q : μ(kontQueue Eff Resp (Resp op) A)` is a queue value carrying the continuation. Emits a desc-con HOAS form with an inr payload `(op, (q, refl))`.";
      signature = "impureCon : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas Eff -> Hoas (μ kontQueue …) -> Hoas (FreeFx Eff Resp A)";
      tests = {
        "impureCon-emits-desc-con" = {
          expr = (impureCon testEff testResp testA H.true_
                   (qIdentity testEff testResp testX testA))._htag;
          expected = "desc-con";
        };
        "impureCon-bootInr-snd-is-queue" = {
          expr = (impureCon testEff testResp testA H.true_
                   (qIdentity testEff testResp testX testA)).d.term.snd.fst._htag;
          expected = "desc-con";
        };
      };
    };

    kontQueue = {
      description = "kontQueue Eff Resp X A : Desc U U — description-side FTCQueue (Kiselyov & Ishii 2015 §3.1); three-summand plus encoding Identity / Leaf / Node. Levitation transposition of `nix/nix-effects/src/queue.nix`.";
      signature = "kontQueue : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (Desc U U)";
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
          expected = "ret";
        };
        "kontQueue-leaf-summand-kind" = {
          expr = (G.descView (qLeafSummand testEff testResp testX testA)).kind;
          expected = "arg";
        };
        "kontQueue-node-summand-kind" = {
          expr = (G.descView (qNodeSummand testEff testResp testX testA)).kind;
          expected = "arg";
        };
      };
    };

    kontQueueApp = {
      description = "kontQueueApp Eff Resp X A — identity-tagged HOAS form of `kontQueue Eff Resp X A`; canonApp wrapper that stamps the resulting VDescCon with `_canonRef = { id = \"kontQueue\"; params = [Eff, Resp, X, A]; }` so conv on μ(kontQueueApp …) self-equality short-circuits without forcing `.D`.";
      signature = "kontQueueApp : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (Desc U U)";
      tests = {
        "kontQueueApp-htag" = {
          expr = (kontQueueApp testEff testResp testX testA)._htag;
          expected = "canon-app";
        };
        "kontQueueApp-self-equal" = {
          expr = G.deepEqualDesc
                   (kontQueueApp testEff testResp testX testA)
                   (kontQueueApp testEff testResp testX testA);
          expected = true;
        };
        "kontQueueApp-distinguishes-by-X" = {
          expr = G.deepEqualDesc
                   (kontQueueApp testEff testResp H.unit testA)
                   (kontQueueApp testEff testResp H.bool testA);
          expected = false;
        };
      };
    };

    qIdentity = {
      description = "qIdentity Eff Resp X A — smart constructor for the Identity summand of `kontQueue`; emits a desc-con HOAS form with payload `bootInl refl` of the outer plus.";
      signature = "qIdentity : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (μ kontQueue …)";
      tests = {
        "qIdentity-emits-desc-con" = {
          expr = (qIdentity testEff testResp testX testA)._htag;
          expected = "desc-con";
        };
      };
    };

    qLeaf = {
      description = "qLeaf Eff Resp X A fn — smart constructor for the Leaf summand; `fn : X → μ(freeFxApp Eff Resp A)`. Emits a desc-con HOAS form with payload `bootInr (bootInl (fn, refl))` of the nested plus.";
      signature = "qLeaf : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (X -> μ freeFx) -> Hoas (μ kontQueue …)";
      tests = {
        "qLeaf-emits-desc-con" = {
          expr = (qLeaf testEff testResp testX testA
                   (H.lam "_" testX (_:
                     pureCon testEff testResp testA (H.intLit 0))))._htag;
          expected = "desc-con";
        };
      };
    };

    qNode = {
      description = "qNode Eff Resp X A l r — smart constructor for the Node summand; `l` and `r` are queue values. Emits a desc-con HOAS form with payload `bootInr (bootInr (l, (r, refl)))` of the nested plus.";
      signature = "qNode : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (μ kontQueue …) -> Hoas (μ kontQueue …) -> Hoas (μ kontQueue …)";
      tests = {
        "qNode-emits-desc-con" = {
          expr = (qNode testEff testResp testX testA
                   (qIdentity testEff testResp testX testA)
                   (qIdentity testEff testResp testX testA))._htag;
          expected = "desc-con";
        };
      };
    };
  };
}
