# Freer-monad kernel over FreeFx descriptions — `pure` / `send` / `bind`
# operate on HOAS `desc-con` inhabitants of `μ(freeFxApp Eff Resp A)`,
# mirroring `fx.kernel.{pure, send, bind}` at the description layer.
#
# `bind` does no recursive descent on the μ-tree: it peeks at the top
# `boot-inl` / `boot-inr` tag once and either applies the continuation
# (Pure) or snocs it into the Impure summand's queue (Impure). The
# Kiselyov-Ishii FTCQueue from `desc.nix` carries continuations as
# meta-level Nix functions stored at queue leaves — no reification.
# Linear bind chains stay flat in the queue, avoiding the closure-
# composition blow-up that overflows Nix's call stack at depth ≈10K.
#
# Equality boundary. The kontQueue's seam M (the existential
# `recI U² k (X, M); recI U² k (M, A)` in qNodeSummand) is the
# signature of indexed composition: a qNode at index (X, A) commits to
# a specific intermediate type witness joining its two children. `~q`
# (operational equivalence — two queues are equivalent iff they
# produce the same effects-and-result under every handler) is the
# principled equality relation on this family: it dissolves M's
# universal quantification into a definitional equivalence at the
# extensional layer, by quotienting over all witnesses that compute
# the same trampolined output. `deepEqualDesc` is strictly finer than
# `~q`: it distinguishes queues by their seam-witness data, and
# laws (ii)/(iii) on Impure `m` are theorems of `~q`, not of
# `deepEqualDesc`. The structural mismatch the FTCQueue surface
# exposes is the seam's intentional signature, not an artefact of
# representation choice. Atkey 2018's QTT-erasure offers a future-work
# route to erase the seam witnesses syntactically — collapsing `~q`
# into `deepEqualDesc` at the cost of an annotation discipline at use
# sites; for now the witnesses remain intensional data the trampoline
# traverses.
#
# Consequence: on the raw μ-tree, `deepEqualDesc` decides only the
# Pure-summand subcase of laws (i)-(iii); FTCQueue defers continuation
# composition, so `bind m pure` and `bind (bind m f) g` build queue
# shapes (Leaf vs Node, composed vs uncomposed) that differ on their
# seam witnesses. Normalising at each bind would restore the O(n²)
# blow-up the queue exists to avoid (and the ≈10K Nix call-depth
# ceiling). Under `trampoline.nix:run`, distinct seam-witness queues
# project to the same Pure leaf, so laws (ii)/(iii) on Impure `m`
# hold under `deepEqualDesc` on the post-run carriers — the
# trampoline is the computational content of the `~q` quotient.
# See `tests/experimental/desc-interp-laws/`. This file keeps the
# queue-evolution invariants and law (i) on all `m`.
#
# Refs: Kiselyov & Ishii (Haskell'15) §3.1 FTCQueue; Chapman/Dagand/
# McBride/Morris (ICFP'10) §6 indexed descriptions; Atkey (LICS'18)
# QTT; `nix/nix-effects/src/queue.nix` is the type-erased twin —
# same operational shape, different universe.
{ fx, api, ... }:
let
  H = fx.tc.hoas;
  G = fx.tc.generic.desc;
  D = fx.experimental.desc-interp.desc;
  inherit (D) pureCon impureCon qIdentity qLeaf qNode;

  # `pure Eff Resp A` — direct alias for `pureCon Eff Resp A`. The
  # 3-arg partial application is itself the memoised closure returned
  # by `pureCon` (carrying `D`/`pC`/`iC`); no wrapper layer is added.
  # Callers that let-bind the partial application
  # (`let p = pure E R A; in p v1; p v2; …`) reuse the cached carriers
  # across every invocation; direct `pure E R A v` call sites still
  # re-evaluate the chain each time.
  pure = Eff: Resp: A: pureCon Eff Resp A;

  # `send Eff Resp op` — issue an effect request with the identity
  # continuation. The queue is `qIdentity Eff Resp (Resp op)` carrying
  # `_index = { X = Resp op; A = Resp op; }`; a downstream `qApp`
  # consumer recognises it and resumes with `pure response` directly.
  #
  # `op` must be a HOAS term (carries `_htag`). The assertion keeps
  # Nix attrsets from tunnelling through to a kernel-eval crash with no
  # source line, since `Resp op` would silently produce a malformed HOAS
  # application.
  send = Eff: Resp: op:
    assert (op._htag or null) != null
      || throw "experimental.desc-interp.kernel.send: op must be a HOAS term, got Nix value (likely `{ _opTag = ... }` attrset)";
    let A = H.app Resp op;
    in impureCon Eff Resp A op (qIdentity Eff Resp A);

  # `bind Eff Resp A B m f`:
  #   Pure (boot-inl):  extract v from `m.d.term.fst`, apply `f`.
  #   Impure (boot-inr): extract `op` and queue `q`, snoc `f` onto `q`,
  #                      rebuild the Impure node.
  # The continuation `f` is a Nix-meta function `Hoas A → Hoas (μ freeFxApp
  # Eff Resp B)`. Bind never crosses into `f`'s body — continuations
  # remain meta-level closures, never reified into the description.
  #
  # qSnoc reads `q._index.A` as the output type of the prior chain; the
  # queue's sidecar carries the indexing intrinsic to the family.
  #
  # Force each branch's outer desc-con. Otherwise foldl' only reaches the
  # returned attrset shell and leaves a chain of lazy branch thunks for the
  # final consumer to force recursively.
  freeLevelTm = H.levelSuc H.levelZero;
  lowerFreeField = A: x:
    if builtins.isAttrs x
      && (x._htag or null) == "lift-intro"
      && (x.l or null) == H.levelZero
      && (x.m or null) == freeLevelTm
      && x ? a
    then x.a
    else H.lowerAt H.levelZero freeLevelTm A x;

  bind = Eff: Resp: A: B: m: f:
    if m.d._htag == "boot-inl"
    then
      let
        v = lowerFreeField A m.d.term.fst;
        r = builtins.seq v (f v);
      in
      builtins.seq r.d._htag r
    else
      let
        op = lowerFreeField Eff m.d.term.fst;
        q = m.d.term.snd.fst;
        newQ = qSnoc Eff Resp B q f;
      in
      builtins.seq op (builtins.seq newQ.d._htag (impureCon Eff Resp B op newQ));

  # `qSnoc Eff Resp B q f` — append `f` to the right of `q`. The chain's
  # input type is `q._index.X` and its current output type is
  # `q._index.A`; `f : q._index.A → μ freeFx … B` shifts the output to
  # B. Identity short-circuits to a fresh Leaf at `(q._index.A, B)`.
  # Otherwise builds `qNode q (qLeaf q._index.A B fn)`; qNode reads both
  # children's `_index` sidecars and asserts the seam `M = q._index.A`
  # via Nix-level equality.
  qSnoc = Eff: Resp: B: q: f:
    let
      Av = q._index.A;
      leafFn = H.lam "_x" Av (x: f x);
      newLeaf = qLeaf Eff Resp Av B leafFn;
    in
    if q.d._htag == "boot-inl"
    then newLeaf
    else qNode Eff Resp q newLeaf;

  # ---- test fixtures ---------------------------------------------------

  testEff = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat); # Resp(_) = nat — keeps A = nat.

  # Let-bind the partial applications so the memoised closures inside
  # `pure` / `bind` are shared across every fixture invocation.
  pure_T_R_N = pure testEff testResp H.nat;
  bind_T_R_N_N = bind testEff testResp H.nat H.nat;

  pureN = v: pure_T_R_N (H.intLit v);
  sendT = send testEff testResp H.true_;
  bindNN = bind_T_R_N_N;
  idK = pure_T_R_N;

  # One Pure-shaped program retained as a sanity anchor for the
  # structurally-decidable monad-law subcase (laws (ii)/(iii) on
  # Pure `m`). The Impure-case structural-equality failure is
  # *intrinsic* to the FTCQueue design — see the header — and is
  # exercised by the queue-evolution tests below rather than by
  # pretending `deepEqualDesc` can witness the laws on Impure `m`.
  mPure = pureN 0;

  f_arr = _: pureN 1;
  g_arr = _: pureN 2;

  lawILhs = v: k: bindNN (pureN v) k;
  lawIRhs = v: k: k (H.intLit v);

in
{
  scope = {
    kernel = api.namespace {
      description = "fx.experimental.desc-interp.kernel: pure/send/bind constructors producing FreeFx Desc values directly as `μ freeFxApp` data, not Nix-host computations.";

      value = {
        pure = api.leaf {
          value = pure;
          description = "pure Eff Resp A v — lift v into the Pure summand of FreeFx; alias for `D.pureCon`.";
          signature = "pure : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas A -> Hoas (μ freeFxApp Eff Resp A)";
          tests = {
            "pure-emits-desc-con" = {
              expr = (pureN 5)._htag;
              expected = "desc-con";
            };
            "pure-payload-is-bootInl" = {
              expr = (pureN 5).d._htag;
              expected = "boot-inl";
            };
          };
        };
        send = api.leaf {
          value = send;
          description = "send Eff Resp op — issue an effect request with the identity continuation; emits an impureCon whose queue slot is `qIdentity Eff Resp (Resp op)` at index `(Resp op, Resp op)`.";
          signature = "send : Hoas U -> Hoas (U -> U) -> Hoas Eff -> Hoas (μ freeFxApp Eff Resp (Resp op))";
          tests = {
            "send-emits-desc-con" = {
              expr = sendT._htag;
              expected = "desc-con";
            };
            "send-summand-is-boot-inr" = {
              # send produces an Impure node — right summand of freeFx's
              # outer plus.
              expr = sendT.d._htag;
              expected = "boot-inr";
            };
            "send-queue-is-identity-via-index" = {
              # `send op` wires the response back to the program via the
              # identity continuation: the queue carries `_index = { X =
              # Resp op; A = Resp op; }` — the Identity contract X == A,
              # observed semantically without inspecting the queue's
              # summand encoding.
              expr =
                let q = sendT.d.term.snd.fst;
                in q._index.X == q._index.A;
              expected = true;
            };
          };
        };
        bind = api.leaf {
          value = bind;
          description = "bind Eff Resp A B m f — sequence two computations. Pure case applies `f` to the payload; Impure case snocs `f` into the queue. Linear continuation chains stay flat in the queue, sidestepping Nix's call-depth ceiling.";
          signature = "bind : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (μ freeFxApp Eff Resp A) -> (Hoas A -> Hoas (μ freeFxApp Eff Resp B)) -> Hoas (μ freeFxApp Eff Resp B)";
          tests = {
            # ----- Law (i): left identity — bind (pure v) k == k v -----
            "law-i-v0" = {
              expr = G.deepEqualDesc (lawILhs 0 idK) (lawIRhs 0 idK);
              expected = true;
            };
            "law-i-v42" = {
              expr = G.deepEqualDesc (lawILhs 42 idK) (lawIRhs 42 idK);
              expected = true;
            };
            "law-i-v7" = {
              expr = G.deepEqualDesc (lawILhs 7 idK) (lawIRhs 7 idK);
              expected = true;
            };
            "law-i-v100" = {
              expr = G.deepEqualDesc
                (lawILhs 100 (_: pureN 999))
                (lawIRhs 100 (_: pureN 999));
              expected = true;
            };
            "law-i-vN9" = {
              expr = G.deepEqualDesc (lawILhs (-9) f_arr) (lawIRhs (-9) f_arr);
              expected = true;
            };

            # ----- Laws (ii)/(iii) on Pure m — structurally trivial -----
            # Both sides reduce to the same `pure v`. Retained as sanity
            # anchors; the Impure-case statement is observational, not
            # structural — see the header for why `deepEqualDesc` cannot
            # decide these on Impure m.
            "law-ii-pure-m" = {
              expr = G.deepEqualDesc (bindNN mPure idK) mPure;
              expected = true;
            };
            "law-iii-pure-m" = {
              expr = G.deepEqualDesc
                (bindNN (bindNN mPure f_arr) g_arr)
                (bindNN mPure (x: bindNN (f_arr x) g_arr));
              expected = true;
            };

            # ----- Queue-evolution invariants on Impure m -----
            # `bind` rewrites the Impure summand's queue via `qSnoc`; the
            # mathematical content of the rewrite is observable in the
            # queue's `_index` sidecar (input X preserved, output A shifts
            # to B) and via deepEqualDesc inequality against the un-bound
            # original (the seam-witness shift that ~q quotients over).

            "bind-shifts-output-index-to-B" = {
              # bind : μ Eff Resp A → (A → μ Eff Resp B) → μ Eff Resp B.
              # The output queue's `_index.A` is B (here H.nat — `idK`
              # returns into μ … H.nat); `_index.X` is preserved from the
              # input chain (here Resp(true_) = H.nat).
              expr =
                let
                  r = bindNN sendT idK;
                  q = r.d.term.snd.fst;
                in
                q._index.A == H.nat;
              expected = true;
            };

            "bind-preserves-input-index-through-chain" = {
              # `_index.X` of the queue threads unchanged through any
              # number of binds: the start of the continuation chain is
              # determined by `send`'s `Resp op`, not by later `f`s.
              expr =
                let
                  r1 = bindNN sendT idK;
                  r2 = bindNN r1 idK;
                  r3 = bindNN r2 idK;
                  q3 = r3.d.term.snd.fst;
                  q1 = r1.d.term.snd.fst;
                in
                q3._index.X == q1._index.X;
              expected = true;
            };

            "law-ii-on-impure-m-not-deepEqual" = {
              # The structural inequality is the equality boundary set out
              # in the header: `bind m pure` snocs the identity
              # continuation onto `m`'s queue, distinguishing the result
              # from `m` at the seam-witness layer. Under `~q` the two are
              # equivalent (handlers cannot observe the difference); under
              # `deepEqualDesc` they are not. Witnessing the inequality
              # here is the honest pre-run picture.
              expr =
                G.deepEqualDesc
                  sendT
                  (bindNN sendT (x: pure testEff testResp H.nat x));
              expected = false;
            };

            # ----- Stack-safety stress tests -----
            "bind-depth-10K-pure-chain-equals-pure-0" = {
              # 10K bind chain on Pure-m reduces by law (i) at every step:
              # bind (pure 0) idK ≡ idK 0 ≡ pure 0. Closed form: pure 0.
              # foldl' iterates without growing the Nix call stack;
              # `deepEqualDesc` against the closed form both witnesses the
              # iterated law-i reduction and forces enough evaluation to
              # surface stack overflow as success=false.
              expr =
                let
                  n = 10000;
                  chain = builtins.foldl'
                    (m: _: bindNN m idK)
                    (pureN 0)
                    (builtins.genList (i: i) n);
                  cmp = builtins.tryEval
                    (G.deepEqualDesc chain (pureN 0));
                in
                cmp.success && cmp.value;
              expected = true;
            };
            "bind-depth-10K-send-chain" = {
              # 10K bind chain on Impure-m snocs into the queue each step —
              # the queue becomes a right-leaning Node tree of depth 10K, but
              # construction is one allocation per step, no stack growth.
              expr =
                let
                  n = 10000;
                  chain = builtins.foldl'
                    (m: _: bindNN m (_: sendT))
                    sendT
                    (builtins.genList (i: i) (n - 1));
                in
                (builtins.tryEval (builtins.seq chain._htag true)).success;
              expected = true;
            };
          };
        };
        qSnoc = api.leaf {
          value = qSnoc;
          description = "qSnoc Eff Resp B q f — append the Nix-meta continuation `f` (Hoas q._index.A → Hoas (μ freeFxApp Eff Resp B)) to the right of queue `q`. The chain's input type is q._index.X and its current output is q._index.A. Identity short-circuits to a fresh `qLeaf` at (q._index.A, B); otherwise builds `qNode q (qLeaf q._index.A B fn)` with the seam M = q._index.A asserted via the sidecar invariant on qNode.";
          signature = "qSnoc : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas (μI U² kontQueueApp …) -> (Hoas A -> Hoas (μ freeFxApp Eff Resp B)) -> Hoas (μI U² kontQueueApp …)";
          tests = {
            "qSnoc-on-identity-yields-leaf" = {
              # qSnoc qIdentity f → qLeaf f. qLeaf is `bootInr` outer +
              # `bootInl` inner. We probe the outer payload tag.
              expr =
                let
                  q = qIdentity testEff testResp H.nat;
                  snocced = qSnoc testEff testResp H.nat q idK;
                in
                snocced.d._htag;
              expected = "boot-inr";
            };
            "qSnoc-on-identity-yields-inner-bootInl" = {
              # The inner-plus payload is `bootInl` (Leaf side of inner plus).
              expr =
                let
                  q = qIdentity testEff testResp H.nat;
                  snocced = qSnoc testEff testResp H.nat q idK;
                in
                snocced.d.term._htag;
              expected = "boot-inl";
            };
            "qSnoc-on-non-identity-yields-node" = {
              # qSnoc twice: first hits Identity → qLeaf (inner bootInl);
              # second sees non-Identity → qNode (inner bootInr).
              expr =
                let
                  q1 = qIdentity testEff testResp H.nat;
                  q2 = qSnoc testEff testResp H.nat q1 idK;
                  q3 = qSnoc testEff testResp H.nat q2 idK;
                in
                q3.d.term._htag;
              expected = "boot-inr";
            };
            "qSnoc-preserves-input-index" = {
              # The chain's input type X is preserved through qSnoc: the
              # snocced queue still starts at q._index.X.
              expr =
                let
                  q1 = qIdentity testEff testResp H.nat;
                  q2 = qSnoc testEff testResp H.nat q1 idK;
                in
                q2._index.X == q1._index.X;
              expected = true;
            };
            "qSnoc-shifts-output-index-to-B" = {
              # qSnoc q f : the output type shifts to B (the codomain of
              # f's continuation). Here `qSnoc … H.nat …` declares B =
              # H.nat, and the result queue's `_index.A` is H.nat.
              expr =
                let
                  q1 = qIdentity testEff testResp H.nat;
                  q2 = qSnoc testEff testResp H.nat q1 idK;
                in
                q2._index.A == H.nat;
              expected = true;
            };

            "qSnoc-seam-threading-at-Nat-Bool-shifts-to-Nat-String" = {
              # qSnoc on q : (Nat, Bool) with a continuation producing
              # `μ freeFxApp … String`. The seam M = Bool is read from
              # `q._index.A`; qSnoc wraps the continuation at
              # `H.lam "_x" Bool (...)`, so the new leaf's `_index = (Bool,
              # String)` and the composite qNode inhabits (Nat, String).
              expr =
                let
                  q0 = qIdentity testEff testResp H.nat;
                  qNB = qSnoc testEff testResp H.bool q0
                    (_: pure testEff testResp H.bool H.true_);
                  qNS = qSnoc testEff testResp H.string qNB
                    (_: pure testEff testResp H.string
                      (H.stringLit "out"));
                in
                qNS._index.X == H.nat && qNS._index.A == H.string;
              expected = true;
            };
          };
        };
      };
    };
  };
}
