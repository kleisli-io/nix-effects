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
# composition blow-up that overflows Nix's call stack at depth ≈8K.
#
# Equality boundary. Monad laws (i)-(iii) hold *observationally* for
# all `m`, but `deepEqualDesc` only decides the Pure-summand subcase
# structurally. This is intrinsic, not a defect: FTCQueue's whole
# purpose is to defer continuation composition, so two queues with
# different tree shapes can be observationally equivalent (`bind m
# pure` snocs an extra Leaf onto `m`'s queue; `bind (bind m f) g`
# builds a right-leaning Node where `bind m (\x. bind (f x) g)`
# builds a Leaf with the composed continuation). If structural conv
# decided observational equality, FTCQueue would be unnecessary —
# you would normalise at every bind, restoring the O(n²) blow-up the
# queue exists to avoid (and the O(8K) call-depth ceiling we cannot
# afford under Nix). This file therefore verifies *queue-evolution
# invariants* on Impure `m` (the queue grows in the documented
# shape) plus law (i) on all `m`. Observational-equivalence proofs
# for laws (ii)/(iii) on Impure `m` belong with `run`/`handle` — a
# real `qApp` consumer that observes the queue's behaviour rather
# than its shape — and live in a separate module.
#
# Refs: Kiselyov & Ishii (Haskell'15) §3.1 FTCQueue; `nix/nix-effects/
# src/queue.nix` is the type-erased twin — same operational shape,
# different universe.
{ fx, ... }:
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
  # continuation. The queue is `qIdentity` at `(Resp op, Resp op)`; a
  # downstream `qApp` consumer recognises it and resumes with
  # `pure response` directly.
  send = Eff: Resp: op:
    let A = H.app Resp op;
    in impureCon Eff Resp A op (qIdentity Eff Resp A A);

  # `bind Eff Resp A B m f`:
  #   Pure (boot-inl):  extract v from `m.d.term.fst`, apply `f`.
  #   Impure (boot-inr): extract `op` and queue `q`, snoc `f` onto `q`,
  #                      rebuild the Impure node.
  # The continuation `f` is a Nix-meta function `Hoas A → Hoas (μ freeFxApp
  # Eff Resp B)`. Bind never crosses into `f`'s body — continuations
  # remain meta-level closures, never reified into the description.
  #
  # `builtins.seq newQ.d._htag` is mandatory: without it, repeated bind
  # builds a lazy chain of qSnoc thunks (each step's queue slot stores
  # an unevaluated `qSnoc q_prev f` whose body re-checks `q_prev.d._htag`,
  # forcing the previous qSnoc, cascading N levels deep). Forcing the
  # new queue to its outer descCon at each step keeps each iteration's
  # host stack at O(1) and makes the overall chain consumable without
  # blowing Nix's call-depth ceiling. Mirrors the deepSeq discipline at
  # `src/trampoline.nix:124`.
  bind = Eff: Resp: A: B: m: f:
    if m.d._htag == "boot-inl"
    then f m.d.term.fst
    else
      let op = m.d.term.fst;
          q  = m.d.term.snd.fst;
          X  = H.app Resp op;
          newQ = qSnoc Eff Resp X A B q f;
      in builtins.seq newQ.d._htag (impureCon Eff Resp B op newQ);

  # `qSnoc Eff Resp X A B q f` — append `f` to the right of `q`.
  # Identity short-circuits to a fresh Leaf (mirrors `queue.nix:33-34`).
  # Otherwise builds `qNode q (qLeaf f)`. We don't type-align the Node's
  # children — both slots are claimed at `(X, B)` even though the left
  # child carries `(X, A)` continuations; the type-imprecision is
  # invisible to conv at the HOAS layer and the downstream `qApp`
  # consumer routes values through correctly.
  qSnoc = Eff: Resp: X: A: B: q: f:
    let
      leafFn  = H.lam "_x" A (x: f x);
      newLeaf = qLeaf Eff Resp A B leafFn;
    in
      if q.d._htag == "boot-inl"
      then newLeaf
      else qNode Eff Resp X B q newLeaf;

  # ---- test fixtures ---------------------------------------------------

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);   # Resp(_) = nat — keeps A = nat.

  # Let-bind the partial applications so the memoised closures inside
  # `pure` / `bind` are SHARED across every fixture invocation. Without
  # these binds each `pure testEff testResp H.nat (H.intLit v)` rebuilds
  # the entire (Eff, Resp, A) carrier chain — re-introducing the same
  # per-call cost the closure refactor was designed to eliminate.
  pure_T_R_N = pure testEff testResp H.nat;
  bind_T_R_N_N = bind testEff testResp H.nat H.nat;

  pureN  = v: pure_T_R_N (H.intLit v);
  sendT  = send testEff testResp H.true_;
  bindNN = bind_T_R_N_N;
  idK    = pure_T_R_N;

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

in {
  inherit pure send bind qSnoc;

  __docs = {
    pure = {
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

    send = {
      description = "send Eff Resp op — issue an effect request with the identity continuation; emits an impureCon whose queue slot is `qIdentity`.";
      signature = "send : Hoas U -> Hoas (U -> U) -> Hoas Eff -> Hoas (μ freeFxApp Eff Resp (Resp op))";
      tests = {
        "send-emits-desc-con" = {
          expr = sendT._htag;
          expected = "desc-con";
        };
        "send-payload-is-bootInr" = {
          expr = sendT.d._htag;
          expected = "boot-inr";
        };
        "send-queue-is-identity" = {
          # Impure payload is `pair op (pair q refl)`; queue `q` is at
          # `.d.term.snd.fst`. qIdentity has `.d._htag = "boot-inl"`
          # (outer plus's left summand).
          expr = sendT.d.term.snd.fst.d._htag;
          expected = "boot-inl";
        };
      };
    };

    bind = {
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
        # `bind` / `qSnoc` grow the queue in the documented shape, and
        # the divergence from `m`'s tree shape under `bind m pure` is
        # exactly what makes the observational laws unprovable under
        # structural conv. Witnessing that divergence here is more
        # honest than asserting equalities that cannot hold.

        "bind-once-on-send-yields-qLeaf" = {
          # `bind sendT idK` snocs `idK` onto sendT's `qIdentity` queue,
          # firing the Identity short-circuit → qLeaf. Outer plus is
          # `boot-inr` (queue is non-Identity); inner plus is `boot-inl`
          # (Leaf side of the Leaf-vs-Node inner plus).
          expr =
            let r = bindNN sendT idK;
                q = r.d.term.snd.fst;
            in { outer = q.d._htag; inner = q.d.term._htag; };
          expected = { outer = "boot-inr"; inner = "boot-inl"; };
        };

        "bind-twice-on-send-yields-qNode" = {
          # Second `bind` sees a non-Identity queue and builds
          # qNode(qLeaf, qLeaf). Outer plus stays `boot-inr`; inner
          # plus flips to `boot-inr` (Node side).
          expr =
            let r = bindNN (bindNN sendT idK) idK;
                q = r.d.term.snd.fst;
            in { outer = q.d._htag; inner = q.d.term._htag; };
          expected = { outer = "boot-inr"; inner = "boot-inr"; };
        };

        "bind-preserves-op-through-chain" = {
          # The effect operation `op` rides through bind unchanged
          # regardless of queue depth; probe at depth 3.
          expr = (bindNN (bindNN (bindNN sendT idK) f_arr) g_arr)
                   .d.term.fst._htag;
          expected = (H.true_)._htag;
        };

        "law-ii-on-impure-m-diverges-structurally" = {
          # DIRECT witness for the equality boundary documented in the
          # header. `sendT` has a `qIdentity` queue (outer `boot-inl`);
          # `bind sendT pure` snocs an extra Leaf, producing a qLeaf
          # queue (outer `boot-inr`). The two are observationally equal
          # under any handler but structurally distinct. This is *why*
          # law (ii) cannot be a `deepEqualDesc` assertion on Impure m.
          expr = {
            original = sendT.d.term.snd.fst.d._htag;
            after_bind_pure =
              (bindNN sendT (x: pure testEff testResp H.nat x))
                .d.term.snd.fst.d._htag;
          };
          expected = { original = "boot-inl"; after_bind_pure = "boot-inr"; };
        };

        # ----- Impure-shape sanity (structural inspection, not laws) -----
        "bind-impure-preserves-op" = {
          expr = (bindNN sendT (_: pureN 1)).d.term.fst._htag;
          expected = (H.true_)._htag;
        };
        "bind-impure-grows-queue" = {
          # After one snoc onto qIdentity, the queue is a qLeaf — outer
          # bootInr, inner bootInl in the nested plus encoding.
          expr =
            let r = bindNN sendT (_: pureN 1);
                q = r.d.term.snd.fst;
            in q.d._htag;
          expected = "boot-inr";
        };

        # ----- Stack-safety stress tests -----
        "bind-depth-10K-pure-chain" = {
          # 10K bind chain on Pure-m discharges each bind to `f v` and
          # accumulates a single pureN. foldl' iterates without growing
          # the Nix call stack.
          expr =
            let
              n = 10000;
              chain = builtins.foldl'
                (m: _: bindNN m idK)
                (pureN 0)
                (builtins.genList (i: i) n);
            in
              (builtins.tryEval (builtins.seq chain._htag true)).success;
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

    qSnoc = {
      description = "qSnoc Eff Resp X A B q f — append the Nix-meta continuation `f` (Hoas A → Hoas (μ freeFxApp Eff Resp B)) to the right of queue `q`. Identity short-circuits to a fresh `qLeaf`; otherwise builds `qNode q (qLeaf f)`. Type-alignment on Node's children is not enforced at the HOAS layer.";
      signature = "qSnoc : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas U -> Hoas (μ kontQueueApp Eff Resp X A) -> (Hoas A -> Hoas (μ freeFxApp Eff Resp B)) -> Hoas (μ kontQueueApp Eff Resp X B)";
      tests = {
        "qSnoc-on-identity-yields-leaf" = {
          # qSnoc qIdentity f → qLeaf f. qLeaf is `bootInr` outer +
          # `bootInl` inner. We probe the outer payload tag.
          expr =
            let q = qIdentity testEff testResp H.nat H.nat;
                snocced = qSnoc testEff testResp H.nat H.nat H.nat q idK;
            in snocced.d._htag;
          expected = "boot-inr";
        };
        "qSnoc-on-identity-yields-inner-bootInl" = {
          # The inner-plus payload is `bootInl` (Leaf side of inner plus).
          expr =
            let q = qIdentity testEff testResp H.nat H.nat;
                snocced = qSnoc testEff testResp H.nat H.nat H.nat q idK;
            in snocced.d.term._htag;
          expected = "boot-inl";
        };
        "qSnoc-on-non-identity-yields-node" = {
          # qSnoc twice: first hits Identity → qLeaf (inner bootInl);
          # second sees non-Identity → qNode (inner bootInr).
          expr =
            let q1 = qIdentity testEff testResp H.nat H.nat;
                q2 = qSnoc testEff testResp H.nat H.nat H.nat q1 idK;
                q3 = qSnoc testEff testResp H.nat H.nat H.nat q2 idK;
            in q3.d.term._htag;
          expected = "boot-inr";
        };
      };
    };
  };
}
