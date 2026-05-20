# Trampolined interpreter for FreeFx descriptions — `run` / `handle`
# drive `μ(freeFxApp Eff Resp A)` programs to completion via
# `builtins.genericClosure`, dispatching effects through user-supplied
# handlers. The continuation queue inside each Impure node is walked
# by `qApp`, which itself uses `genericClosure` to keep host stack
# depth at O(1) regardless of queue size.
#
# Operational shape mirrors `nix/nix-effects/src/queue.nix:qApp` and
# `nix/nix-effects/src/trampoline.nix:interpret`. Differences:
#  - Programs are `μ(freeFxApp …)` values, not the production
#    `Pure`/`Impure` records. Pure/Impure are decided by the outer
#    plus tag (`m.d._htag`).
#  - The queue is `μ(kontQueueApp …)`, not a sumtype attrset. Leaves
#    store HOAS lams; their `.body` field is the underlying Nix
#    function used for meta-level beta (`leafFn.body x`).
#  - Ops are HOAS values of type `Eff` (no synthetic `.name`/`.param`
#    fields). Handlers are a single function `{ param, state } -> ...`
#    where `param` is the op HOAS value; the handler dispatches on
#    whatever structure of the op it cares about.
#
# Refs: Kiselyov & Ishii (Haskell'15) §3.1; Plotkin & Pretnar (2009)
# for the resume/abort encoding; Gibbons (2021) on associativity-as-
# precondition for accumulating worklists.
{ fx, lib, ... }:
let
  H = fx.tc.hoas;
  D = fx.experimental.desc-interp.desc;
  K = fx.experimental.desc-interp.kernel;

  inherit (D) impureCon qIdentity qLeaf qNode;
  inherit (K) pure send bind qSnoc;

  # ---- queue traversal -------------------------------------------------

  # Node-tag predicates on `μ(kontQueueApp …)` values.
  isIdentity = n: n.d._htag == "boot-inl";
  isLeaf     = n: n.d._htag == "boot-inr" && n.d.term._htag == "boot-inl";

  # `qAppend Eff Resp X A l r` — concatenate two queues. Identity
  # short-circuits on either side mirror `queue.nix:append`.
  qAppend = Eff: Resp: X: A: l: r:
    if l.d._htag == "boot-inl" then r
    else if r.d._htag == "boot-inl" then l
    else qNode Eff Resp X A l r;

  # `qApp Eff Resp X A q x` — apply queue `q` to value `x : Hoas X`.
  # Streams the tree traversal and leaf-application in a single
  # `genericClosure` pass: the right-subtree stack is an attrset
  # linked-list (`{ top; rest } | null`), so push/pop are O(1) and
  # total memory is O(N) — Nix's vector `++` would otherwise force
  # an O(N²) copy chain on each push. Leaf application happens
  # in-line; no intermediate Nix list of leaf fns is built.
  #
  # State per step: `{ key; _current; _stack; _val; _halt; _impure }`.
  #  - `_current` is the queue node currently focused.
  #  - `_stack` is the linked-list of pending right-subtrees.
  #  - `_val` is the running value piped through Pure leaves.
  #  - `_halt = true` signals genericClosure to stop on the next call.
  #  - `_impure` is `null` (pure path) or the Impure result carrying
  #    `{ op; innerQueue }` that needs splicing with the residual
  #    `_stack`.
  #
  # The Impure splice converts the residual stack back into a queue
  # via `stackToQueue` (right-leaning fold of `qAppend`) — type
  # indices are not tracked at the HOAS layer; conv is unaffected.
  qApp = Eff: Resp: X: A:
    # Memoise (Eff, Resp, A)-only partial applications so the inner
    # carrier chain inside `pure` / `impureCon` and the (Eff, Resp, A, A)
    # carrier chain inside `qIdentity` / `qNode` is shared across every
    # qApp invocation with these indices.
    let
      pure_RA  = pure Eff Resp A;
      imp_RA   = impureCon Eff Resp A;
      qId_RAA  = qIdentity Eff Resp A A;
      qNode_RAA = qNode Eff Resp A A;
    in q: x:
    if isIdentity q
    then pure_RA x
    else
      let
        push = top: rest: { inherit top rest; };
        # `stackToQueue` converts the residual right-subtree stack
        # into a queue when the streaming traversal halts mid-flight
        # on an Impure leaf. The stack is L→R visit-order from `top`
        # outwards, so a left-fold with `qAppend` (which is queue-
        # concatenation) reconstructs the correct queue shape. We use
        # `genericClosure` rather than a recursive walk so a 10K-deep
        # residual stack doesn't blow the host stack — same reason
        # `qApp` itself is iterative.
        # Build a RIGHT-leaning queue from the residual stack:
        #   qNode top1 (qNode top2 (… (qNode topN qIdentity))).
        # The earlier left-leaning `qAppend`-fold was O(N²) over an
        # N-effect bind chain: each `run` iteration's residual stack
        # had length (N-i), and rebuilding via qAppend allocated
        # (N-i) qNodes each time → Σᵢ(N-i) = O(N²) qNode allocations.
        # Right-leaning rebuild is O(N) at iteration 1; every later
        # iteration's residual stack is length 1 (the inner right-
        # subtree of the prior rebuild) → the s0.rest == null short-
        # circuit returns it as-is with no new allocations. Net:
        # O(N) total qNode allocations across the whole run.
        #
        # Two genericClosure passes — reverse the stack to a linked
        # list with `topN` at the head, then foldl `qNode item acc`
        # from that head. Both passes are host-stack-safe regardless
        # of stack depth.
        stackToQueue = s0:
          if s0 == null then qId_RAA
          else if s0.rest == null then s0.top
          else
            let
              reversed = builtins.genericClosure {
                startSet = [{ key = 0; _src = s0; _rev = null; }];
                operator = st:
                  if st._src == null then []
                  else [{
                    key = st.key + 1;
                    _src = st._src.rest;
                    _rev = { top = st._src.top; rest = st._rev; };
                  }];
              };
              reversedStack = (lib.last reversed)._rev;
              build = builtins.genericClosure {
                startSet = [{
                  key = 0;
                  _node = reversedStack;
                  _acc = qId_RAA;
                }];
                operator = st:
                  if st._node == null then []
                  else [{
                    key = st.key + 1;
                    _node = st._node.rest;
                    _acc = qNode_RAA st._node.top st._acc;
                  }];
              };
            in (lib.last build)._acc;

        steps = builtins.genericClosure {
          startSet = [{
            key = 0;
            _current = q;
            _stack = null;
            _val = x;
            _halt = false;
            _impure = null;
          }];
          operator = s:
            if s._halt then []
            else if isIdentity s._current then
              # Pop one right-subtree off the stack, or halt if empty.
              # `deepSeq s._val` into the key forces the running value
              # along its pass-through hop, breaking the thunk chain
              # described above the descent branch.
              if s._stack == null
              then [{
                key = builtins.deepSeq s._val (s.key + 1);
                _current = s._current;
                _stack = null;
                _val = s._val;
                _halt = true;
                _impure = null;
              }]
              else [{
                key = builtins.deepSeq s._val (s.key + 1);
                _current = s._stack.top;
                _stack = s._stack.rest;
                _val = s._val;
                _halt = false;
                _impure = null;
              }]
            else if isLeaf s._current then
              let
                fn = s._current.d.term.term.fst;
                r  = fn.body s._val;
              in if r.d._htag == "boot-inl"
                 then
                   # Pure: pipe `r.d.term.fst` to the next leaf, or
                   # halt if no more pending right-subtrees. `deepSeq`
                   # the running value into the key to break thunk
                   # chains through pureCon-returning continuations.
                   if s._stack == null
                   then [{
                     key = builtins.deepSeq r.d.term.fst (s.key + 1);
                     _current = s._current;
                     _stack = null;
                     _val = r.d.term.fst;
                     _halt = true;
                     _impure = null;
                   }]
                   else [{
                     key = builtins.deepSeq r.d.term.fst (s.key + 1);
                     _current = s._stack.top;
                     _stack = s._stack.rest;
                     _val = r.d.term.fst;
                     _halt = false;
                     _impure = null;
                   }]
                 else
                   # Impure: halt with `r` for splicing. `deepSeq s._val`
                   # is unnecessary at halt — but cheap and keeps the pin
                   # discipline uniform across all _val pass-throughs.
                   [{
                     key = builtins.deepSeq s._val (s.key + 1);
                     _current = s._current;
                     _stack = s._stack;
                     _val = s._val;
                     _halt = true;
                     _impure = r;
                   }]
            else
              # Node: descend into left, push right onto stack.
              # `_val = s._val` passes the running value through unchanged
              # during the entire descent phase. Without forcing it here,
              # an N-deep left-leaning queue builds an N-long `_val`
              # thunk chain (state_k._val ↦ state_{k-1}._val ↦ …); at
              # apply-time the first force recurses N levels on the host
              # C stack and overflows at N ≳ 175K. `deepSeq s._val` into
              # the key keeps `_val` flat across every step. Same pin
              # discipline as the leaf-Pure branch's `r.d.term.fst` pin.
              let
                l = s._current.d.term.term.fst;
                r = s._current.d.term.term.snd.fst;
              in [{
                key = builtins.deepSeq s._val (s.key + 1);
                _current = l;
                _stack = push r s._stack;
                _val = s._val;
                _halt = false;
                _impure = null;
              }];
        };
        final = lib.last steps;
      in
        if final._impure == null
        then pure_RA final._val
        else
          let
            result  = final._impure;
            innerOp = result.d.term.fst;
            innerQ  = result.d.term.snd.fst;
            innerX  = H.app Resp innerOp;
            tailQ   = stackToQueue final._stack;
          in imp_RA innerOp
               (qAppend Eff Resp innerX A innerQ tailQ);

  # ---- interpreter -----------------------------------------------------

  # `run Eff Resp A handlers prog initialState` — drive `prog` to
  # completion. Returns `{ value : Hoas A; state : <opaque>; }`.
  # `handlers : { param : Hoas Eff, state } -> { resume? | abort?; state }`.
  # `resume` is a `Hoas (Resp op)` that gets piped through the
  # continuation queue. `abort` is a `Hoas A` that bypasses the queue
  # and becomes the final value. State is `deepSeq`-forced into the
  # worklist key per step to break thunk chains (mirror of
  # `src/trampoline.nix:124`).
  run = Eff: Resp: A:
    # Memoise `pure Eff Resp A` once per `run E R A` partial application
    # so the abort branch's `pure_RA result.abort` skips the (Eff,Resp,A)
    # carrier chain on every iteration.
    let pure_RA = pure Eff Resp A;
    in handlers: prog: initialState:
    let
      steps = builtins.genericClosure {
        startSet = [{ key = 0; _comp = prog; _state = initialState; }];
        operator = step:
          if step._comp.d._htag == "boot-inl"
          then []
          else
            let
              op = step._comp.d.term.fst;
              q  = step._comp.d.term.snd.fst;
              X  = H.app Resp op;
              result = handlers { param = op; state = step._state; };
              newState =
                if result ? state then result.state
                else throw "experimental.descInterp.run: handler return must include 'state'";
              k = builtins.deepSeq newState (step.key + 1);
            in
              if result ? abort then
                [{
                  key = k;
                  _comp = pure_RA result.abort;
                  _state = newState;
                }]
              else if result ? resume then
                [{
                  key = k;
                  _comp = qApp Eff Resp X A q result.resume;
                  _state = newState;
                }]
              else
                throw "experimental.descInterp.run: handler must return { resume; state; } or { abort; state; }";
      };
      final = lib.last steps;
    in {
      value = final._comp.d.term.fst;
      state = final._state;
    };

  # `handle Eff Resp A { return?; handlers; state? } prog` — thin
  # wrapper over `run` with a custom `return` clause folded over the
  # final `(value, state)` pair. Mirrors `src/trampoline.nix:handle`.
  handle = Eff: Resp: A:
    { return ? (v: s: { value = v; state = s; }),
      handlers,
      state ? null,
    }: prog:
      let r = run Eff Resp A handlers prog state;
      in return r.value r.state;

  # ---- test fixtures ---------------------------------------------------

  testEff  = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);

  # Let-bind the partial applications so leaf-fn invocations like
  # `(x: pureN (x.value + 1))` share the memoised (Eff, Resp, A) carrier
  # chain across all calls. The `pure_T_R_N` thunk is forced exactly
  # once across an N-leaf chain; without this binding every leaf
  # invocation rebuilds the chain.
  pure_T_R_N   = pure testEff testResp H.nat;
  bind_T_R_N_N = bind testEff testResp H.nat H.nat;

  pureN  = v: pure_T_R_N (H.intLit v);
  sendT  = send testEff testResp H.true_;
  bindNN = bind_T_R_N_N;
  idK    = pure_T_R_N;

  runNN  = run testEff testResp H.nat;
  qAppNN = qApp testEff testResp H.nat H.nat;

  # Constant handler: every op returns `resume = H.intLit r`; state
  # passes through unchanged. The simplest useful handler shape.
  constHandler = r: { param, state }: { resume = H.intLit r; inherit state; };

  # Counting handler: increments a Nix-level counter in `state` on
  # every effect, returns `resume = H.intLit (state + 1)`.
  countHandler = { param, state }: {
    resume = H.intLit (state + 1);
    state  = state + 1;
  };

in {
  inherit qAppend qApp run handle;

  __docs = {
    qApp = {
      description = "qApp Eff Resp X A q x — apply queue `q` to value `x`; trampolines Pure-returning leaves via genericClosure; on Impure splices the inner queue with the remaining tail.";
      signature = "qApp : Hoas U -> Hoas (U -> U) -> Hoas U -> Hoas U -> Hoas (μ kontQueueApp Eff Resp X A) -> Hoas X -> Hoas (μ freeFxApp Eff Resp A)";
      tests = {
        "qApp-on-qIdentity-returns-pure" = {
          # qIdentity short-circuit: qApp qId x = pure x.
          expr =
            let q = qIdentity testEff testResp H.nat H.nat;
                r = qAppNN q (H.intLit 7);
            in { tag = r.d._htag; v = r.d.term.fst.value; };
          expected = { tag = "boot-inl"; v = 7; };
        };

        "qApp-on-qLeaf-applies-fn-once" = {
          # qLeaf carrying `idK` resumes to `pure x`.
          expr =
            let q = qLeaf testEff testResp H.nat H.nat
                     (H.lam "_x" H.nat (x: idK x));
                r = qAppNN q (H.intLit 3);
            in { tag = r.d._htag; v = r.d.term.fst.value; };
          expected = { tag = "boot-inl"; v = 3; };
        };

        "qApp-on-qNode-chains-leaves" = {
          # qNode (qLeaf addOne) (qLeaf addTen) applied to x rotates
          # left-leaningly: first add 1, then add 10. Both leaves are
          # Pure-returning, so qApp iterates and final pure carries
          # x + 11.
          expr =
            let
              addOne = H.lam "_x" H.nat (x: pureN (x.value + 1));
              addTen = H.lam "_x" H.nat (x: pureN (x.value + 10));
              l = qLeaf testEff testResp H.nat H.nat addOne;
              r = qLeaf testEff testResp H.nat H.nat addTen;
              q = qNode testEff testResp H.nat H.nat l r;
              out = qAppNN q (H.intLit 5);
            in { tag = out.d._htag; v = out.d.term.fst.value; };
          expected = { tag = "boot-inl"; v = 16; };
        };

        "qApp-deep-pure-chain-10K" = {
          # Build a left-leaning Node tree of 10K Pure-returning leaves
          # via qSnoc; apply to 0. Each leaf adds 1. Final value is
          # 10000. The streaming `qApp` walks the tree via a single
          # genericClosure with an O(1)-push linked-list stack, so RAM
          # stays linear in N (≈4–5 KB per leaf) — a vector-list
          # `++`-based stack would blow up O(N²).
          expr =
            let
              n = 10000;
              q0 = qIdentity testEff testResp H.nat H.nat;
              q  = builtins.foldl'
                     (acc: _: qSnoc testEff testResp
                                H.nat H.nat H.nat acc
                                (x: pureN (x.value + 1)))
                     q0
                     (builtins.genList (i: i) n);
              out = qAppNN q (H.intLit 0);
            in (builtins.tryEval
                  (builtins.seq out.d.term.fst.value true)).success;
          expected = true;
        };
      };
    };

    run = {
      description = "run Eff Resp A handlers prog initialState — drive `prog : μ(freeFxApp Eff Resp A)` to completion via a `genericClosure` worklist; handlers dispatch on the HOAS op value and return `{ resume | abort; state }`.";
      signature = "run : Hoas U -> Hoas (U -> U) -> Hoas U -> ({ param, state } -> { resume? | abort?, state }) -> Hoas (μ freeFxApp Eff Resp A) -> State -> { value : Hoas A, state : State }";
      tests = {
        "run-on-pure-returns-value" = {
          # Pure program — handlers never invoked; final value is the
          # wrapped HOAS lit, state unchanged.
          expr =
            let r = runNN (_: throw "handler unreachable") (pureN 42) null;
            in { v = r.value.value; s = r.state; };
          expected = { v = 42; s = null; };
        };

        "run-on-send-applies-handler" = {
          # Single effect: handler returns resume = 99; queue is
          # qIdentity so qApp short-circuits to pure resume.
          expr =
            let r = runNN (constHandler 99) sendT null;
            in r.value.value;
          expected = 99;
        };

        "run-bind-once-pipes-through-handler" = {
          # bind sendT (x: pureN (x + 1)) — handler returns resume=5;
          # queue is qLeaf wrapping the addOne fn; result is 6.
          expr =
            let
              prog = bindNN sendT (x: pureN (x.value + 1));
              r = runNN (constHandler 5) prog null;
            in r.value.value;
          expected = 6;
        };

        "run-bind-twice-pipes-through-queue" = {
          # Two binds = qNode(qLeaf addOne, qLeaf addTen). qApp walks
          # the rotation: 5 + 1 = 6, then 6 + 10 = 16.
          expr =
            let
              prog = bindNN
                       (bindNN sendT (x: pureN (x.value + 1)))
                       (y: pureN (y.value + 10));
              r = runNN (constHandler 5) prog null;
            in r.value.value;
          expected = 16;
        };

        "run-abort-discards-continuation" = {
          # Handler returns abort = H.intLit 999. The bind-attached
          # continuation `(_: pureN 0)` is discarded; final value is
          # 999.
          expr =
            let
              prog = bindNN sendT (_: pureN 0);
              r = runNN ({ param, state }: {
                    abort = H.intLit 999; inherit state;
                  }) prog null;
            in r.value.value;
          expected = 999;
        };

        "run-threads-state-through-handler" = {
          # countHandler increments state on each effect. 3 binds =
          # 3 effects (each `_: sendT` re-emits the op); final state
          # = 3 and final value = state at the final effect = 3.
          expr =
            let
              prog = bindNN (bindNN sendT (_: sendT)) (_: sendT);
              r = run testEff testResp H.nat countHandler prog 0;
            in { v = r.value.value; s = r.state; };
          expected = { v = 3; s = 3; };
        };

        "run-deep-bind-10K" = {
          # 10K-deep bind chain on a send-then-pure loop. The single
          # send at the head emits one effect; qApp then walks 10K
          # Pure-returning leaves to thread the result through the
          # continuation queue. Both the run worklist and qApp's
          # internal traversal use genericClosure with linked-list
          # stacks — host stack is O(1), heap is O(N).
          expr =
            let
              n = 10000;
              prog = builtins.foldl'
                       (acc: _: bindNN acc (x: pureN (x.value + 1)))
                       sendT
                       (builtins.genList (i: i) n);
              r = runNN (constHandler 0) prog null;
            in r.value.value;
          expected = 10000;
        };

        "run-deepseq-state-thunk-pinned" = {
          # Regression-pin the `builtins.deepSeq newState (key + 1)`
          # discipline in `run`. State = integer counter; without the
          # pin, after N handler invocations `r.state` is a depth-N
          # `(((0+1)+1)+…)+1` thunk whose force overflows the host
          # stack (Nix ceiling ≈ 5–8K). With the pin every snapshot's
          # state is forced flat → O(1) per step, O(1) final force.
          #
          # The bind chain is built RIGHT-leaning via genericClosure
          # — `bind sendT (_: bind sendT (_: …))`. Each program holds
          # exactly one Impure node; `run` peels one effect per
          # iteration; `qApp` finishes in O(1) with an empty residual
          # stack, so the O(N²) `stackToQueue` splice path is never
          # entered. Left-leaning equivalents OOM the host at N≥3K
          # because every leaf returning `sendT` rebuilds a shrinking
          # N-deep queue on every iteration.
          expr =
            let
              n = 10000;
              buildChain = builtins.genericClosure {
                startSet = [{ key = 0; _prog = pureN 0; }];
                operator = s:
                  if s.key >= n then []
                  else [{
                    key = s.key + 1;
                    _prog = bindNN sendT (_: s._prog);
                  }];
              };
              prog = (lib.last buildChain)._prog;
              h = { param, state }: {
                resume = H.intLit state;
                state  = state + 1;
              };
              r = runNN h prog 0;
            in (builtins.tryEval (builtins.seq r.state true)).success;
          expected = true;
        };

        # ----- Observational equivalence: monad laws (ii)/(iii) on
        # Impure m. These are exactly the equalities the kernel's
        # `deepEqualDesc` cannot witness — they hold under `run` with
        # any handler because `qApp` collapses the queue's tree shape
        # to a sequence of value-applications. Closes the open
        # equality boundary documented in `kernel.nix`.
        "obs-eq-law-ii-on-impure-sendT" = {
          # bind sendT pure == sendT (observationally) — under run
          # with constHandler 7, both sides yield 7.
          expr =
            let
              lhs = bindNN sendT (x: pure testEff testResp H.nat x);
              rhs = sendT;
              vL = (runNN (constHandler 7) lhs null).value.value;
              vR = (runNN (constHandler 7) rhs null).value.value;
            in { lhs = vL; rhs = vR; equal = vL == vR; };
          expected = { lhs = 7; rhs = 7; equal = true; };
        };

        "obs-eq-law-iii-on-impure-sendT" = {
          # bind (bind sendT f) g == bind sendT (x: bind (f x) g)
          # f = (x: pureN (x + 1)); g = (y: pureN (y * 10)).
          # Both sides: handler returns 5; (5+1)*10 = 60.
          expr =
            let
              f = x: pureN (x.value + 1);
              g = y: pureN (y.value * 10);
              lhs = bindNN (bindNN sendT f) g;
              rhs = bindNN sendT (x: bindNN (f x) g);
              vL = (runNN (constHandler 5) lhs null).value.value;
              vR = (runNN (constHandler 5) rhs null).value.value;
            in { lhs = vL; rhs = vR; equal = vL == vR; };
          expected = { lhs = 60; rhs = 60; equal = true; };
        };
      };
    };

    handle = {
      description = "handle Eff Resp A { return?; handlers; state? } prog — thin wrapper over `run` with a custom `return` clause folding the final (value, state) pair; mirrors `nix-effects/src/trampoline.nix:handle` at the description layer.";
      signature = "handle : Hoas U -> Hoas (U -> U) -> Hoas U -> { return?, handlers, state? } -> Hoas (μ freeFxApp Eff Resp A) -> b";
      tests = {
        "handle-with-default-return" = {
          # Default return is identity-as-pair. Result is { value;
          # state } with HOAS value, raw state.
          expr =
            let
              r = handle testEff testResp H.nat
                    { handlers = constHandler 21; }
                    sendT;
            in { v = r.value.value; s = r.state; };
          expected = { v = 21; s = null; };
        };

        "handle-with-custom-return-doubles" = {
          # Custom return: doubles the Nix-level value extracted from
          # the HOAS literal, drops state.
          expr =
            handle testEff testResp H.nat
              {
                return = v: _s: v.value * 2;
                handlers = constHandler 21;
              }
              sendT;
          expected = 42;
        };
      };
    };
  };
}
