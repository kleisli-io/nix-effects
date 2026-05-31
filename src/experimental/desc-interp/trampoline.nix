# Trampolined interpreter for FreeFx descriptions — `run` / `handle`
# drive `μ(freeFxApp Eff Resp A)` programs to completion via
# `builtins.genericClosure`, dispatching effects through a kernel-
# resident handler term + Nix-side dispatch interpreter. The
# continuation queue inside each Impure node is walked by `qApp`,
# which itself uses `genericClosure` to keep host stack depth at
# O(1) regardless of queue size.
#
# Runtime-bridge architecture (per-effect handler shape).
#   Caller supplies `{ handler; dispatch }`:
#     handler  : HOAS term `Π(op:Eff). Π(_s:State). ResultTy`.
#     dispatch : `{ op; outputVal; state } -> { action; newState;
#                response?; value?; error? }`, `action ∈ {"resume",
#                "abort", "throw"}`.
#   Per Impure node `op` is elab'd+eval'd and `handler` applied to
#   `(opVal, stateVal)`; `outputVal` plus HOAS `op` and prior `state`
#   feed `dispatch`. Smart-constructor sidecars (e.g. `_opTag`,
#   `payload` on `op`) survive `kernel.send`'s `impureCon` wrap, so
#   `dispatch` can be parameterised by per-op Nix-host data.
#   Initial state is elab'd+eval'd iff it carries `_htag`; otherwise
#   threaded verbatim — handlers that ignore `_s` accept any carrier.
#
# Operational shape mirrors `nix/nix-effects/src/queue.nix:qApp` and
# `nix/nix-effects/src/trampoline.nix:interpret`. Differences:
#  - Programs are `μ(freeFxApp …)` values, not the production
#    `Pure`/`Impure` records. Pure/Impure are decided by the outer
#    plus tag (`m.d._htag`).
#  - The queue is `μI U² (kontQueueApp …)` at the indexed slice, not a
#    sumtype attrset. Leaves store HOAS lams; their `.body` field is
#    the underlying Nix function used for meta-level beta
#    (`leafFn.body x`). Each queue value carries an `_index = { X; A; }`
#    Nix-meta sidecar; qApp / qAppend / stackToQueue read this rather
#    than threading (X, A) ghost parameters.
#  - Ops are HOAS values of type `Eff` (no synthetic `.name`/`.param`
#    fields). The handler is a kernel TERM dispatching on the op via
#    the effect's elim, paired with a Nix-side dispatch interpreter
#    that turns the kernel-eval'd return value into a step decision.
#
# Refs: Kiselyov & Ishii (Haskell'15) §3.1; Chapman/Dagand/McBride/
# Morris (ICFP'10) §6 indexed descriptions; Plotkin & Pretnar (2009)
# for the resume/abort encoding; Gibbons (2021) on associativity-as-
# precondition for accumulating worklists.
{ fx, lib, api, ... }:
let
  H = fx.tc.hoas;
  HII = H._internal._indexed;
  G = fx.tc.generic.desc;
  D = fx.experimental.desc-interp.desc;
  K = fx.experimental.desc-interp.kernel;
  Elab = fx.tc.elaborate;

  inherit (D) impureCon qIdentity qLeaf qNode;
  inherit (K) pure send bind qSnoc;

  # `pinVal v` forces the outer WHNF marker plus payload scalar of a
  # running value, returning `v.value or 0` (so callers can `seq` it).
  # HOAS carriers expose `._htag` (+ `.value` for lits); kernel `Val`s
  # expose `.tag`. Fallbacks let Nix-side carriers (e.g. raw attrsets
  # used as `state` by some handlers) pass through harmlessly.
  # Limited to scalar fields — never walks closure environments, since
  # `Val.right.closure` and friends are shared cyclically with their
  # carrier descriptions and overflow under `deepSeq`. Used by `qApp`
  # to break the N-deep `_val` thunk chain across the queue walk, and
  # by `run` to break the analogous N-deep `_state` chain across the
  # outer Impure-step loop.
  pinVal = v: builtins.seq (v.tag or v._htag or 0) (v.value or 0);

  freeLevelTm = H.levelSuc H.levelZero;
  lowerFreeField = A: x:
    if builtins.isAttrs x
      && (x._htag or null) == "lift-intro"
      && (x.l or null) == H.levelZero
      && (x.m or null) == freeLevelTm
      && x ? a
    then x.a
    else HII.lowerAt H.levelZero freeLevelTm A x;

  # ---- queue traversal -------------------------------------------------

  # Node-tag predicates on `μI U² (kontQueueApp …)` values.
  isIdentity = n: n.d._htag == "boot-inl";
  isLeaf = n: n.d._htag == "boot-inr" && n.d.term._htag == "boot-inl";

  # `qAppend Eff Resp l r` — concatenate two queues. Each child carries
  # its own `_index` sidecar, and `qNode` enforces the seam
  # `l._index.A = r._index.X` via Nix-level equality. Identity
  # short-circuits on either side mirror `queue.nix:append`.
  qAppend = Eff: Resp: l: r:
    if l.d._htag == "boot-inl" then r
    else if r.d._htag == "boot-inl" then l
    else qNode Eff Resp l r;

  # `qApp Eff Resp q x` — apply queue `q` to value `x : Hoas q._index.X`.
  # The queue's `_index` sidecar carries the (X, A) indexing that the
  # kernel's μI U² slot witnesses. Streams the tree traversal and
  # leaf-application in a single `genericClosure` pass: the right-
  # subtree stack is an attrset linked-list (`{ top; rest } | null`), so
  # push/pop are O(1) and total memory is O(N) — Nix's vector `++` would
  # otherwise force an O(N²) copy chain on each push. Leaf application
  # happens in-line; no intermediate Nix list of leaf fns is built.
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
  # The Impure splice converts the residual stack back into a queue via
  # `stackToQueue` (right-leaning fold of `qAppend`); seam alignment
  # is preserved by `qNode`'s sidecar assertion on each new node.
  #
  # Without the `pinVal` forcing inside the genericClosure key,
  # intLit-carrying chains (e.g. `pureN (x.value + 1)` accumulators)
  # build an N-deep `value` thunk that the final read unwinds on the
  # host C stack. See the module-level `pinVal` definition for the
  # forcing discipline.
  qApp = Eff: Resp:
    let
      qNode_R = qNode Eff Resp;
    in
    q: x:
      # Memoise the (Eff, Resp, A)-dependent closures inside the q-x
      # body. A comes from `q._index.A`, so it cannot be baked at the
      # outer curry layer; the let-binds below share pure_RA, imp_RA,
      # and qId_RAA across every iteration of this qApp call's
      # genericClosure pass.
      let
        Av = q._index.A;
        pure_RA = pure Eff Resp Av;
        imp_RA = impureCon Eff Resp Av;
        qId_RAA = qIdentity Eff Resp Av;
      in
      if isIdentity q
      then pure_RA x
      else
        let
          push = top: rest: { inherit top rest; };
          # `stackToQueue` converts the residual right-subtree stack
          # into a queue when the streaming traversal halts mid-flight
          # on an Impure leaf. The stack is L→R visit-order from `top`
          # outwards, so a right-leaning rebuild of qNode applications
          # reconstructs the correct queue shape. We use
          # `genericClosure` rather than a recursive walk so a 10K-deep
          # residual stack doesn't blow the host stack — same reason
          # `qApp` itself is iterative.
          # Build a right-leaning queue from the residual stack:
          #   qNode top1 (qNode top2 (… (qNode topN qIdentity))).
          # This is O(N) across the whole run: the first rebuild is linear,
          # and later residual stacks collapse through the `s0.rest == null`
          # shortcut.
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
                    if st._src == null then [ ]
                    else [{
                      key = st.key + 1;
                      _src = st._src.rest;
                      _rev = { top = st._src.top; rest = st._rev; };
                    }];
                };
                reversedStack = (lib.last reversed)._rev;
                # Per-step `seq newAcc (st.key + 1)` forces each newly-built
                # qNode to WHNF, which forces its seamOk check
                # (`l._index.A == r._index.X`) eagerly. Without this, the
                # accumulator stays as a lazy thunk chain; the FINAL force
                # at `(lib.last build)._acc` then unwinds it on the host
                # C stack — qNode_N's seamOk forces qNode_{N-1}'s WHNF
                # which forces qNode_{N-1}'s seamOk, etc., overflowing at
                # N ≳ 10K. Forcing per step means each iteration reads
                # its `r._index.X` from a WHNF prior accumulator: O(1)
                # per step instead of O(N) at the end.
                build = builtins.genericClosure {
                  startSet = [{
                    key = 0;
                    _node = reversedStack;
                    _acc = qId_RAA;
                  }];
                  operator = st:
                    if st._node == null then [ ]
                    else
                      let newAcc = qNode_R st._node.top st._acc; in
                      [{
                        key = builtins.seq newAcc (st.key + 1);
                        _node = st._node.rest;
                        _acc = newAcc;
                      }];
                };
              in
              (lib.last build)._acc;

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
              if s._halt then [ ]
              else if isIdentity s._current then
              # Pop one right-subtree off the stack, or halt if empty.
              # `seq (pinVal s._val)` into the key forces the running
              # value to WHNF, breaking the thunk chain described above
              # the descent branch without walking into closure envs.
                if s._stack == null
                then [{
                  key = builtins.seq (pinVal s._val) (s.key + 1);
                  _current = s._current;
                  _stack = null;
                  _val = s._val;
                  _halt = true;
                  _impure = null;
                }]
                else [{
                  key = builtins.seq (pinVal s._val) (s.key + 1);
                  _current = s._stack.top;
                  _stack = s._stack.rest;
                  _val = s._val;
                  _halt = false;
                  _impure = null;
                }]
              else if isLeaf s._current then
              # qLeaf payload layout: `descArgAt(X) ∘ descArgAt(A) ∘
              # descArg(fn) ∘ retI` produces `(X, (A, (fn, refl)))` at
              # `.d.term.term` (where `.d.term` is the bootInr-of-inner-
              # plus selector). The fn sits at `.d.term.term.snd.snd.fst`.
                let
                  fn = s._current.d.term.term.snd.snd.fst;
                  r = fn.body s._val;
                  nextVal = lowerFreeField s._current._index.A r.d.term.fst;
                in
                if r.d._htag == "boot-inl"
                then
                # Pure: pipe `r.d.term.fst` to the next leaf, or
                # halt if no more pending right-subtrees. WHNF-pin
                # the running value into the key to break thunk
                # chains through pureCon-returning continuations.
                  if s._stack == null
                  then [{
                    key = builtins.seq (pinVal nextVal) (s.key + 1);
                    _current = s._current;
                    _stack = null;
                    _val = nextVal;
                    _halt = true;
                    _impure = null;
                  }]
                  else [{
                    key = builtins.seq (pinVal nextVal) (s.key + 1);
                    _current = s._stack.top;
                    _stack = s._stack.rest;
                    _val = nextVal;
                    _halt = false;
                    _impure = null;
                  }]
                else
                # Impure: halt with `r` for splicing. The WHNF pin is
                # unnecessary at halt — but cheap and keeps the pin
                # discipline uniform across all _val pass-throughs.
                  [{
                    key = builtins.seq (pinVal s._val) (s.key + 1);
                    _current = s._current;
                    _stack = s._stack;
                    _val = s._val;
                    _halt = true;
                    _impure = r;
                  }]
              else
              # Node: descend into left, push right onto stack.
              # qNode payload layout: `descArgAt(X) ∘ descArgAt(M) ∘
              # descArgAt(A) ∘ recI(l) ∘ recI(r) ∘ retI` produces
              # `(X, (M, (A, (l, (r, refl)))))` at `.d.term.term`. The
              # recursive children l and r sit at
              # `.d.term.term.snd.snd.snd.fst` (l) and
              # `.d.term.term.snd.snd.snd.snd.fst` (r).
              #
              # `_val = s._val` passes the running value through unchanged
              # during the entire descent phase. Without forcing it here,
              # an N-deep left-leaning queue builds an N-long `_val`
              # thunk chain (state_k._val ↦ state_{k-1}._val ↦ …); at
              # apply-time the first force recurses N levels on the host
              # C stack and overflows at N ≳ 175K. `seq (pinVal s._val)`
              # into the key forces the value to WHNF, flattening the
              # chain without walking into kernel-Val closure envs.
              # Same pin discipline as the leaf-Pure branch's
              # `r.d.term.fst` pin.
                let
                  l = s._current.d.term.term.snd.snd.snd.fst;
                  r = s._current.d.term.term.snd.snd.snd.snd.fst;
                in
                [{
                  key = builtins.seq (pinVal s._val) (s.key + 1);
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
            result = final._impure;
            innerOp = lowerFreeField Eff result.d.term.fst;
            innerQ = result.d.term.snd.fst;
            tailQ = stackToQueue final._stack;
          in
          imp_RA innerOp
            (qAppend Eff Resp innerQ tailQ);

  # ---- interpreter -----------------------------------------------------

  # `run Eff Resp A { handler; dispatch } prog initialState` — drive
  # `prog` to completion via the bridge architecture documented at the
  # top of this file. Returns `{ value; state }`.
  #
  # `seq (pinVal newState)` breaks the N-deep `_state` thunk chain that
  # otherwise builds across iterations: `newState` for step k is the
  # kernel `vApp` output threading step (k-1)'s state, so without an
  # interior-scalar force the `.value` payload accumulates an O(N)
  # closure chain that the final read unwinds on the host C stack.
  # Mirror of the pin at `src/trampoline.nix:124`.
  run = Eff: Resp: A:
    # Memoise `pure Eff Resp A` once per `run E R A` partial application
    # so the abort branch's `pure_RA decision.value` skips the
    # (Eff,Resp,A) carrier chain on every iteration. Also memoise
    # `qApp Eff Resp` — the inner (Eff, Resp)-keyed closure is shared
    # across every Impure-step's queue traversal.
    let
      pure_RA = pure Eff Resp A;
      qApp_R = qApp Eff Resp;
    in
    { handler, dispatch, evalOp ? null, handlerShortcut ? null }:
    prog: initialState:
      let
        handlerCore = fx.tc.eval.eval [ ] (H.elab handler);
        # Per-Impure `op → Val` translation. Effect modules may supply a
        # memoised `evalOp` (e.g. tag-keyed precomputed Vals for canonical
        # op constructors); when absent, fall back to the generic elab+eval
        # path that walks the HOAS op on every step.
        evalOp_ =
          if evalOp == null
          then op: fx.tc.eval.eval [ ] (H.elab op)
          else evalOp;
        # HOAS state elab+evals to a Val; Nix-side state (e.g. runElab's
        # Δ attrset) is threaded verbatim. `vAppF` never inspects its
        # arg, so handlers that ignore `_s` accept any carrier.
        initStateVal =
          if initialState ? _htag
          then fx.tc.eval.eval [ ] (H.elab initialState)
          else initialState;
        steps = builtins.genericClosure {
          startSet = [{ key = 0; _comp = prog; _state = initStateVal; }];
          operator = step:
            if step._comp.d._htag == "boot-inl"
            then [ ]
            else
              let
                op = lowerFreeField Eff step._comp.d.term.fst;
                q = step._comp.d.term.snd.fst;
                # `handlerShortcut op stateVal` — partial-evaluation
                # residual for `handle_X op s` certified by per-effect
                # H.refl lemma (`<effect>-shortcut-laws.nix`) + emitter
                # conv soundness (`extract.nix`). Returns the same Val
                # the kernel path would produce; returns `null` for
                # untagged ops (falling back to the kernel handler).
                shortVal =
                  if handlerShortcut == null then null
                  else handlerShortcut op step._state;
                outputVal =
                  if shortVal != null then shortVal
                  else
                    fx.tc.eval.vApp (fx.tc.eval.vApp handlerCore (evalOp_ op))
                      step._state;
                decision = dispatch {
                  inherit op outputVal;
                  state = step._state;
                };
                newState = decision.newState;
                k = builtins.seq (pinVal newState) (step.key + 1);
              in
              if decision.action == "resume" then [{
                key = k;
                _comp = qApp_R q decision.response;
                _state = newState;
              }]
              else if decision.action == "abort" then [{
                key = k;
                _comp = pure_RA decision.value;
                _state = newState;
              }]
              else if decision.action == "throw" then
                throw
                  ("experimental.descInterp.run: handler threw at op "
                    + "tag '${op._htag or "<unknown>"}' "
                    + "(newState tag '${newState.tag or "<unknown>"}')")
              else throw "experimental.descInterp.run: unknown dispatch action '${decision.action}'";
        };
        final = lib.last steps;
      in
      {
        value = lowerFreeField A final._comp.d.term.fst;
        # Force the state slot: `put` leaves it a VThunkTm that `pinVal`
        # won't unwrap. The value slot stays lazy — `run` is shared with
        # elaboration, whose value can be a meta-bearing thunk the kernel
        # `forceVal` must not touch.
        state = fx.tc.eval.forceVal final._state;
      };

  # `handle Eff Resp A { return?; handler; dispatch; state?; evalOp?;
  # handlerShortcut? } prog` — thin wrapper over `run` with a custom
  # `return` clause folded over the final `(value, state)` pair.
  # `evalOp` and `handlerShortcut` (both optional) thread through to
  # `run` for the tag-keyed per-Impure fast paths. Mirrors
  # `src/trampoline.nix:handle`.
  handle = Eff: Resp: A:
    { return ? (v: s: { value = v; state = s; })
    , handler
    , dispatch
    , state
    , evalOp ? null
    , handlerShortcut ? null
    ,
    }: prog:
      let
        r = run Eff Resp A
          { inherit handler dispatch evalOp handlerShortcut; }
          prog
          state;
      in
      return r.value r.state;

  # ---- test fixtures ---------------------------------------------------

  testEff = H.bool;
  testResp = H.lam "_" H.bool (_: H.nat);

  # Let-bind the partial applications so leaf-fn invocations like
  # `(x: pureN (x.value + 1))` share the memoised (Eff, Resp, A) carrier
  # chain across all calls.
  pure_T_R_N = pure testEff testResp H.nat;
  bind_T_R_N_N = bind testEff testResp H.nat H.nat;

  pureN = v: pure_T_R_N (H.intLit v);
  sendT = send testEff testResp H.true_;
  bindNN = bind_T_R_N_N;
  idK = pure_T_R_N;

  qAppNN = qApp testEff testResp;

  # State-effect fixtures for `run`/`handle` tests. The state module's
  # `atType` ships the kernel-resident handler closure + Nix-side
  # dispatch interpreter as a `{ handler; dispatch; … }` record.
  stateMod = fx.experimental.desc-interp.effects.state;
  stateAtNat = stateMod.atType H.nat H.nat;
  runState =
    run stateAtNat.eff stateAtNat.resp H.nat;

  # Error-effect fixtures for `run` shortcut parity tests. Each strategy
  # exposes a different `outputVal` shape — strict aborts (`Σ State E`,
  # action="throw"), collecting resumes (`Σ (List E) Unit`,
  # action="resume"), result aborts (`Σ State (Sum E A_inner)`,
  # action="abort"). All three reduce by `H.refl` per their
  # `error-shortcut-laws.nix` lemma; shortcut output is built via
  # `extract.PairRaw` plus precomputed inner-injector Val closures.
  errorMod = fx.experimental.desc-interp.effects.error;
  errorStrictAtString = errorMod.atType_strict H.string H.nat;
  errorCollectingAtString = errorMod.atType_collecting H.string;
  errorResultAtString = errorMod.atType_result H.string H.nat H.nat;
  runErrorStrict =
    run errorStrictAtString.eff errorStrictAtString.resp H.nat;
  runErrorCollecting =
    run errorCollectingAtString.eff errorCollectingAtString.resp H.nat;
  runErrorResult =
    run errorResultAtString.eff errorResultAtString.resp H.nat;

  # Fully-applied `composeHandlers` spine.
  composeHandlersAt = S_A: S_B: Op_A: Op_B: Resp_A: Resp_B: A: H_A: H_B:
    let C = fx.experimental.desc-interp.compose; in
    H.app
      (H.app
        (H.app
          (H.app
            (H.app
              (H.app
                (H.app
                  (H.app (H.app C.composeHandlers S_A) S_B)
                  Op_A)
                Op_B)
              Resp_A)
            Resp_B)
          A)
        H_A)
      H_B;

  # UniRet dispatch reader. `.d.val.fst` is `Pair(payload, state)`;
  # VBootInl ↦ resume, VBootInr ↦ abort. Composed `state` is itself
  # `Pair(s_A, s_B)` and threads back verbatim.
  composedDispatch = ctx:
    let
      outputVal = ctx.outputVal;
      side = outputVal.d.tag;
      pair = outputVal.d.val.fst;
    in
    if side == "VBootInl" then {
      action = "resume";
      response = pair.fst;
      newState = pair.snd;
    }
    else if side == "VBootInr" then {
      action = "abort";
      value = pair.fst;
      newState = pair.snd;
    }
    else throw "experimental.descInterp.trampoline composedDispatch: expected VBootInl/VBootInr at outputVal.d.tag, got '${side}'";

in
{
  scope = {
    trampoline = api.namespace {
      description = "fx.experimental.desc-interp.trampoline: qApp/run/handle interpreters trampolining FreeFx Desc values via genericClosure for O(1) stack depth on long chains.";

      value = {
        qAppend = api.leaf {
          value = qAppend;
          description = "qAppend Eff Resp l r — concatenate two queues. Identity short-circuits on either side mirror `queue.nix:append`; otherwise builds `qNode l r` with the seam M = `l._index.A` (= `r._index.X`, asserted host-level by qNode). The composite queue inhabits μI U² kontQueueApp (l._index.X, r._index.A).";
          signature = "qAppend : Hoas U -> Hoas (U -> U) -> Hoas (μI U² kontQueueApp …) -> Hoas (μI U² kontQueueApp …) -> Hoas (μI U² kontQueueApp …)";
          tests = {
            "qAppend-regrouping-conv-on-sigma-residual" = {
              # The conv-on-Σ residual `~q` addresses operationally.
              #
              # Three seam-aligned queues:
              #   l : (Nat, Bool), m : (Bool, String), r : (String, Unit).
              #
              # `qAppend (qAppend l m) r` ⇒ `qNode (qNode l m) r`:
              #   outer seam String, inner seam Bool.
              # `qAppend l (qAppend m r)` ⇒ `qNode l (qNode m r)`:
              #   outer seam Bool, inner seam String.
              #
              # The seam-witness `M : U` slot of qNodeSummand carries
              # different values at corresponding tree positions, so
              # `deepEqualDesc` distinguishes the two. Under qApp the
              # observable content is the same iterated continuation
              # composition.
              #
              # Kernel features that would dissolve this residual into a
              # definitional equality, absent here:
              #   - Atkey 2018 (QTT): erasure declares M's quantity 0; the
              #     seam witness is syntactically erased from convertibility.
              #   - Altenkirch / McBride / Swierstra 2007 (OTT): extensional
              #     equality reduces away seam-witness Σ-spines via
              #     congruence on downstream observation.
              #
              # `~q q1 q2 = ∀x:X. EqDT (qApp q1 x) (qApp q2 x)` is the
              # user-land equivalent: the seams become unobservable under
              # qApp's iterated composition.
              expr =
                let
                  ln = qLeaf testEff testResp H.nat H.bool
                    (H.lam "_n" H.nat (_:
                      pure testEff testResp H.bool H.true_));
                  mn = qLeaf testEff testResp H.bool H.string
                    (H.lam "_b" H.bool (_:
                      pure testEff testResp H.string
                        (H.stringLit "out")));
                  rn = qLeaf testEff testResp H.string H.unit
                    (H.lam "_s" H.string (_:
                      pure testEff testResp H.unit H.tt));
                  left = qAppend testEff testResp
                    (qAppend testEff testResp ln mn)
                    rn;
                  right = qAppend testEff testResp ln
                    (qAppend testEff testResp mn rn);
                in
                G.deepEqualDesc left right;
              expected = false;
            };
          };
        };
        qApp = api.leaf {
          value = qApp;
          description = "qApp Eff Resp q x — apply queue `q` to value `x : Hoas q._index.X`; trampolines Pure-returning leaves via genericClosure; on Impure splices the inner queue with the remaining tail. The queue's `_index` sidecar carries the (X, A) indexing that the kernel's μI U² slot witnesses.";
          signature = "qApp : Hoas U -> Hoas (U -> U) -> Hoas (μI U² kontQueueApp …) -> Hoas X -> Hoas (μ freeFxApp Eff Resp A)";
          tests = {
            "qApp-on-qIdentity-equals-pure-x" = {
              # η-law of qIdentity: qApp qIdentity x ≡ pure x. Witnessed by
              # `deepEqualDesc` on the resulting freeFx values — on Pure-
              # only outputs, deepEqualDesc and ~q coincide.
              expr =
                let
                  q = qIdentity testEff testResp H.nat;
                  r = qAppNN q (H.intLit 7);
                in
                G.deepEqualDesc r (pure_T_R_N (H.intLit 7));
              expected = true;
            };

            "qApp-on-qLeaf-equals-fn-applied" = {
              # β-law of qLeaf: qApp (qLeaf X A fn) x ≡ fn x. Here fn = idK
              # (= pure), so the equivalence reduces to qApp qLeaf x ≡ pure x.
              expr =
                let
                  q = qLeaf testEff testResp H.nat H.nat
                    (H.lam "_x" H.nat (x: idK x));
                  r = qAppNN q (H.intLit 3);
                in
                G.deepEqualDesc r (pure_T_R_N (H.intLit 3));
              expected = true;
            };

            "qApp-on-qNode-equals-composed-leaves" = {
              # qNode-composition law: qApp (qNode l r) x ≡ bind (qApp l x)
              # (qApp r). With l = qLeaf addOne and r = qLeaf addTen on Pure-
              # returning continuations, the composition reduces to
              # pure ((x + 1) + 10). At x = 5 the closed form is pure 16.
              # Seam alignment: l._index.A = r._index.X = H.nat.
              expr =
                let
                  addOne = H.lam "_x" H.nat (x: pureN (x.value + 1));
                  addTen = H.lam "_x" H.nat (x: pureN (x.value + 10));
                  l = qLeaf testEff testResp H.nat H.nat addOne;
                  r = qLeaf testEff testResp H.nat H.nat addTen;
                  q = qNode testEff testResp l r;
                  out = qAppNN q (H.intLit 5);
                in
                G.deepEqualDesc out (pure_T_R_N (H.intLit 16));
              expected = true;
            };

            "qApp-deep-pure-chain-10K-equals-pure-10000" = {
              # Build a left-leaning Node tree of 10K Pure-returning leaves
              # via qSnoc; apply to 0. Each leaf adds 1, so by qNode-
              # composition the chain reduces to pure 10000. The streaming
              # `qApp` walks the tree via a single genericClosure with an
              # O(1)-push linked-list stack, so RAM stays linear in N
              # (≈4–5 KB per leaf) — a vector-list `++`-based stack would
              # blow up O(N²). `deepEqualDesc` against the closed form
              # both witnesses semantic correctness and forces the full
              # traversal that detects host-stack overflow; `tryEval`
              # surfaces an overflow as success=false.
              expr =
                let
                  n = 10000;
                  q0 = qIdentity testEff testResp H.nat;
                  q = builtins.foldl'
                    (acc: _: qSnoc testEff testResp H.nat acc
                      (x: pureN (x.value + 1)))
                    q0
                    (builtins.genList (i: i) n);
                  out = qAppNN q (H.intLit 0);
                  cmp = builtins.tryEval
                    (G.deepEqualDesc out (pure_T_R_N (H.intLit 10000)));
                in
                cmp.success && cmp.value;
              expected = true;
            };
          };
        };
        run = api.leaf {
          value = run;
          description = "run Eff Resp A { handler; dispatch } prog initialState — drive `prog : μ(freeFxApp Eff Resp A)` to completion via a `genericClosure` worklist; per Impure node, the kernel-resident `handler` term is applied to the op + threaded state via `vApp`, and the Nix-side `dispatch` interpreter reads the kernel-eval'd result to produce a step decision.";
          signature = "run : Hoas U -> Hoas (U -> U) -> Hoas U -> { handler; dispatch } -> Hoas (μ freeFxApp Eff Resp A) -> Hoas State -> { value; state }";
          tests = {
            "run-on-pure-returns-value" = {
              # Pure program: dispatch is never invoked. Final value is the
              # HOAS lit threaded through `pureD`; state remains the eval'd
              # initial HOAS state (here `H.zero`, a VDescCon Nat zero).
              expr =
                let
                  pureD = pure stateAtNat.eff stateAtNat.resp H.nat;
                  r = runState
                    { inherit (stateAtNat) handler dispatch; }
                    (pureD (H.intLit 42))
                    H.zero;
                in
                { v = r.value.value; sTag = r.state.tag; };
              expected = { v = 42; sTag = "VDescCon"; };
            };

            "run-state-get-resumes-with-current-state" = {
              # Single `get` on initial state `succ (succ zero)`. dispatch
              # returns action="resume" with response = state Val; qApp
              # short-circuits qIdentity into `pure response`. The final
              # value is the state Val (a Nat VDescCon at depth 2).
              expr =
                let
                  initS = H.succ (H.succ H.zero);
                  r = runState
                    { inherit (stateAtNat) handler dispatch; }
                    stateAtNat.get
                    initS;
                in
                { vTag = r.value.tag; sTag = r.state.tag; };
              expected = { vTag = "VDescCon"; sTag = "VDescCon"; };
            };

            "run-state-put-updates-state" = {
              # Single `put zero` after initial state `succ zero`. State
              # becomes zero; final value is the put's response (Unit /
              # tt). The new state must be the freshly-supplied HOAS arg
              # eval'd to its VDescCon zero form.
              expr =
                let
                  initS = H.succ H.zero;
                  r = runState
                    { inherit (stateAtNat) handler dispatch; }
                    (stateAtNat.put H.zero)
                    initS;
                in
                r.state.tag;
              expected = "VDescCon";
            };

            "run-state-bind-get-then-put" = {
              # `bind get (n: put (succ n))` — read state, write its
              # successor. Initial state `zero`; final state `succ zero`.
              # Verifies the queue-threaded resume path: response is the
              # current state Val (lifted back to HOAS via `embedVal` so it
              # can sit under `H.succ …` — `H.succ` is a Nix-level wrapper
              # for `H.app NatDT.succ`, so `H.app H.succ x` would put a bare
              # Nix lambda in an `app.fn` slot and trip the elaborator).
              # qLeaf body builds `put (succ response)`.
              expr =
                let
                  bindD = bind stateAtNat.eff stateAtNat.resp H.nat H.nat;
                  prog = bindD stateAtNat.get (n:
                    stateAtNat.put (H.succ (Elab.embedVal n)));
                  r = runState
                    { inherit (stateAtNat) handler dispatch; }
                    prog
                    H.zero;
                in
                r.state.tag;
              expected = "VDescCon";
            };

            # ---- handlerShortcut behavioural parity ---------------------
            #
            # With `handlerShortcut` wired, the per-Impure step bypasses
            # `vApp (vApp handlerCore opVal) stateVal` and produces the
            # output Val directly via `extract.Resume`. Each test below
            # runs the same program with and without the shortcut and
            # asserts the observable result is identical.

            "shortcut-state-get-matches-kernel-path" = {
              expr =
                let
                  initS = H.succ (H.succ H.zero);
                  base = runState { inherit (stateAtNat) handler dispatch; }
                    stateAtNat.get
                    initS;
                  short = runState
                    {
                      inherit (stateAtNat)
                        handler dispatch handlerShortcut;
                    }
                    stateAtNat.get
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            "shortcut-state-put-matches-kernel-path" = {
              expr =
                let
                  initS = H.succ H.zero;
                  base = runState { inherit (stateAtNat) handler dispatch; }
                    (stateAtNat.put H.zero)
                    initS;
                  short = runState
                    {
                      inherit (stateAtNat)
                        handler dispatch handlerShortcut;
                    }
                    (stateAtNat.put H.zero)
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state;
              expected = true;
            };

            "shortcut-state-bind-get-then-put-matches-kernel-path" = {
              expr =
                let
                  bindD = bind stateAtNat.eff stateAtNat.resp H.nat H.nat;
                  prog = bindD stateAtNat.get (n:
                    stateAtNat.put (H.succ (Elab.embedVal n)));
                  base = runState { inherit (stateAtNat) handler dispatch; }
                    prog
                    H.zero;
                  short = runState
                    {
                      inherit (stateAtNat)
                        handler dispatch handlerShortcut;
                    }
                    prog
                    H.zero;
                in
                fx.tc.conv.conv 0 base.state short.state;
              expected = true;
            };

            # `modify` exercises the third shortcut branch — `fnVal`
            # evaluated from `op.arg`, applied to the runtime state to
            # produce the new state. Probe with `succ : Nat → Nat`.
            "shortcut-state-modify-matches-kernel-path" = {
              expr =
                let
                  initS = H.succ H.zero;
                  modProg = stateAtNat.modify
                    (H.lam "n" H.nat (n: H.succ n));
                  base = runState { inherit (stateAtNat) handler dispatch; }
                    modProg
                    initS;
                  short = runState
                    {
                      inherit (stateAtNat)
                        handler dispatch handlerShortcut;
                    }
                    modProg
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state;
              expected = true;
            };

            # ---- error-effect handlerShortcut parity ---------------------
            #
            # Three strategies, each exercising a different dispatch action.
            # Strict's action="throw" makes end-to-end value comparison
            # impossible — `run` raises a Nix `throw` on either path — so
            # the parity test confirms both paths reach the throw (proves
            # the shortcut output's `.fst`/`.snd` slots survive dispatch).
            # Structural conv between shortcut and kernel paths is
            # certified at the lemma + emitter layer (see
            # `error-shortcut-laws.nix` + `extract.nix:_self.tests`).
            # Collecting (resume) and result (abort) admit full end-to-end
            # `conv` parity since `run` returns normally.

            "shortcut-error-strict-throws-on-raise-with-or-without-shortcut" = {
              # `run` returns a lazy `{ value; state; }`; the throw is
              # buried inside the thunks. Force `.state.tag` under tryEval
              # to surface it.
              expr =
                let
                  prog = errorStrictAtString.raise (H.stringLit "boom");
                  forceRun = args:
                    let r = runErrorStrict args prog H.zero; in
                    builtins.tryEval
                      (builtins.seq (r.state.tag or "?") true);
                  base = forceRun
                    { inherit (errorStrictAtString) handler dispatch; };
                  short = forceRun
                    {
                      inherit (errorStrictAtString)
                        handler dispatch handlerShortcut;
                    };
                in
                (!base.success) && (!short.success);
              expected = true;
            };

            # collecting resumes with tt; final state cons-es the payload
            # onto the initial nil. Compare state Val for parity.
            "shortcut-error-collecting-matches-kernel-path" = {
              expr =
                let
                  prog = errorCollectingAtString.raise (H.stringLit "boom");
                  initS = H.nil;
                  base = runErrorCollecting
                    { inherit (errorCollectingAtString) handler dispatch; }
                    prog
                    initS;
                  short = runErrorCollecting
                    {
                      inherit (errorCollectingAtString)
                        handler dispatch handlerShortcut;
                    }
                    prog
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            # result aborts; final value is the Sum-injected payload, final
            # state is the initial state. Compare both for parity.
            "shortcut-error-result-matches-kernel-path" = {
              expr =
                let
                  prog = errorResultAtString.raise (H.stringLit "boom");
                  base = runErrorResult
                    { inherit (errorResultAtString) handler dispatch; }
                    prog
                    H.zero;
                  short = runErrorResult
                    {
                      inherit (errorResultAtString)
                        handler dispatch handlerShortcut;
                    }
                    prog
                    H.zero;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            # ---- composed handlerShortcut parity ------------------------
            #
            # `composeHandlers` over (state, error_X) on `composedInl`/
            # `composedInr` programs. Short path uses `composedHandlerShortcut
            # H_short_state H_short_uniformX metaFor`; soundness anchored
            # kernel-side by `composed-shortcut-laws.nix`. `metaFor` is
            # narrowed to the single canonical op each test exercises.

            # A := S_A from `composedResp (composedInl get) ι→ S_A`.
            "shortcut-composed-state-collecting-get-matches-kernel-path" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  CS = fx.experimental.desc-interp.composed-shortcut;
                  S_A = H.nat;
                  E = H.string;
                  S_B = H.listOf E;
                  A = H.nat;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_collecting E;
                  SigmaSHoas = H.sigma "_sA" S_A (_: S_B);
                  SumOp = H.sum Op_A Op_B;
                  RespC = fx.experimental.desc-interp.compose.composedRespAt
                    Op_A
                    Op_B
                    Resp_A
                    Resp_B;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_collecting E) A;
                  handler = composeHandlersAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                  stateAt = State.atType S_A A;
                  errorAt = Error.atType_collecting E;
                  metaFor = op:
                    if (op._side or null) == "composed-inl"
                      && (op._inner._opTag or null) == "state-get"
                    then
                      CS.mkComposedMeta
                        {
                          inherit SigmaSHoas A;
                          respHoas = S_A;
                        }
                    else null;
                  handlerShortcut = CS.composedHandlerShortcut
                    stateAt.handlerShortcut
                    (errorAt.uniformOfShortAt A)
                    metaFor;
                  taggedGet = (State.getAt S_A)
                    // { _opTag = "state-get"; };
                  prog = K.send SumOp RespC (CS.composedInl Op_A Op_B taggedGet);
                  initS = H.pair (H.succ H.zero) H.nil;
                  runC = run SumOp RespC A;
                  base = runC { inherit handler; dispatch = composedDispatch; }
                    prog
                    initS;
                  short = runC
                    {
                      inherit handler handlerShortcut;
                      dispatch = composedDispatch;
                    }
                    prog
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            # A := unit from `composedResp (composedInr raise) ι→ unit`.
            "shortcut-composed-state-collecting-raise-matches-kernel-path" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  CS = fx.experimental.desc-interp.composed-shortcut;
                  S_A = H.nat;
                  E = H.string;
                  S_B = H.listOf E;
                  A = H.unit;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_collecting E;
                  SigmaSHoas = H.sigma "_sA" S_A (_: S_B);
                  SumOp = H.sum Op_A Op_B;
                  RespC = fx.experimental.desc-interp.compose.composedRespAt
                    Op_A
                    Op_B
                    Resp_A
                    Resp_B;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_collecting E) A;
                  handler = composeHandlersAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                  stateAt = State.atType S_A A;
                  errorAt = Error.atType_collecting E;
                  metaFor = op:
                    if (op._side or null) == "composed-inr"
                      && (op._inner._opTag or null) == "error-raise"
                    then
                      CS.mkComposedMeta
                        {
                          inherit SigmaSHoas A;
                          respHoas = H.unit;
                        }
                    else null;
                  handlerShortcut = CS.composedHandlerShortcut
                    stateAt.handlerShortcut
                    (errorAt.uniformOfShortAt A)
                    metaFor;
                  taggedRaise =
                    (H.app (H.app Error.EffError.error E) (H.stringLit "boom"))
                    // { _opTag = "error-raise"; };
                  prog = K.send SumOp RespC (CS.composedInr Op_A Op_B taggedRaise);
                  initS = H.pair H.zero H.nil;
                  runC = run SumOp RespC A;
                  base = runC { inherit handler; dispatch = composedDispatch; }
                    prog
                    initS;
                  short = runC
                    {
                      inherit handler handlerShortcut;
                      dispatch = composedDispatch;
                    }
                    prog
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            # A := E (strict's abort channel). Composed UniRet aborts via
            # VBootInr, so `composedDispatch` routes "abort" (not "throw");
            # both paths return normally and `.value`/`.state` are comparable.
            "shortcut-composed-state-strict-raise-matches-kernel-path" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  CS = fx.experimental.desc-interp.composed-shortcut;
                  S_A = H.nat;
                  S_B = H.nat;
                  E = H.string;
                  A = E;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_strict E;
                  SigmaSHoas = H.sigma "_sA" S_A (_: S_B);
                  SumOp = H.sum Op_A Op_B;
                  RespC = fx.experimental.desc-interp.compose.composedRespAt
                    Op_A
                    Op_B
                    Resp_A
                    Resp_B;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app Error.uniformOf_strict E) S_B;
                  handler = composeHandlersAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                  stateAt = State.atType S_A A;
                  errorAt = Error.atType_strict E S_B;
                  metaFor = op:
                    if (op._side or null) == "composed-inr"
                      && (op._inner._opTag or null) == "error-raise"
                    then
                      CS.mkComposedMeta
                        {
                          inherit SigmaSHoas A;
                          respHoas = H.void;
                        }
                    else null;
                  handlerShortcut = CS.composedHandlerShortcut
                    stateAt.handlerShortcut
                    errorAt.uniformOfShort
                    metaFor;
                  taggedRaise =
                    (H.app (H.app Error.EffError.error E) (H.stringLit "boom"))
                    // { _opTag = "error-raise"; };
                  prog = K.send SumOp RespC (CS.composedInr Op_A Op_B taggedRaise);
                  initS = H.pair H.zero H.zero;
                  runC = run SumOp RespC A;
                  base = runC { inherit handler; dispatch = composedDispatch; }
                    prog
                    initS;
                  short = runC
                    {
                      inherit handler handlerShortcut;
                      dispatch = composedDispatch;
                    }
                    prog
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };

            # A := Sum E A_inner (result's typed channel).
            "shortcut-composed-state-result-raise-matches-kernel-path" = {
              expr =
                let
                  State = fx.experimental.desc-interp.effects.state;
                  Error = fx.experimental.desc-interp.effects.error;
                  CS = fx.experimental.desc-interp.composed-shortcut;
                  S_A = H.nat;
                  S_B = H.nat;
                  E = H.string;
                  A_inner = H.nat;
                  A = H.sum E A_inner;
                  Op_A = H.app State.EffState.T S_A;
                  Op_B = H.app Error.EffError.T E;
                  Resp_A = H.app State.Resp_State S_A;
                  Resp_B = H.app Error.Resp_result E;
                  SigmaSHoas = H.sigma "_sA" S_A (_: S_B);
                  SumOp = H.sum Op_A Op_B;
                  RespC = fx.experimental.desc-interp.compose.composedRespAt
                    Op_A
                    Op_B
                    Resp_A
                    Resp_B;
                  H_A = H.app (H.app State.handle_State S_A) A;
                  H_B = H.app (H.app (H.app Error.uniformOf_result E) S_B) A_inner;
                  handler = composeHandlersAt S_A S_B Op_A Op_B Resp_A Resp_B A H_A H_B;
                  stateAt = State.atType S_A A;
                  errorAt = Error.atType_result E S_B A_inner;
                  metaFor = op:
                    if (op._side or null) == "composed-inr"
                      && (op._inner._opTag or null) == "error-raise"
                    then
                      CS.mkComposedMeta
                        {
                          inherit SigmaSHoas A;
                          respHoas = H.void;
                        }
                    else null;
                  handlerShortcut = CS.composedHandlerShortcut
                    stateAt.handlerShortcut
                    errorAt.uniformOfShort
                    metaFor;
                  taggedRaise =
                    (H.app (H.app Error.EffError.error E) (H.stringLit "boom"))
                    // { _opTag = "error-raise"; };
                  prog = K.send SumOp RespC (CS.composedInr Op_A Op_B taggedRaise);
                  initS = H.pair H.zero H.zero;
                  runC = run SumOp RespC A;
                  base = runC { inherit handler; dispatch = composedDispatch; }
                    prog
                    initS;
                  short = runC
                    {
                      inherit handler handlerShortcut;
                      dispatch = composedDispatch;
                    }
                    prog
                    initS;
                in
                fx.tc.conv.conv 0 base.state short.state
                && fx.tc.conv.conv 0 base.value short.value;
              expected = true;
            };
          };
        };
        handle = api.leaf {
          value = handle;
          description = "handle Eff Resp A { return?; handler; dispatch; state } prog — thin wrapper over `run` with a custom `return` clause folding the final (value, state) pair.";
          signature = "handle : Hoas U -> Hoas (U -> U) -> Hoas U -> { return?, handler, dispatch, state } -> Hoas (μ freeFxApp Eff Resp A) -> b";
          tests = {
            "handle-with-default-return" = {
              expr =
                let
                  pureD = pure stateAtNat.eff stateAtNat.resp H.nat;
                  r = handle stateAtNat.eff stateAtNat.resp H.nat
                    {
                      inherit (stateAtNat) handler dispatch;
                      state = H.zero;
                    }
                    (pureD (H.intLit 7));
                in
                r.value.value;
              expected = 7;
            };

            "handle-with-custom-return" = {
              # Custom return extracts Nix int from the HOAS intLit value
              # and ignores final state.
              expr =
                let
                  pureD = pure stateAtNat.eff stateAtNat.resp H.nat;
                in
                handle stateAtNat.eff stateAtNat.resp H.nat
                  {
                    inherit (stateAtNat) handler dispatch;
                    state = H.zero;
                    return = v: _s: v.value * 2;
                  }
                  (pureD (H.intLit 21));
              expected = 42;
            };
          };
        };
      };
    };
  };
}
