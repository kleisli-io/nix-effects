# Generic description views and folds.
{ self, fx, api, ... }:

let
  H = fx.tc.hoas;
  HE = fx.tc.hoas._internal._encoders;
  HI = fx.tc.hoas._internal._indexed;
  E = fx.tc.eval;
  V = fx.tc.value;

  K = fx.kernel;
  P = fx.diag.positions;
  bindP = fx.tc.check.bindP;

  isHoas = x:
    builtins.isAttrs x && x ? _htag;

  isVal = x:
    builtins.isAttrs x && x ? tag;

  evalDesc = d:
    if isVal d then d
    else if isHoas d then E.eval [ ] (H.elab d)
    else throw "generic.desc.evalDesc: expected HOAS or evaluated description";

  kindOf = idx:
    if idx == 0 then "ret"
    else if idx == 1 then "arg"
    else if idx == 2 then "rec"
    else if idx == 3 then "pi"
    else if idx == 4 then "plus"
    else throw "generic.desc.descView: unknown desc view index ${toString idx}";

  rawView = d:
    let
      dVal = evalDesc d;
      view = E.descView dVal;
    in
    if view == null then throw "generic.desc.descView: malformed description"
    else view // { kind = kindOf view.idx; };

  applyDescFn = fn: arg:
    if builtins.isAttrs fn && (fn.tag or null) == "VDescViewFn"
    then fn.apply arg
    else E.vApp fn arg;

  placeholder = V.vTt;

  handlerOr = handlers: name: fallback:
    if handlers ? ${name} then builtins.getAttr name handlers else fallback;

  # Pre-elaborated HOAS encoders evaluated to closed VLam chains. Each
  # `encodeDescXTm` lives at hoas/desc.nix:184-371. Evaluating once at
  # module init lets `reconstruct` apply them via `E.vApp` without
  # re-walking the encoder HOAS tree on every call.
  encRetVal = E.eval [ ] HE.encodeDescRetTm;
  encArgVal = E.eval [ ] HE.encodeDescArgTm;
  encArgAtVal = E.eval [ ] HE.encodeDescArgAtTm;
  encRecVal = E.eval [ ] HE.encodeDescRecTm;
  encPiVal = E.eval [ ] HE.encodeDescPiTm;
  encPiAtVal = E.eval [ ] HE.encodeDescPiAtTm;
  encPlusVal = E.eval [ ] HE.encodeDescPlusTm;

  vAppN = fn: args: builtins.foldl' E.vApp fn args;

  # Homogeneity predicate: `l == k` decided structurally on level Vals.
  # vLevelZero/vLevelSuc are in normal form so Nix-meta equality is
  # reliable on the homogeneous-default path where `descViewF` threads
  # `l = k` for non-VLift sTy slots.
  isHomogeneous = l: k: l == k;

  # Build a fresh `VDescCon` from a view plus mapped children. The
  # `children` record's shape depends on the view's idx:
  #   idx 0: {}                        (ret has no sub-descriptions)
  #   idx 1: { tFn = fn-Val }          (arg's body fn: S -> muTt)
  #   idx 2: { sub = D-Val }           (rec's tail D)
  #   idx 3: { fn; sub }               (pi's selector + tail)
  #   idx 4: { A; B }                  (plus' two summands)
  # Throws on null I/k (only triggered for VDescCons not stamped by the
  # encoder bodies — e.g. synthesized test fixtures).
  # Re-attach a view's labels after rebuilding. The encoder application
  # chains drop sidecar metadata (they elaborate to plain `mkApp` chains
  # without the `ann`-with-labels wrapper the elaborator emits at
  # source-level). For round-trip identity (`mapDesc (x: x.default)`),
  # `reconstruct` re-stamps both labels directly on the resulting
  # VDescCon — both are conv-irrelevant, so the patched value remains
  # definitionally equal to a freshly elaborated
  # `H.withDescLabel`/`H.withConLabel`-decorated source. `null` labels
  # are no-ops; the two slots are orthogonal so each is restored
  # independently.
  withReconstructedLabels = view: base:
    let
      l = view.label    or null;
      cl = view.conLabel or null;
    in
    base
    // (if l != null then { _label = l; } else { })
    // (if cl != null then { _conLabel = cl; } else { });

  reconstruct = view: children:
    if view.I == null || view.k == null then
      throw "generic.desc.reconstruct: view missing I/k metadata (idx=${toString view.idx})"
    else
      let iLev = view.iLev or V.vLevelZero; in
      withReconstructedLabels view (
        if view.idx == 0 then
          vAppN encRetVal [ iLev view.I view.k view.j ]
        else if view.idx == 1 then
          if isHomogeneous view.l view.k
          then
            vAppN encArgVal
              [ iLev view.I view.k view.sTyRaw children.tFn ]
          else
            vAppN encArgAtVal
              [ iLev view.I view.k view.l view.eq view.sTyRaw children.tFn ]
        else if view.idx == 2 then
          vAppN encRecVal [ iLev view.I view.k view.j children.sub ]
        else if view.idx == 3 then
          if isHomogeneous view.l view.k
          then
            vAppN encPiVal
              [ iLev view.I view.k view.sTyRaw children.fn children.sub ]
          else
            vAppN encPiAtVal
              [
                iLev
                view.I
                view.k
                view.l
                view.eq
                view.sTyRaw
                children.fn
                children.sub
              ]
        else if view.idx == 4 then
          vAppN encPlusVal [ iLev view.I view.k children.A children.B ]
        else throw "generic.desc.reconstruct: unknown view idx ${toString view.idx}"
      );

  # Wrap a sub-description Val as a constant function `λ_:sTy. subVal`.
  # Used to build the `tFn` continuation for reconstructed `arg`/`pi`
  # descriptions where the sub-description was approximated by sampling
  # at `placeholder`. Builds the VLam directly to avoid an HOAS round
  # trip.
  constantSubFn = sTy: subVal:
    fx.tc.value.vLam "_" sTy
      (fx.tc.value.mkClosure [ subVal ] (fx.tc.term.mkVar 1));

  # Compute the children record for `reconstruct` from a view, recursing
  # via `recur` on each sub-description position. For arg/pi, the body
  # function is sampled at `placeholder` (matching `fold`'s `sample`
  # approximation), recursed, then wrapped back as a constant function.
  childrenForReconstruction = view: recur:
    if view.idx == 0 then { }
    else if view.idx == 1 then
      let subSample = recur (applyDescFn view.tFn placeholder); in
      { tFn = constantSubFn view.sTy subSample; }
    else if view.idx == 2 then
      { sub = recur view.sub; }
    else if view.idx == 3 then
      {
        fn = view.fn;
        sub = recur view.sub;
      }
    else { A = recur view.A; B = recur view.B; };

  mapDescGo = mapper: d:
    let
      view = rawView d;
      kind = kindOf view.idx;
      recurChildren = childrenForReconstruction view (mapDescGo mapper);
      default = reconstruct view recurChildren;
      mapped = mapper {
        original = d;
        inherit view kind default;
        children = recurChildren;
      };
    in
    # Mapper output protocols, checked in priority order:
      #   1. HOAS form ({ _htag = ...; }): elaborate and use.
      #   2. { _replaceChildren = {…}; }: reconstruct with the supplied
      #      children (overriding the recursed ones).
      #   3. Any Val (including `x.default` for identity-after-recursion,
      #      or a wholesale replacement Val): use as-is.
      # `x.original` is provided for inspection; returning it preserves the
      # PRE-recursion description, bypassing child rewriting. Mappers that
      # want post-recursion identity return `x.default`.
    if isHoas mapped then evalDesc mapped
    else if builtins.isAttrs mapped && mapped ? _replaceChildren
    then reconstruct view mapped._replaceChildren
    else mapped;

  # Definitional equality on descriptions, delegated to the kernel's
  # `conv` predicate. `conv` decides `Desc I k`-equality the same way
  # the type checker does: VLift idempotent collapse at `l = m`, VLam
  # α-equivalence via instantiation under a fresh var, `_canonRef`
  # short-circuit on cyclic VDescCon (avoids the Nix `==` loop on
  # μ-recursive carriers), Desc/μ unfolding (`Desc I k ≡ μ ⊤ (descDesc I k) tt`),
  # and witness-irrelevance for bound `liftedRefl` / `Eq Level` proofs.
  # Initial binder depth is 0; conv increments under binders.

  fold = handlers: d:
    let
      view = rawView d;
      recur = sub: fold handlers sub;
      default = handlerOr handlers "default" (v: v);
    in
    if view.idx == 0 then
      (handlerOr handlers "ret" default)
        {
          inherit view;
          j = view.j;
        }
    else if view.idx == 1 then
      (handlerOr handlers "arg" default)
        {
          inherit view;
          sTy = view.sTy;
          body = arg: recur (applyDescFn view.tFn arg);
          sample = recur (applyDescFn view.tFn placeholder);
        }
    else if view.idx == 2 then
      (handlerOr handlers "rec" default)
        {
          inherit view;
          j = view.j;
          sub = recur view.sub;
        }
    else if view.idx == 3 then
      (handlerOr handlers "pi" default)
        {
          inherit view;
          sTy = view.sTy;
          fn = view.fn;
          sub = recur view.sub;
        }
    else
      (handlerOr handlers "plus" default) {
        inherit view;
        left = recur view.A;
        right = recur view.B;
      };

  shapeOf = d:
    fold
      {
        ret = x: { kind = "ret"; };
        arg = x: { kind = "arg"; body = x.sample; };
        "rec" = x: { kind = "rec"; sub = x.sub; };
        pi = x: { kind = "pi"; sub = x.sub; };
        plus = x: { kind = "plus"; left = x.left; right = x.right; };
      }
      d;

  # Default monadic handler — short-circuits to a pure null carrier so a
  # partial handler set leaves untouched summands as `K.pure null` rather
  # than throwing. Users supply `default = K.pure : Computation R` (or a
  # constant of their own) to override.
  defaultHandlerM = _: K.pure null;

  # Monadic catamorphism. Each handler returns `Computation R`; the
  # combinator `bind`s recursed sub-results so handlers receive bound
  # `R` values alongside the raw view metadata. For `arg`, `body` stays
  # as a function `arg -> Computation R` because the body's
  # sub-description is parameterised; `sample` is the bound result of
  # `recur (applyDescFn view.tFn placeholder)` for handlers that only
  # need a representative.
  foldDescM = handlers: d:
    let
      view = rawView d;
      recur = sub: foldDescM handlers sub;
      default = handlerOr handlers "default" defaultHandlerM;
    in
    if view.idx == 0 then
      (handlerOr handlers "ret" default)
        {
          inherit view;
          inherit (view) j;
        }
    else if view.idx == 1 then
      K.bind (recur (applyDescFn view.tFn placeholder))
        (sampleR:
          (handlerOr handlers "arg" default) {
            inherit view;
            inherit (view) sTy;
            body = arg: recur (applyDescFn view.tFn arg);
            sample = sampleR;
          })
    else if view.idx == 2 then
      K.bind (recur view.sub)
        (subR:
          (handlerOr handlers "rec" default) {
            inherit view;
            inherit (view) j;
            sub = subR;
          })
    else if view.idx == 3 then
      K.bind (recur view.sub)
        (subR:
          (handlerOr handlers "pi" default) {
            inherit view;
            inherit (view) sTy fn;
            sub = subR;
          })
    else
      K.bind (recur view.A) (leftR:
        K.bind (recur view.B) (rightR:
          (handlerOr handlers "plus" default) {
            inherit view;
            left = leftR;
            right = rightR;
          }));

  # Paramorphism. Each handler additionally receives the original
  # sub-description Val alongside the bound recursed result — required
  # by callers that need the kernel description value at the recursive
  # site (e.g. `inferD` consulting an outer `_descRef` certificate to
  # short-circuit, or an elaborator emitting reflective term metadata).
  #
  # `arg`/`pi` carry both `body : arg -> Computation R` (recursion) and
  # `bodyDesc : arg -> Val` (description-only view) so handlers can
  # query a sub-description without paying for a monadic descent.
  paraDM = handlers: d:
    let
      view = rawView d;
      recur = sub: paraDM handlers sub;
      default = handlerOr handlers "default" defaultHandlerM;
    in
    if view.idx == 0 then
      (handlerOr handlers "ret" default)
        {
          inherit view;
          inherit (view) j;
        }
    else if view.idx == 1 then
      let sampleDesc = applyDescFn view.tFn placeholder; in
      K.bind (recur sampleDesc) (sampleR:
        (handlerOr handlers "arg" default) {
          inherit view;
          inherit (view) sTy;
          body = arg: recur (applyDescFn view.tFn arg);
          bodyDesc = arg: applyDescFn view.tFn arg;
          sample = sampleR;
          inherit sampleDesc;
        })
    else if view.idx == 2 then
      K.bind (recur view.sub)
        (subR:
          (handlerOr handlers "rec" default) {
            inherit view;
            inherit (view) j;
            sub = subR;
            subDesc = view.sub;
          })
    else if view.idx == 3 then
      K.bind (recur view.sub)
        (subR:
          (handlerOr handlers "pi" default) {
            inherit view;
            inherit (view) sTy fn;
            sub = subR;
            subDesc = view.sub;
          })
    else
      K.bind (recur view.A) (leftR:
        K.bind (recur view.B) (rightR:
          (handlerOr handlers "plus" default) {
            inherit view;
            left = leftR;
            right = rightR;
            leftDesc = view.A;
            rightDesc = view.B;
          }));

  # Path-threading monadic fold. Mirrors `foldDescM` and additionally
  # threads a `path` (list of `fx.diag.positions` segments) extended at
  # each descent. The descent uses `bindP` so any `typeError` emitted
  # from inside a sub-walk is auto-wrapped under the structural
  # position before re-raising — the kernel `bindP` discipline applied
  # to structural recursion. The descent alphabet:
  #
  #   arg.T   — `P.DArgBody`  (the body sub-description)
  #   rec.D   — `P.DRecTail`  (the recursive tail)
  #   pi.T    — `P.DPiBody`   (the pi tail)
  #   plus.L  — `P.DPlusL`    (left summand)
  #   plus.R  — `P.DPlusR`    (right summand)
  #
  # The `path` argument is *also* exposed to handlers as data, so
  # consumers that want to reflect on the descent chain (debug
  # traces, structural-position-aware non-error handlers) need not
  # rebuild it. Error handlers can either rely on `bindP`'s automatic
  # wrapping or construct positioned errors directly from `path`;
  # both routes compose because the alphabet is identical.
  #
  # `isPure` fast-path is inherited from `bindP` — recursing through a
  # sub-walk that resolves to `K.pure …` installs no handler.
  #
  # Initial path is the caller-supplied root (typically `[]` for a
  # top-level walk; callers nested under an existing descent pass the
  # outer chain so positions compose end-to-end).
  foldDescWithPath = path: handlers: d:
    let
      view = rawView d;
      default = handlerOr handlers "default" defaultHandlerM;
      extend = seg: path ++ [ seg ];
      recurAt = seg: sub:
        foldDescWithPath (extend seg) handlers sub;
    in
    if view.idx == 0 then
      (handlerOr handlers "ret" default)
        {
          inherit view path;
          inherit (view) j;
        }
    else if view.idx == 1 then
      bindP P.DArgBody (recurAt P.DArgBody (applyDescFn view.tFn placeholder))
        (sampleR:
          (handlerOr handlers "arg" default) {
            inherit view path;
            inherit (view) sTy;
            body = arg: recurAt P.DArgBody (applyDescFn view.tFn arg);
            sample = sampleR;
            bodyPath = extend P.DArgBody;
          })
    else if view.idx == 2 then
      bindP P.DRecTail (recurAt P.DRecTail view.sub)
        (subR:
          (handlerOr handlers "rec" default) {
            inherit view path;
            inherit (view) j;
            sub = subR;
            subPath = extend P.DRecTail;
          })
    else if view.idx == 3 then
      bindP P.DPiBody (recurAt P.DPiBody view.sub)
        (subR:
          (handlerOr handlers "pi" default) {
            inherit view path;
            inherit (view) sTy fn;
            sub = subR;
            subPath = extend P.DPiBody;
          })
    else
      bindP P.DPlusL (recurAt P.DPlusL view.A) (leftR:
        bindP P.DPlusR (recurAt P.DPlusR view.B) (rightR:
          (handlerOr handlers "plus" default) {
            inherit view path;
            left = leftR;
            right = rightR;
            leftPath = extend P.DPlusL;
            rightPath = extend P.DPlusR;
          }));
in
{
  scope = {
    evalDesc = api.leaf {
      value = evalDesc;
      description = "evalDesc: idempotent description normaliser — returns evaluated `Val` descriptions unchanged, evaluates HOAS descriptions via `H.elab` + `E.eval []`; throws on inputs that are neither.";
      signature = "evalDesc : Hoas | Val -> Val";
    };

    descView = api.leaf {
      value = rawView;
      description = "descView: one-step semantic view of a description value — returns `{ idx, kind, I, k, ... }` selecting the outer constructor (`0` = ret, `1` = arg, `2` = rec, `3` = pi, `4` = plus); throws on malformed inputs.";
      signature = "descView : Hoas | Val -> { idx : 0..4; kind : String; I : Val; k : Val; ... }";
      doc = ''
        Friendly wrapper around `fx.tc.eval.descView` that adds a
        human-readable `kind` field alongside the integer `idx`.
        Returns the raw view fields (`I`, `k`, `j`, `sTy`, `tFn`,
        `sub`, `A`, `B`, optional `label`/`conLabel`) so callers can
        peel apart any description shape uniformly.

        Use this entry as the canonical view for generic programming
        over levitated descriptions; the lower-level
        `fx.tc.eval.descView` is identical in semantics but skips the
        kind-naming step.
      '';
    };

    foldDesc = api.leaf {
      value = fold;
      description = "foldDesc: catamorphism over description structure — recursively decomposes a description into its ret/arg/rec/pi/plus shape and invokes the matching case in `cases` with the materialised sub-values.";
      signature = "foldDesc : { ret? ; arg? ; rec? ; pi? ; plus? ; default? } -> Hoas | Val -> R";
    };

    foldDescM = api.leaf {
      value = foldDescM;
      description = "foldDescM: monadic catamorphism over description structure — recurses through ret/arg/rec/pi/plus and binds each sub-`Computation R` before invoking the matching handler, so handlers receive already-bound `R` carriers and the combinator owns the threading.";
      signature = "foldDescM : { ret? ; arg? ; rec? ; pi? ; plus? ; default? } -> Hoas | Val -> Computation R";
      doc = ''
        Monadic dual of `foldDesc`. Each handler returns a
        `Computation R`; recursed sub-computations are sequenced via
        `fx.kernel.bind` before the handler runs, so a handler
        observes bound `R` values (not raw computations).

        Per-summand handler shapes:

        - `ret`   : `{ view; j }` — no sub-recursion.
        - `arg`   : `{ view; sTy; body; sample }` where
                     `body : arg -> Computation R` defers recursion at
                     the body's parameter and `sample : R` is the bound
                     result of recursing on the placeholder-instantiated
                     body (mirrors the pure `foldDesc` arg convention).
        - `rec`   : `{ view; j; sub }` with `sub : R`.
        - `pi`    : `{ view; sTy; fn; sub }` with `sub : R` (the
                     selector `fn` stays raw — it's a `Val`, not a
                     description).
        - `plus`  : `{ view; left; right }` with both bound.

        The `default` handler is used when a per-summand handler is
        absent; default-of-defaults is `_: K.pure null`.

        Use this fold to drive `checkD`/`inferD`-shaped walkers where
        each kernel-CHECK sub-delegation lives inside a
        `Computation Tm` (typeError handler, `bindP`-style position
        wrapping). The combinator preserves the pure-bind discipline:
        recursing at a summand whose sub-walk resolves to `K.pure …`
        does not install a handler.
      '';
    };

    paraDM = api.leaf {
      value = paraDM;
      description = "paraDM: monadic paramorphism over description structure — each handler additionally receives the original sub-description `Val` alongside the bound recursed result, enabling certificate-aware fast paths and reflective elaborators.";
      signature = "paraDM : { ret? ; arg? ; rec? ; pi? ; plus? ; default? } -> Hoas | Val -> Computation R";
      doc = ''
        Paramorphic variant of `foldDescM`. Where `foldDescM` exposes
        only the recursed `R` carrier at each sub-position, `paraDM`
        also exposes the raw sub-description `Val` — required by
        callers that inspect the kernel-level description shape
        without paying for a monadic descent (certificate consultation,
        ornament-section selection, reflection).

        Per-summand handler shapes:

        - `ret`   : `{ view; j }`.
        - `arg`   : `{ view; sTy; body; bodyDesc; sample; sampleDesc }`
                     — `body : arg -> Computation R` and the
                     parallel `bodyDesc : arg -> Val` return
                     the sub-description without recursing. `sample`
                     and `sampleDesc` are the bound result and raw
                     `Val` at the placeholder respectively.
        - `rec`   : `{ view; j; sub; subDesc }` — `subDesc : Val` is
                     the original sub-description `view.sub`.
        - `pi`    : `{ view; sTy; fn; sub; subDesc }`.
        - `plus`  : `{ view; left; right; leftDesc; rightDesc }`.

        `default` and identity-on-failure semantics match `foldDescM`.
      '';
    };

    foldDescWithPath = api.leaf {
      value = foldDescWithPath;
      description = "foldDescWithPath: monadic catamorphism that threads a `path` of `fx.diag.positions` segments AND uses `bindP` at each descent so emitted typeErrors auto-wrap under the structural position before re-raising.";
      signature = "foldDescWithPath : [Position] -> { ret? ; arg? ; rec? ; pi? ; plus? ; default? } -> Hoas | Val -> Computation R";
      doc = ''
        Variant of `foldDescM` with two-pronged structural blame:
        every descent installs a `fx.tc.check.bindP` handler under
        the descent's position, and the current `path` is exposed to
        handlers as data. The blame alphabet at each descent:

          arg.T   → `P.DArgBody`
          rec.D   → `P.DRecTail`
          pi.T    → `P.DPiBody`
          plus.L  → `P.DPlusL`
          plus.R  → `P.DPlusR`

        Because the descent uses `bindP`, a sub-handler that emits
        `typeError` produces an error tree whose outermost edge is
        the descent position, with the original error nested under
        it. Nested descents stack — a typeError emitted at the leaf
        of a plus(rec(ret)) descent surfaces with the edge chain
        `[DPlusL, DRecTail]` outermost-first, matching the kernel's
        existing positional-blame convention. Handlers that prefer
        explicit position wrapping can use the `path` argument and
        `D.nestUnder` directly; both routes compose because the
        alphabet is identical.

        Pure (`K.pure …`) sub-walks short-circuit through `bindP`'s
        `isPure` fast path — no handler install, no overhead.

        Each handler receives the *current* `path` (the chain leading
        to its node, not yet extended by its own descent) and, for
        non-leaf summands, helper extenders matching what the
        descent will install:

        - `ret`   : `{ view; path; j }`.
        - `arg`   : `{ view; path; sTy; body; sample; bodyPath }` —
                     `bodyPath = path ++ [DArgBody]`.
        - `rec`   : `{ view; path; j; sub; subPath }` —
                     `subPath = path ++ [DRecTail]`.
        - `pi`    : `{ view; path; sTy; fn; sub; subPath }` —
                     `subPath = path ++ [DPiBody]`.
        - `plus`  : `{ view; path; left; right; leftPath; rightPath }`.

        Pass `[]` as the root path for a top-level walk. Nested
        callers pass the outer chain so positions compose
        end-to-end.
      '';
    };

    mapDesc = api.leaf {
      value = mapDescGo;
      description = "mapDesc: structurally rewrite each layer of a description via per-shape mapper functions, then reconstruct using the canonical encoder chain — the result is conv-equivalent to the original when mappers are identities.";
      signature = "mapDesc : { ret? ; arg? ; rec? ; pi? ; plus? } -> Hoas | Val -> Val";
    };

    deepEqualDesc = api.leaf {
      value = d1: d2:
        fx.tc.conv.conv 0 (evalDesc d1) (evalDesc d2);
      description = "deepEqualDesc: definitional equality on description values — evaluates both arguments via `evalDesc`, then runs `fx.tc.conv.conv 0` for full conv-equality.";
      signature = "deepEqualDesc : Hoas | Val -> Hoas | Val -> Bool";
    };

    children = api.leaf {
      value = d:
        let view = rawView d; in
        if view.idx == 0 then [ ]
        else if view.idx == 1 then [ (applyDescFn view.tFn placeholder) ]
        else if view.idx == 2 then [ view.sub ]
        else if view.idx == 3 then [ view.sub ]
        else [ view.A view.B ];
      description = "children: direct sub-descriptions list — empty for `ret`, `[body]` for `arg`/`rec`/`pi` (arg applies the body to a `vTt` placeholder), `[A, B]` for `plus`.";
      signature = "children : Hoas | Val -> [Val]";
    };

    shape = api.leaf {
      value = shapeOf;
      description = "shape: tagged-record skeleton of a description — returns `{ kind = \"ret\" | \"arg\" | \"rec\" | \"pi\" | \"plus\"; ...payload }` with only the shape-relevant fields; payload depends on `kind`.";
      signature = "shape : Hoas | Val -> { kind : String; ... }";
    };

    isRet = api.leaf {
      value = d: (rawView d).idx == 0;
      description = "isRet: predicate — `true` iff the description's outer constructor is `descRet`.";
      signature = "isRet : Hoas | Val -> Bool";
    };
    isArg = api.leaf {
      value = d: (rawView d).idx == 1;
      description = "isArg: predicate — `true` iff the description's outer constructor is `descArg`.";
      signature = "isArg : Hoas | Val -> Bool";
    };
    isRec = api.leaf {
      value = d: (rawView d).idx == 2;
      description = "isRec: predicate — `true` iff the description's outer constructor is `descRec`.";
      signature = "isRec : Hoas | Val -> Bool";
    };
    isPi = api.leaf {
      value = d: (rawView d).idx == 3;
      description = "isPi: predicate — `true` iff the description's outer constructor is `descPi`.";
      signature = "isPi : Hoas | Val -> Bool";
    };
    isPlus = api.leaf {
      value = d: (rawView d).idx == 4;
      description = "isPlus: predicate — `true` iff the description's outer constructor is `plusI` (binary sum).";
      signature = "isPlus : Hoas | Val -> Bool";
    };
  };

  tests = {
    "desc-view-ret" = {
      expr = self.descView H.descRet;
      expected = {
        idx = 0;
        kind = "ret";
        j = V.vTt;
        iLev = V.vLevelZero;
        I = V.vUnit;
        k = V.vLevelZero;
        label = null;
        conLabel = null;
      };
    };

    "desc-view-plus-kind" = {
      expr = (self.descView (H.plus H.descRet H.descRet)).kind;
      expected = "plus";
    };

    # Labels — erasable presentation metadata threaded through encoder /
    # eval / view round-trip. Definitional equality is label-irrelevant
    # (conv doesn't see `_label` on VDescCon); mapDesc preserves labels
    # through reconstruction.
    "desc-view-arg-no-label" = {
      expr = (self.descView (H.descArg H.unit 0 H.nat (_: H.descRet))).label;
      expected = null;
    };

    "desc-view-arg-with-label" = {
      expr = (self.descView
        (H.withDescLabel "x"
          (H.descArg H.unit 0 H.nat (_: H.descRet)))).label;
      expected = "x";
    };

    "desc-view-rec-with-label" = {
      expr = (self.descView
        (H.withDescLabel "tail" (H.descRec H.descRet))).label;
      expected = "tail";
    };

    "desc-view-plus-with-label" = {
      expr = (self.descView
        (H.withDescLabel "Cons" (H.plus H.descRet H.descRet))).label;
      expected = "Cons";
    };

    "desc-view-pi-with-label" = {
      expr =
        let
          Dpi = HI.piI H.unit 0 H.nat (H.lam "_" H.nat (_: H.tt)) H.descRet;
        in
        (self.descView (H.withDescLabel "f" Dpi)).label;
      expected = "f";
    };

    "desc-deepEqualDesc-labels-irrelevant" = {
      # Two descArgs of the same shape, one labeled and one not, are
      # definitionally equal — labels are presentation metadata, not
      # propositional content. Mirrors the eq-witness-irrelevance pattern
      # already used for `LiftAt`.
      expr =
        let
          labeled = H.withDescLabel "x"
            (H.descArg H.unit 0 H.nat (_: H.descRet));
          plain = H.descArg H.unit 0 H.nat (_: H.descRet);
        in
        self.deepEqualDesc labeled plain;
      expected = true;
    };

    "desc-mapDesc-identity-preserves-label" = {
      # Round-tripping a labeled description through `mapDesc (x: x.default)`
      # must preserve the label — `reconstruct` re-stamps the label.
      expr =
        let
          D = H.withDescLabel "x"
            (H.descArg H.unit 0 H.nat (_: H.descRet));
        in
        (self.descView (self.mapDesc (x: x.default) D)).label;
      expected = "x";
    };

    "desc-mapDesc-identity-preserves-plus-label" = {
      expr =
        let
          D = H.withDescLabel "Cons" (H.plus H.descRet H.descRet);
        in
        (self.descView (self.mapDesc (x: x.default) D)).label;
      expected = "Cons";
    };

    # Constructor labels — orthogonal to per-node labels. Lives in a
    # separate `_conLabel` slot so wrapping a field-labeled
    # description with a constructor name does not overwrite the
    # field's identity. Surfaces as `.conLabel` on every view.
    "desc-view-arg-no-conLabel" = {
      expr = (self.descView (H.descArg H.unit 0 H.nat (_: H.descRet))).conLabel;
      expected = null;
    };

    "desc-view-arg-with-conLabel" = {
      expr = (self.descView
        (H.withConLabel "mk"
          (H.descArg H.unit 0 H.nat (_: H.descRet)))).conLabel;
      expected = "mk";
    };

    "desc-view-conLabel-independent-of-label" = {
      # Both slots populated simultaneously; both surface. This is the
      # exact property the wiring in hoas/datatype.nix relies on when
      # `H.con "mk" [H.field "x" T]` produces a description carrying
      # both names.
      expr =
        let
          D = H.withConLabel "mk"
            (H.withDescLabel "x"
              (H.descArg H.unit 0 H.nat (_: H.descRet)));
          v = self.descView D;
        in
        { inherit (v) label conLabel; };
      expected = { label = "x"; conLabel = "mk"; };
    };

    "desc-view-conLabel-order-independent" = {
      # Reversing the wrap order gives the same view — neither label
      # overwrites the other because they target distinct sidecar slots.
      expr =
        let
          D = H.withDescLabel "x"
            (H.withConLabel "mk"
              (H.descArg H.unit 0 H.nat (_: H.descRet)));
          v = self.descView D;
        in
        { inherit (v) label conLabel; };
      expected = { label = "x"; conLabel = "mk"; };
    };

    "desc-deepEqualDesc-conLabels-irrelevant" = {
      expr =
        let
          labeled = H.withConLabel "mk"
            (H.descArg H.unit 0 H.nat (_: H.descRet));
          plain = H.descArg H.unit 0 H.nat (_: H.descRet);
        in
        self.deepEqualDesc labeled plain;
      expected = true;
    };

    "desc-mapDesc-identity-preserves-conLabel" = {
      expr =
        let
          D = H.withConLabel "mk"
            (H.descArg H.unit 0 H.nat (_: H.descRet));
        in
        (self.descView (self.mapDesc (x: x.default) D)).conLabel;
      expected = "mk";
    };

    "desc-mapDesc-identity-preserves-both-labels" = {
      # Both labels must survive a reconstruct round-trip — `reconstruct`
      # re-stamps both slots independently. This is the round-trip
      # property that guarantees label preservation under generic
      # description traversals like `mapDesc`.
      expr =
        let
          D = H.withConLabel "mk"
            (H.withDescLabel "x"
              (H.descArg H.unit 0 H.nat (_: H.descRet)));
          v = self.descView (self.mapDesc (x: x.default) D);
        in
        { inherit (v) label conLabel; };
      expected = { label = "x"; conLabel = "mk"; };
    };

    # H.datatype wiring — verifies that conDesc pushes f.name into the
    # per-node `_label` slot and that _datatypeImpl pushes c.name into
    # `_conLabel`. The two slots are orthogonal so both labels survive
    # on a single constructor's description.
    "datatype-single-field-preserves-both-labels" = {
      # The exact case my first wiring attempt got wrong: a constructor
      # wraps a single labeled field. With separate slots, both names
      # survive.
      expr =
        let
          T = H.datatype "T" [ (H.con "mk" [ (H.recField "pred") ]) ];
          v = self.descView T.D;
        in
        { inherit (v) label conLabel; };
      expected = { label = "pred"; conLabel = "mk"; };
    };

    "datatype-multi-field-only-first-carries-conLabel" = {
      # Constructor label rides on the constructor's full description.
      # In a multi-field constructor that means it lands on the OUTERMOST
      # node (the first field's descArg). Descending one step via
      # `children` reaches the second field's view, which carries
      # `label` but no `conLabel` — the constructor identity is
      # positional, not propagated.
      expr =
        let
          T = H.datatype "P" [
            (H.con "mk" [
              (H.field "a" H.nat)
              (H.field "b" H.nat)
            ])
          ];
          v0 = self.descView T.D;
          v1 = self.descView (builtins.head (self.children T.D));
        in
        {
          v0 = { inherit (v0) label conLabel; };
          v1 = { inherit (v1) label conLabel; };
        };
      expected = {
        v0 = { label = "a"; conLabel = "mk"; };
        v1 = { label = "b"; conLabel = null; };
      };
    };

    "datatype-multi-con-spine-labels-survive" = {
      # The plus-spine has no constructor label on the plus node itself
      # (per-summand labeling, not tag-on-plus). Each summand carries
      # its own conLabel. The succ summand additionally carries a
      # `label = "pred"` for its recField.
      expr =
        let
          N = H.datatype "Nat" [
            (H.con "zero" [ ])
            (H.con "succ" [ (H.recField "pred") ])
          ];
          spine = self.descView N.D;
          zeroBranch = self.descView spine.A;
          succBranch = self.descView spine.B;
        in
        {
          spine = { inherit (spine) label conLabel; };
          zeroBranch = { inherit (zeroBranch) label conLabel; };
          succBranch = { inherit (succBranch) label conLabel; };
        };
      expected = {
        spine = { label = null; conLabel = null; };
        zeroBranch = { label = null; conLabel = "zero"; };
        succBranch = { label = "pred"; conLabel = "succ"; };
      };
    };

    "datatype-label-irrelevance-preserved-after-wiring" = {
      # Two datatypes with the same SHAPE but different constructor/
      # field names. Conv ignores labels on both axes so deepEqualDesc
      # returns true — the wiring does not perturb definitional
      # equality, only presentation.
      expr =
        let
          T1 = H.datatype "T1" [ (H.con "mk" [ (H.recField "next") ]) ];
          T2 = H.datatype "T2" [ (H.con "other" [ (H.recField "tail") ]) ];
        in
        self.deepEqualDesc T1.D T2.D;
      expected = true;
    };

    "desc-children-plus-count" = {
      expr = builtins.length (self.children (H.plus H.descRet H.descRet));
      expected = 2;
    };

    "desc-fold-counts-nodes" = {
      expr = self.foldDesc
        {
          ret = _: 1;
          arg = x: 1 + x.sample;
          "rec" = x: 1 + x.sub;
          pi = x: 1 + x.sub;
          plus = x: 1 + x.left + x.right;
        }
        (H.plus H.descRet (H.descRec H.descRet));
      expected = 4;
    };

    "desc-shape-small" = {
      expr = self.shape (H.plus H.descRet (H.descRec H.descRet));
      expected = {
        kind = "plus";
        left = { kind = "ret"; };
        right = {
          kind = "rec";
          sub = { kind = "ret"; };
        };
      };
    };

    "desc-map-preserves-shape" = {
      expr =
        let D = H.plus H.descRet (H.descRec H.descRet);
        in self.shape (self.mapDesc (x: x.default) D) == self.shape D;
      expected = true;
    };

    "desc-mapDesc-identity-deepequal" = {
      expr =
        let D = H.plus H.descRet (H.descRec H.descRet);
        in self.deepEqualDesc (self.mapDesc (x: x.default) D) D;
      expected = true;
    };

    "desc-mapDesc-non-trivial-replacement" = {
      # Swap every leaf ret with (rec ret); both summands of the plus must
      # come back as rec-ret. Detects whether reconstruction actually fires.
      expr =
        let
          D = H.plus H.descRet H.descRet;
          swap = x: if x.kind == "ret" then H.descRec H.descRet else x.default;
        in
        self.shape (self.mapDesc swap D);
      expected = {
        kind = "plus";
        left = { kind = "rec"; sub = { kind = "ret"; }; };
        right = { kind = "rec"; sub = { kind = "ret"; }; };
      };
    };

    "desc-mapDesc-sequential-roundtrip" = {
      # Sequential application: f wraps every ret in a rec, g collapses
      # every rec back to ret. f-then-g must reproduce D's shape. Mappers
      # return pure-HOAS replacements (H.descRet has no Val sub-children).
      expr =
        let
          D = H.plus H.descRet H.descRet;
          f = x: if x.kind == "ret" then H.descRec H.descRet else x.default;
          g = x: if x.kind == "rec" then H.descRet else x.default;
          sequenced = self.mapDesc g (self.mapDesc f D);
        in
        self.shape sequenced;
      expected = self.shape (H.plus H.descRet H.descRet);
    };

    "desc-mapDesc-arg-identity" = {
      # Identity over a descArg description preserves shape: sub-description
      # is sampled at placeholder, recursed, re-wrapped via constantSubFn.
      expr =
        let Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
        in self.deepEqualDesc (self.mapDesc (x: x.default) Darg) Darg;
      expected = true;
    };

    "desc-deepEqualDesc-refl" = {
      expr =
        let D = H.plus H.descRet (H.descRec H.descRet);
        in self.deepEqualDesc D D;
      expected = true;
    };

    "desc-deepEqualDesc-differs" = {
      expr = self.deepEqualDesc H.descRet (H.descRec H.descRet);
      expected = false;
    };

    # foldDescM: monadic catamorphism. Carrier `Int`, default handler
    # short-circuits to `K.pure 0`; sub-results are bound before each
    # case fires. Pure (`K.pure`) handler chains stay on the fast path
    # — no handler install, value extracted via `.value` directly.
    "desc-foldDescM-counts-nodes-pure" = {
      expr = (self.foldDescM
        {
          ret = _: K.pure 1;
          arg = x: K.pure (1 + x.sample);
          "rec" = x: K.pure (1 + x.sub);
          pi = x: K.pure (1 + x.sub);
          plus = x: K.pure (1 + x.left + x.right);
        }
        (H.plus H.descRet (H.descRec H.descRet))).value;
      expected = 4;
    };

    "desc-foldDescM-default-applies-to-missing-summand" = {
      expr = (self.foldDescM
        {
          default = _: K.pure 7;
        }
        H.descRet).value;
      expected = 7;
    };

    "desc-foldDescM-impure-arm-makes-fold-impure" = {
      # A sub-handler that emits an effect must propagate through the
      # binds — the resulting computation is `Impure` with the emitted
      # effect's name visible at the outermost layer. Verifies that
      # `foldDescM` does not accidentally collapse impure sub-walks to
      # pure values.
      expr =
        let
          comp = self.foldDescM
            {
              ret = _: K.pure 0;
              plus = _: K.send "trace" { tag = "plus"; };
              default = _: K.pure 0;
            }
            (H.plus H.descRet H.descRet);
        in
        comp.effect.name;
      expected = "trace";
    };

    "desc-foldDescM-body-defers-recursion" = {
      # arg handler's `body : arg -> Computation R` lets the handler
      # decide whether (and at what argument) to recurse. Confirms the
      # body slot is exposed as a function, not a pre-bound value.
      expr =
        let
          Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
          comp = self.foldDescM
            {
              ret = _: K.pure 11;
              arg = x: x.body V.vTt;
              default = _: K.pure 0;
            }
            Darg;
        in
        comp.value;
      expected = 11;
    };

    "desc-foldDescM-arg-sample-is-bound-result" = {
      # `sample` exposed to the arg handler must equal the recursed
      # carrier at the placeholder (`recur (applyDescFn tFn vTt)`),
      # not a raw Computation.
      expr =
        let
          Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
        in
        (self.foldDescM
          {
            ret = _: K.pure 99;
            arg = x: K.pure x.sample;
            default = _: K.pure 0;
          }
          Darg).value;
      expected = 99;
    };

    # paraDM: paramorphic monadic fold. The bonus carrier is the raw
    # `Val` sub-description at every recursive site, exposed alongside
    # the bound `R`. Confirms handlers see both views and that the
    # combinator's sequencing matches `foldDescM`.
    "desc-paraDM-exposes-subDesc-on-rec" = {
      expr =
        let
          Drec = H.descRec H.descRet;
          comp = self.paraDM
            {
              ret = _: K.pure null;
              "rec" = x: K.pure ((self.descView x.subDesc).kind);
              default = _: K.pure null;
            }
            Drec;
        in
        comp.value;
      expected = "ret";
    };

    "desc-paraDM-plus-exposes-both-subDescs" = {
      expr =
        let
          Dplus = H.plus H.descRet (H.descRec H.descRet);
          comp = self.paraDM
            {
              ret = _: K.pure null;
              "rec" = _: K.pure null;
              plus = x: K.pure {
                left = (self.descView x.leftDesc).kind;
                right = (self.descView x.rightDesc).kind;
              };
              default = _: K.pure null;
            }
            Dplus;
        in
        comp.value;
      expected = { left = "ret"; right = "rec"; };
    };

    "desc-paraDM-arg-bodyDesc-without-recursion" = {
      # `bodyDesc : arg -> Val` lets a paramorphic handler peek at the
      # body's description shape without paying for a monadic descent.
      expr =
        let
          Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
          comp = self.paraDM
            {
              ret = _: K.pure null;
              arg = x: K.pure ((self.descView (x.bodyDesc V.vTt)).kind);
              default = _: K.pure null;
            }
            Darg;
        in
        comp.value;
      expected = "ret";
    };

    "desc-paraDM-matches-foldDescM-on-shape-counting" = {
      # paraDM and foldDescM must agree on shape-only carriers; the
      # extra sub-description payload is purely additive.
      expr =
        let
          D = H.plus H.descRet (H.descRec H.descRet);
          cataR = (self.foldDescM
            {
              ret = _: K.pure 1;
              "rec" = x: K.pure (1 + x.sub);
              plus = x: K.pure (1 + x.left + x.right);
              default = _: K.pure 0;
            }
            D).value;
          paraR = (self.paraDM
            {
              ret = _: K.pure 1;
              "rec" = x: K.pure (1 + x.sub);
              plus = x: K.pure (1 + x.left + x.right);
              default = _: K.pure 0;
            }
            D).value;
        in
        cataR == paraR;
      expected = true;
    };

    # foldDescWithPath: path-threading variant. Confirms initial path
    # is the caller-supplied root and each descent extends with the
    # description-centric segment.
    "desc-foldDescWithPath-root-path-is-empty" = {
      expr = (self.foldDescWithPath [ ]
        {
          ret = x: K.pure x.path;
          default = _: K.pure null;
        }
        H.descRet).value;
      expected = [ ];
    };

    "desc-foldDescWithPath-extends-under-plusL" = {
      # The left summand of a plus receives `[DPlusL]` as its path.
      expr = (self.foldDescWithPath [ ]
        {
          ret = x: K.pure x.path;
          plus = x: K.pure x.left;
          default = _: K.pure null;
        }
        (H.plus H.descRet H.descRet)).value;
      expected = [ P.DPlusL ];
    };

    "desc-foldDescWithPath-extends-under-plusR" = {
      expr = (self.foldDescWithPath [ ]
        {
          ret = x: K.pure x.path;
          plus = x: K.pure x.right;
          default = _: K.pure null;
        }
        (H.plus H.descRet H.descRet)).value;
      expected = [ P.DPlusR ];
    };

    "desc-foldDescWithPath-extends-under-recTail" = {
      expr = (self.foldDescWithPath [ ]
        {
          ret = x: K.pure x.path;
          "rec" = x: K.pure x.sub;
          default = _: K.pure null;
        }
        (H.descRec H.descRet)).value;
      expected = [ P.DRecTail ];
    };

    "desc-foldDescWithPath-composes-segments-end-to-end" = {
      # plus(rec(ret), ret): walking the leftmost ret produces
      # `[DPlusL, DRecTail]`.
      expr = (self.foldDescWithPath [ ]
        {
          ret = x: K.pure x.path;
          "rec" = x: K.pure x.sub;
          plus = x: K.pure x.left;
          default = _: K.pure null;
        }
        (H.plus (H.descRec H.descRet) H.descRet)).value;
      expected = [ P.DPlusL P.DRecTail ];
    };

    "desc-foldDescWithPath-honours-non-empty-initial-path" = {
      # Caller-supplied root path prefixes every emitted chain.
      expr = (self.foldDescWithPath [ P.AnnTerm ]
        {
          ret = x: K.pure x.path;
          plus = x: K.pure x.left;
          default = _: K.pure null;
        }
        (H.plus H.descRet H.descRet)).value;
      expected = [ P.AnnTerm P.DPlusL ];
    };

    "desc-foldDescWithPath-bodyPath-helper-matches-descent" = {
      # The `bodyPath` extender on the arg handler is exactly the path
      # the descent would install — handlers can construct positioned
      # errors that line up with the eventual sub-walk's chain.
      expr =
        let
          Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
        in
        (self.foldDescWithPath [ P.MuPayload ]
          {
            ret = x: K.pure null;
            arg = x: K.pure (x.bodyPath);
            default = _: K.pure null;
          }
          Darg).value;
      expected = [ P.MuPayload P.DArgBody ];
    };

    "desc-foldDescWithPath-arg-descent-records-bodyPath" = {
      # Recursing through arg.body produces a path with DArgBody
      # appended to the caller's initial chain.
      expr =
        let
          Darg = H.descArg H.unit 0 H.nat (_: H.descRet);
        in
        (self.foldDescWithPath [ ]
          {
            ret = x: K.pure x.path;
            arg = x: x.body V.vTt;
            default = _: K.pure null;
          }
          Darg).value;
      expected = [ P.DArgBody ];
    };

    # foldDescWithPath bindP auto-wrapping: a typeError emitted from
    # inside a sub-handler must come out wrapped under the descent
    # position chain (outermost-first), matching the kernel bindP
    # convention exercised by `bindP-nested-outer-position-is-outermost-edge`
    # in `src/tc/check/bindP.nix`.
    "desc-foldDescWithPath-wraps-leaf-typeError-under-plusL" = {
      # ret-handler emits a typeError; left summand of plus must
      # produce an error whose outermost edge is `DPlusL`.
      expr =
        let
          Derr = fx.diag.error.mkKernelError {
            rule = "foldDescWithPath";
            msg = "leaf error";
          };
          runSurfacing = comp:
            let
              r = fx.trampoline.handle
                {
                  handlers.typeError = { param, state }: {
                    abort = { __surfacedError = param.error; };
                    inherit state;
                  };
                }
                comp;
            in
            r.value;
          err = runSurfacing (self.foldDescWithPath [ ]
            {
              ret = _: K.send "typeError" { error = Derr; };
              plus = x: K.pure x.left;
              default = _: K.pure null;
            }
            (H.plus H.descRet H.descRet));
        in
        (builtins.elemAt err.__surfacedError.children 0).position;
      expected = P.DPlusL;
    };

    "desc-foldDescWithPath-nested-descent-chain-outermost-first" = {
      # plus(rec(ret)): a typeError emitted at the leaf ret surfaces
      # with `DPlusL` as the outermost edge and `DRecTail` as the
      # second edge — exactly the descent chain the combinator
      # installs via bindP.
      expr =
        let
          Derr = fx.diag.error.mkKernelError {
            rule = "foldDescWithPath";
            msg = "deep leaf error";
          };
          runSurfacing = comp:
            let
              r = fx.trampoline.handle
                {
                  handlers.typeError = { param, state }: {
                    abort = { __surfacedError = param.error; };
                    inherit state;
                  };
                }
                comp;
            in
            r.value;
          err = runSurfacing (self.foldDescWithPath [ ]
            {
              ret = _: K.send "typeError" { error = Derr; };
              "rec" = x: K.pure x.sub;
              plus = x: K.pure x.left;
              default = _: K.pure null;
            }
            (H.plus (H.descRec H.descRet) H.descRet));
          outer = (builtins.elemAt err.__surfacedError.children 0);
          inner = (builtins.elemAt outer.error.children 0);
        in
        { outer = outer.position; inner = inner.position; };
      expected = { outer = P.DPlusL; inner = P.DRecTail; };
    };

    "desc-foldDescWithPath-leaf-typeError-preserved-under-chain" = {
      # The original kernel error sits at the bottom of the chain;
      # wrapping only adds blame edges and an auto-captured trace,
      # never replaces the leaf's rule/msg/expected/got.
      expr =
        let
          Derr = fx.diag.error.mkKernelError {
            rule = "foldDescWithPath";
            msg = "leaf preserved";
          };
          runSurfacing = comp:
            let
              r = fx.trampoline.handle
                {
                  handlers.typeError = { param, state }: {
                    abort = { __surfacedError = param.error; };
                    inherit state;
                  };
                }
                comp;
            in
            r.value;
          err = runSurfacing (self.foldDescWithPath [ ]
            {
              ret = _: K.send "typeError" { error = Derr; };
              "rec" = x: K.pure x.sub;
              plus = x: K.pure x.left;
              default = _: K.pure null;
            }
            (H.plus (H.descRec H.descRet) H.descRet));
          walkToLeaf = e:
            if builtins.length e.children == 0 then e
            else walkToLeaf (builtins.elemAt e.children 0).error;
          leaf = walkToLeaf err.__surfacedError;
        in
        {
          layer = leaf.layer.tag;
          msg = leaf.msg;
          rule = leaf.detail.rule;
          expected = leaf.detail.expected;
          got = leaf.detail.got;
        };
      expected = {
        layer = "Kernel";
        msg = "leaf preserved";
        rule = "foldDescWithPath";
        expected = null;
        got = null;
      };
    };

    "desc-foldDescWithPath-pure-handlers-stay-on-fast-path" = {
      # `bindP`'s fast-path discipline carries over: when every
      # sub-walk resolves to `K.pure …`, the outer computation is
      # structurally `K.pure …` too — no handler install, no
      # impure node. Direct structural equality on the result
      # records pins the fast-path discharge.
      expr = (self.foldDescWithPath [ ]
        {
          ret = _: K.pure 1;
          plus = x: K.pure (x.left + x.right);
          default = _: K.pure 0;
        }
        (H.plus H.descRet H.descRet)) == K.pure 2;
      expected = true;
    };
  };

}
