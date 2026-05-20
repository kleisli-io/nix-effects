# nix-effects typecheck: Reusable typeCheck effect handlers
#
# Bridges the type system with the effect system.
# Type validation sends typeCheck effects; these handlers interpret them.
#
# The typeCheck effect carries: { type, context, value, path, reason? }
#   type    — a nix-effects type (has .name, .check)
#   context — string describing the local type structure (e.g. "Π domain")
#   value   — the value being checked
#   path    — list of `fx.diag.positions` Position records naming the
#             structural descent from the validation root. Empty for
#             top-level `validate v`; accumulated by Record/ListOf/
#             Variant/Sigma as they recurse via `validateAt`. Render with
#             `fx.diag.positions.renderSegment` (per-segment) or the
#             concatenation thereof.
#   reason  — optional diagnostic intent tag. One of:
#               "shape-mismatch"    — structural shape disagreement (default)
#               "missing-field"     — a required record field is absent
#               "extra-field"       — an unexpected record field is present
#               "predicate-failed"  — a refinement guard returned false
#               "deferred-pi"       — Π domain/codomain check at an
#                                     application site (Findler-Felleisen
#                                     deferred contract)
#             Defaults to "shape-mismatch" when omitted.
#
# Six handlers, all exposed under `fx.effects.policy.*`:
#   strict / collecting / logging / firstN N / summarize / pretty cfg
#
# Handler interface: `{ value.typeCheck = { param, state }: { resume; state } }`.
# Invariants:
#   1. Pure: output depends only on (param, state).
#   2. Param: read `type`, `value`, `context`; optional `path` (Position
#      list — empty by default), `reason` (default "shape-mismatch"),
#      `diagError`.
#   3. Abort via `resume = false`; throwing is reserved for strict.
#   4. State shape is the handler's choice but must be documented;
#      callers pass the documented initial state to `fx.handle`.
#
# Pattern: Plotkin & Pretnar (2009); freer encoding: Kiselyov & Ishii (2015).
{ fx, api, ... }:
let
  inherit (fx.diag.positions) renderSegment;

  # Render the blame location from the Position-list path. Each segment
  # carries its own separator (`.field`, `[i]`, `#tag`), so concatenation
  # is the natural reconstruction. Falls back to `context` when the path
  # is empty (top-level validate).
  renderPath = path:
    builtins.concatStringsSep "" (map renderSegment path);

  blameLocation = param:
    let path = param.path or [ ]; in
    if path == [ ] then param.context else renderPath path;

  # Render the offending value's shape for diagnostics. Plain
  # `builtins.typeOf` collapses every record to `"set"`; if the record
  # carries a `_con` or `_tag` discriminator, surface it so the reader
  # sees what constructor actually arrived versus what was expected.
  describeValue = v:
    let ty = builtins.typeOf v; in
    if ty == "set" then
      let tag = v._con or v._tag or null; in
      if tag != null then "set(_con=${toString tag})" else ty
    else ty;

  # Build the diagnostic message. Top-level errors (empty path) drop the
  # "at <loc>" clause when `context` is redundant with `type.name`; when
  # context describes the issue (e.g. "unknown constructor 'X'"), it
  # appears as a parenthetical note. Non-empty paths use `renderPath`
  # for the blame location.
  mkMessage = param:
    let
      path = param.path or [ ];
      typeName = param.type.name;
      ctx = param.context or "";
      loc =
        if path == [ ] then ""
        else " at ${renderPath path}";
      note =
        if path != [ ] || ctx == "" || ctx == typeName then ""
        else " (${ctx})";
    in
    "Expected ${typeName}${loc}, got ${describeValue param.value}${note}";

  strict = {
    typeCheck = { param, state }:
      if param.type.check param.value
      then { resume = true; inherit state; }
      else
        let reason = param.reason or "shape-mismatch"; in
        builtins.throw "[${reason}] ${mkMessage param}";
  };

  collecting = {
    typeCheck = { param, state }:
      if param.type.check param.value
      then { resume = true; inherit state; }
      else {
        resume = false;
        state = state ++ [{
          context = param.context;
          typeName = param.type.name;
          actual = describeValue param.value;
          path = param.path or [ ];
          reason = param.reason or "shape-mismatch";
          message = mkMessage param;
        }];
      };
  };

  logging = {
    typeCheck = { param, state }:
      let passed = param.type.check param.value;
      in {
        resume = passed;
        state = state ++ [{
          context = param.context;
          typeName = param.type.name;
          path = param.path or [ ];
          reason = param.reason or "shape-mismatch";
          inherit passed;
        }];
      };
  };

  # Build a single error record from a failing typeCheck param. Shared
  # by collecting / firstN to keep the record shape consistent.
  mkErrorRecord = param: {
    context = param.context;
    typeName = param.type.name;
    actual = describeValue param.value;
    path = param.path or [ ];
    reason = param.reason or "shape-mismatch";
    message = mkMessage param;
  };

  firstN = N: {
    typeCheck = { param, state }:
      if param.type.check param.value
      then { resume = true; inherit state; }
      else
        let
          current = state.collected;
          n = builtins.length current;
        in
        if state.aborted || n >= N
        then { resume = false; state = state // { aborted = true; }; }
        else {
          resume = false;
          state = {
            collected = current ++ [ (mkErrorRecord param) ];
            aborted = (n + 1) >= N;
          };
        };
  };

  summarize = {
    typeCheck = { param, state }:
      # Per-step state is forced via `deepSeq` and rebuilt as a fresh
      # literal attrset (no `//`-chain), so values stay concrete integers
      # across `foldl'` iterations. Without this, `state.byReason` and
      # the `passed`/`failed` scalars accumulate O(N)-depth thunk chains
      # that overflow the stack when forced — defeating the handler's
      # documented "bounded memory" guarantee.
      if param.type.check param.value
      then
        let
          newState = {
            byReason = state.byReason;
            passed = state.passed + 1;
            failed = state.failed;
          };
        in
        {
          resume = true;
          state = builtins.deepSeq newState newState;
        }
      else
        let
          reason = param.reason or "shape-mismatch";
          currentCount = state.byReason.${reason} or 0;
          merged = state.byReason // { ${reason} = currentCount + 1; };
          names = builtins.attrNames merged;
          # Rebuild byReason as a flat literal attrset so the next step's
          # lookups are O(1) and don't traverse a //-chain back to step 0.
          newByReason = builtins.listToAttrs (builtins.map
            (n:
              { name = n; value = merged.${n}; }
            )
            names);
          newState = {
            byReason = newByReason;
            passed = state.passed;
            failed = state.failed + 1;
          };
        in
        {
          resume = false;
          state = builtins.deepSeq newState newState;
        };
  };

  pretty = cfg:
    let _sourceMap = cfg.sourceMap or null; in {
      typeCheck = { param, state }:
        if param.type.check param.value
        then { resume = true; inherit state; }
        else
          let
            reason = param.reason or "shape-mismatch";
            line = "[${reason}] ${mkMessage param}";
          in
          {
            resume = false;
            state = state ++ [ line ];
          };
    };

  policy = {
    inherit strict collecting logging firstN summarize pretty;
  };

in
api.namespace {
  description = "typecheck effect handlers: strict / collecting / logging / firstN / summarize / pretty under `policy.*`; bridge between the type system and effects.";
  doc = "Reusable typeCheck handlers. Use `policy.<name>` for the canonical surface; legacy `strict`/`collecting`/`logging` attributes are preserved for back-compat.";
  value = {
    strict = api.leaf {
      value = strict;
      description = "policy.strict: throws on the first failing typeCheck via `builtins.throw`; resumes with true on success. Halts evaluation on error.";
      doc = ''
        Strict typeCheck handler: throws on first type error.
        Resumes with true on success (check passed).

        Use when type errors should halt evaluation immediately.
        State: unused (pass null).
      '';
    };

    collecting = api.leaf {
      value = collecting;
      description = "policy.collecting: accumulates every failing typeCheck into state as a list of `{ context, typeName, actual, message, path, reason }`.";
      doc = ''
        Collecting typeCheck handler: accumulates errors in state.
        Resumes with `true` on success, `false` on failure (computation continues).

        State shape: list of `{ context, typeName, actual, message, path, reason }`
        Initial state: `[]`
      '';
      tests = {
        "passes-good-value" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = collecting.typeCheck {
                param = { type = IntT; context = "test"; value = 42; path = [ ]; };
                state = [ ];
              };
            in
            r.resume;
          expected = true;
        };
        "collects-bad-value" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = collecting.typeCheck {
                param = { type = IntT; context = "test"; value = "nope"; path = [ ]; };
                state = [ ];
              };
            in
            builtins.length r.state;
          expected = 1;
        };
        "carries-path-in-state" = {
          expr =
            let
              P = fx.diag.positions;
              IntT = { name = "Int"; check = builtins.isInt; };
              path = [ (P.Field "a") (P.Field "b") (P.Field "c") ];
              r = collecting.typeCheck {
                param = { type = IntT; context = "Int"; value = "nope"; inherit path; };
                state = [ ];
              };
            in
            (builtins.head r.state).path;
          expected = [
            (fx.diag.positions.Field "a")
            (fx.diag.positions.Field "b")
            (fx.diag.positions.Field "c")
          ];
        };
        "default-reason-is-shape-mismatch" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = collecting.typeCheck {
                param = { type = IntT; context = "Int"; value = "nope"; path = [ ]; };
                state = [ ];
              };
            in
            (builtins.head r.state).reason;
          expected = "shape-mismatch";
        };
        "carries-reason-in-state" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = collecting.typeCheck {
                param = {
                  type = IntT;
                  context = "Int";
                  value = null;
                  path = [ ];
                  reason = "missing-field";
                };
                state = [ ];
              };
            in
            (builtins.head r.state).reason;
          expected = "missing-field";
        };
      };
    };

    logging = api.leaf {
      value = logging;
      description = "policy.logging: records every typeCheck (pass and fail) in state with `passed` boolean; useful for tracing without aborting computation.";
      doc = ''
        Logging typeCheck handler: records every check (pass or fail) in state.
        Always resumes with the actual check result (boolean).

        State shape: list of `{ context, typeName, passed, path, reason }`
        Initial state: `[]`
      '';
      tests = {
        "logs-passing-check" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = logging.typeCheck {
                param = { type = IntT; context = "test"; value = 42; path = [ ]; };
                state = [ ];
              };
            in
            (builtins.head r.state).passed;
          expected = true;
        };
        "logs-failing-check" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = logging.typeCheck {
                param = { type = IntT; context = "test"; value = "no"; path = [ ]; };
                state = [ ];
              };
            in
            (builtins.head r.state).passed;
          expected = false;
        };
        "logging-records-reason" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = logging.typeCheck {
                param = {
                  type = IntT;
                  context = "test";
                  value = 42;
                  path = [ ];
                  reason = "deferred-pi";
                };
                state = [ ];
              };
            in
            (builtins.head r.state).reason;
          expected = "deferred-pi";
        };
        "logging-default-reason" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = logging.typeCheck {
                param = { type = IntT; context = "test"; value = 42; path = [ ]; };
                state = [ ];
              };
            in
            (builtins.head r.state).reason;
          expected = "shape-mismatch";
        };
      };
    };

    firstN = api.leaf {
      value = firstN;
      description = "policy.firstN N: bounded-collection handler keeping up to N failures, then setting `aborted = true` and dropping the rest. State stays bounded.";
      signature = "firstN : Int -> Handler";
      doc = ''
        Bounded-collection handler: collects up to N failures, then drops the rest.

        Useful for early-termination policies where the consumer only needs
        a handful of representative errors. After the Nth failure, `aborted`
        flips true and subsequent failures are silently dropped (state size
        stays bounded at N entries).

        State shape: `{ collected :: [errorRecord]; aborted :: Bool; }`
        Initial state: `{ collected = []; aborted = false; }`
      '';
      tests = {
        "firstN-1-of-3-keeps-only-first" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              h = (firstN 1).typeCheck;
              s0 = { collected = [ ]; aborted = false; };
              s1 = (h { param = { type = IntT; context = "a"; value = "x"; path = [ ]; }; state = s0; }).state;
              s2 = (h { param = { type = IntT; context = "b"; value = "y"; path = [ ]; }; state = s1; }).state;
              s3 = (h { param = { type = IntT; context = "c"; value = "z"; path = [ ]; }; state = s2; }).state;
            in
            {
              len = builtins.length s3.collected;
              firstCtx = (builtins.head s3.collected).context;
              aborted = s3.aborted;
            };
          expected = { len = 1; firstCtx = "a"; aborted = true; };
        };
        "firstN-passes-through-good-values" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (firstN 2).typeCheck {
                param = { type = IntT; context = "ok"; value = 42; path = [ ]; };
                state = { collected = [ ]; aborted = false; };
              };
            in
            r.resume && r.state.collected == [ ] && !r.state.aborted;
          expected = true;
        };
        "firstN-aborts-exactly-at-N" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              h = (firstN 2).typeCheck;
              s0 = { collected = [ ]; aborted = false; };
              s1 = (h { param = { type = IntT; context = "a"; value = "x"; path = [ ]; }; state = s0; }).state;
              s2 = (h { param = { type = IntT; context = "b"; value = "y"; path = [ ]; }; state = s1; }).state;
            in
            { afterFirst = s1.aborted; afterSecond = s2.aborted; };
          expected = { afterFirst = false; afterSecond = true; };
        };
        "firstN-carries-reason-in-record" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (firstN 3).typeCheck {
                param = {
                  type = IntT;
                  context = "Int";
                  value = "x";
                  path = [ ];
                  reason = "predicate-failed";
                };
                state = { collected = [ ]; aborted = false; };
              };
            in
            (builtins.head r.state.collected).reason;
          expected = "predicate-failed";
        };
      };
    };

    summarize = api.leaf {
      value = summarize;
      description = "policy.summarize: bounded-memory grouping by `reason`; tracks counts per reason plus pass/fail totals. State is O(K) in distinct reasons, not O(N).";
      doc = ''
        Bounded-memory grouping handler: counts failures by `reason`, drops
        per-failure data (value/path/context/message) so memory stays O(K)
        in the number of distinct reasons rather than O(N) in the number
        of effects.

        Use for high-volume validation where individual error records would
        blow up state — only the aggregate matters.

        State shape: `{ byReason :: { <reason> = Int; ... }; passed :: Int; failed :: Int; }`
        Initial state: `{ byReason = {}; passed = 0; failed = 0; }`
      '';
      tests = {
        "summarize-groups-by-reason" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              h = summarize.typeCheck;
              s0 = { byReason = { }; passed = 0; failed = 0; };
              mk_ = reason: { type = IntT; context = "c"; value = "x"; path = [ ]; inherit reason; };
              s1 = (h { param = mk_ "shape-mismatch"; state = s0; }).state;
              s2 = (h { param = mk_ "shape-mismatch"; state = s1; }).state;
              s3 = (h { param = mk_ "predicate-failed"; state = s2; }).state;
            in
            s3.byReason;
          expected = { shape-mismatch = 2; predicate-failed = 1; };
        };
        "summarize-counts-pass-and-fail" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              h = summarize.typeCheck;
              s0 = { byReason = { }; passed = 0; failed = 0; };
              s1 = (h { param = { type = IntT; context = "ok"; value = 42; path = [ ]; }; state = s0; }).state;
              s2 = (h { param = { type = IntT; context = "bad"; value = "x"; path = [ ]; }; state = s1; }).state;
              s3 = (h { param = { type = IntT; context = "ok"; value = 7; path = [ ]; }; state = s2; }).state;
            in
            { passed = s3.passed; failed = s3.failed; };
          expected = { passed = 2; failed = 1; };
        };
        "summarize-default-reason" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = summarize.typeCheck {
                param = { type = IntT; context = "c"; value = "x"; path = [ ]; };
                state = { byReason = { }; passed = 0; failed = 0; };
              };
            in
            r.state.byReason;
          expected = { shape-mismatch = 1; };
        };
        "summarize-bounded-memory-10K-stream" = {
          # Feed 10,000 failing effects of two reasons; verify the final
          # state has only the aggregate counts (3 top-level keys) with no
          # per-error records carried.
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              h = summarize.typeCheck;
              s0 = { byReason = { }; passed = 0; failed = 0; };
              step = state: i:
                let reason = if i / 2 * 2 == i then "shape-mismatch" else "predicate-failed";
                in (h {
                  param = { type = IntT; context = "c"; value = "x"; path = [ ]; inherit reason; };
                  inherit state;
                }).state;
              final = builtins.foldl' step s0 (builtins.genList (i: i) 10000);
            in
            {
              shape = final.byReason."shape-mismatch";
              pred = final.byReason."predicate-failed";
              total = final.failed;
              keys = builtins.attrNames final;
            };
          expected = {
            shape = 5000;
            pred = 5000;
            total = 10000;
            keys = [ "byReason" "failed" "passed" ];
          };
        };
      };
    };

    pretty = api.leaf {
      value = pretty;
      description = "policy.pretty cfg: emits one pre-formatted `[reason] expected T at <loc>, got <actualType>` line per failure; renders the Position-list path with per-segment separators.";
      signature = "pretty : { sourceMap? } -> Handler";
      doc = ''
        Display-rendering handler: emits one pre-formatted line per failure.

        Renders the blame location by concatenating each Position's
        `segment` field (`.field`, `[i]`, `#Tag` carry their own
        separator). Falls back to `context` when the path is empty.
        Each line is shaped:
          [reason] expected typeName at <location>, got <actualType>

        `cfg.sourceMap` is reserved for future source-span annotation; not
        consumed yet.

        State shape: `[String]` (one entry per failure; consumer joins with
        newline for display).
        Initial state: `[]`
      '';
      tests = {
        "pretty-renders-field-path" = {
          expr =
            let
              P = fx.diag.positions;
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (pretty { }).typeCheck {
                param = {
                  type = IntT;
                  context = "Int";
                  value = "nope";
                  path = [ (P.Field "user") (P.Field "age") ];
                  reason = "shape-mismatch";
                };
                state = [ ];
              };
            in
            builtins.head r.state;
          expected = "[shape-mismatch] Expected Int at .user.age, got string";
        };
        "pretty-renders-mixed-segments" = {
          expr =
            let
              P = fx.diag.positions;
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (pretty { }).typeCheck {
                param = {
                  type = IntT;
                  context = "Int";
                  value = "nope";
                  path = [ (P.Field "user") (P.Field "age") (P.Elem 0) ];
                  reason = "missing-field";
                };
                state = [ ];
              };
            in
            builtins.head r.state;
          expected = "[missing-field] Expected Int at .user.age[0], got string";
        };
        "pretty-falls-back-to-context-when-no-path" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (pretty { }).typeCheck {
                param = {
                  type = IntT;
                  context = "Int";
                  value = "x";
                  path = [ ];
                  reason = "shape-mismatch";
                };
                state = [ ];
              };
            in
            builtins.head r.state;
          expected = "[shape-mismatch] Expected Int, got string";
        };
        "pretty-skips-passing-checks" = {
          expr =
            let
              IntT = { name = "Int"; check = builtins.isInt; };
              r = (pretty { }).typeCheck {
                param = { type = IntT; context = "Int"; value = 42; path = [ ]; };
                state = [ "earlier" ];
              };
            in
            r.state;
          expected = [ "earlier" ];
        };
        "pretty-deterministic-over-multiple-failures" = {
          expr =
            let
              P = fx.diag.positions;
              IntT = { name = "Int"; check = builtins.isInt; };
              h = (pretty { }).typeCheck;
              s0 = [ ];
              s1 = (h { param = { type = IntT; context = "a"; value = "x"; path = [ (P.Field "p") (P.Field "q") ]; reason = "shape-mismatch"; }; state = s0; }).state;
              s2 = (h { param = { type = IntT; context = "b"; value = false; path = [ ]; reason = "predicate-failed"; }; state = s1; }).state;
            in
            s2;
          expected = [
            "[shape-mismatch] Expected Int at .p.q, got string"
            "[predicate-failed] Expected Int, got bool (b)"
          ];
        };
      };
    };

    policy = api.leaf {
      value = policy;
      description = "policy: canonical grouped surface for typecheck handlers.";
      doc = "Grouped `strict`/`collecting`/`logging`/`firstN`/`summarize`/`pretty` handlers.";
    };
  };
}
