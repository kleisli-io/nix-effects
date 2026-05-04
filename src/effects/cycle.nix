# nix-effects cycle: Reactive FRP in the Cycle.js tradition
#
# Cycle.js (Staltz 2014) on effect streams: a pure, pull-based FRP system
# where nix-effects streams replace Observables and algebraic effect handlers
# replace I/O drivers.
#
#   Cycle.js concept       nix-effects / cycle.nix
#   ────────────────────── ──────────────────────────────────────────────────
#   Observable<T>          Computation (Step r T)  (pull-based lazy stream)
#   main                   Component = Sources -> Sinks
#   Sources                { name: Stream response }  flowing IN to main
#   Sinks                  { name: Stream request  }  flowing OUT of main
#   Driver                 Stream request -> Stream response
#   xs.merge(a$, b$)       stream.merge [a b]   (OR: all events from any stream)
#   xs.combine(a$, b$)     stream.zip a b       (AND: wait for both, pair them)
#   startWith(x)           stream.startWith x s (prepend seed before first event)
#   mapTo(v)               stream.mapTo v s     (map each event to a constant)
#   MVI                    mkMVI { intent; model; view; init }
#   isolate(Comp, scope)   isolate Comp scope
#   run(main, drivers)     run main drivers
#
# REACTIVE PROGRAMMING
# ─────────────────────
# Cycle.js is built on reactive ("inside-out") programming: instead of Foo
# calling methods on Bar (passive/proactive), Bar observes events from Foo
# and manages its own state in response.  Each module is self-responsible.
# nix-effects streams are the reactive primitive: lazy, pull-based sequences
# of values.  Pulling the next element of a stream IS the message-passing.
#
# THE USER-COMPUTER DIALOGUE (Haskell 1.0, Staltz 2014)
# ──────────────────────────────────────────────────────
# `main` and the drivers are two sides of a conversation.  `main` is pure —
# it never performs I/O.  Drivers bridge the external world.
#
# CIRCULAR WIRING WITHOUT lib.fix
# ────────────────────────────────
# Nix evaluates lazily.  The mutual `let`
#
#     let sinks   = main sources;
#         sources = mapAttrs (n: drv: drv sinks.${n}) drivers;
#     in sinks;
#
# resolves the cycle through lazy thunk forcing.  When `main` pulls from
# `sources.tick`, Nix forces the thunk → pulls from `sinks.tick` → advances
# `main`.  The pull-step IS the message.  Identical to Haskell's
# `Dialogue = [Response] -> [Request]` (Henderson 1980).
#
# STREAM SEMANTICS: OR vs AND
# ────────────────────────────
# Two stream combinators are central to Cycle.js patterns:
#
#   merge (OR)   — combine events from any of N streams into one stream.
#                  In nix-effects (deterministic, pull-based): sequential
#                  concat.  Use for action streams that come from multiple
#                  sources (e.g. increment + decrement clicks).
#
#   zip   (AND)  — pair up elements from two streams step-by-step.
#                  Both streams must have a value to produce output.  Use
#                  for combining independent state slices (weight + height
#                  → BMI).  Equivalent to Cycle.js `xs.combine()`.
#
# INITIALIZATION WITH startWith
# ──────────────────────────────
# Cycle.js apps need a "kickstart": the first render must happen before any
# user event arrives.  In Cycle.js: `events$.startWith(initialValue)`.  In
# nix-effects: `stream.startWith initialValue eventStream` prepends one
# element to any stream.  `stream.scanl` also serves this role: it always
# emits the seed as its first element (equivalent to `fold` + `startWith`).
#
# MODEL-VIEW-INTENT
# ─────────────────
# MVI (Trygve Reenskaug 1979 / Staltz 2014) decomposes `main` into three
# pure functions:
#
#   intent : Sources -> Stream action
#            Interpret user input as semantic action streams.
#            ("translate user language → digital language")
#
#   model  : state -> action -> state
#            Pure fold; `stream.scanl model init actions` → state stream.
#            ("manage state from action events")
#
#   view   : Stream state -> Sinks
#            Map state stream to sink streams (virtual DOM, log, etc.).
#            ("translate digital language → user language")
#
#   init   : initial state (seed for scanl — always emitted as first element)
#
# MVI is sliceable: `main = srcs: view (model (intent srcs))` is the
# simplest possible form.  Split further when functions grow large.
#
# DRIVERS
# ───────
# Drivers are `Stream request -> Stream response` functions.  Three shapes:
#
#   Bidirectional — yields one response per request (most common)
#   Write-only    — returns `stream.done null`; ignores its output
#                   (e.g. a logger: `_sinkStream: stream.done null`)
#   Read-only     — ignores the sink; yields an independent stream
#                   (e.g. `drivers.list xs`, `drivers.props config`)
#
# Drivers are often built via factory functions that capture configuration:
#
#   makeMyDriver = config: sinkStream: ... ;  # factory returns a driver
#
# Use `mkDriver { step; initState? }` for stateful bidirectional drivers.
#
# COMPONENTS AND ISOLATION
# ────────────────────────
# Any `Sources -> Sinks` function is a component.  All Cycle.js apps can be
# reused as components in larger apps — the same `main` that is passed to
# `run` is also a valid child component.  Compose by calling child
# components inside parent's `main` and merging their sinks.
#
# `isolate Component scope` namespaces a child's sink keys, preventing
# sibling collision.  Use when running two instances of the same component
# (e.g. weight slider + height slider in a BMI calculator):
#
#   WeightSlider = isolate LabeledSlider "weight";
#   HeightSlider = isolate LabeledSlider "height";
#
# PROPS PATTERN
# ─────────────
# Child components receive static configuration via a `props` source stream.
# The parent (or `run`) supplies props via a read-only driver:
#
#   run MyComp { props = drivers.props { label = "Weight"; value = 70; }; }
#
# Inside `MyComp`, `sources.props` is a stream emitting the config object.
#
# PER-COMPONENT HANDLER SCOPE
# ────────────────────────────
# The optional `handlers : state -> { effectName = handler }` field in
# `mkMVI` exposes dynamic algebraic effect handlers re-derived from each
# model state step.  Child handlers bubble up through `composeHandlers`,
# mirroring tea.nix's `handlers` for `nest`.
#
# References:
#   Staltz (2014) "Cycle.js" https://cycle.js.org/
#   Staltz (2015) "Unidirectional User Interface Architectures"
#   Henderson (1980) "Functional Geometry" (Dialogue metaphor)
#   Reenskaug (1979) "MVC" http://heim.ifi.uio.no/~trygver/themes/mvc/
#   Czaplicki (2012) "Elm: Concurrent FRP" (MVI lineage)
{ fx, api, lib, ... }:

let
  inherit (fx.kernel) pure bind;
  inherit (api) mk;
  inherit (fx.public) stream;


  # ── mkDriver ─────────────────────────────────────────────────────────────

  mkDriver = mk {
    doc = ''
      Build a stateful bidirectional driver from a step function.

      ```
      mkDriver : { step : state -> request -> { state; response }; initState? } -> Driver
      ```

      `step` is called once per sink element; it receives the current driver
      state and the request, and must return `{ state; response }`.  The
      returned `response` becomes the next element of the source stream.

      `initState` defaults to `null`.

      Example — a counter driver that returns how many requests it has seen:

      ```nix
      counterDriver = mkDriver {
        initState = 0;
        step = n: _req: { state = n + 1; response = n + 1; };
      };
      ```
    '';
    value = { step, initState ? null }:
      # Returns a `Stream request -> Stream response` function.
      let
        go = state: sinkStream:
          bind sinkStream (elem:
            if elem._tag == "Done" then stream.done null
            else
              let r = step state elem.head;
              in pure {
                _tag = "More";
                head = r.response;
                tail = go r.state elem.tail;
              });
      in go initState;
    tests = {
      "mkDriver-basic-counter" = {
        expr =
          let
            drv = mkDriver.value {
              initState = 0;
              step = n: _: { state = n + 1; response = n + 1; };
            };
            src = drv (stream.fromList [ "a" "b" "c" ]);
          in (stream.toList src).value;
        expected = [ 1 2 3 ];
      };
      "mkDriver-write-only-done" = {
        expr =
          let
            drv = mkDriver.value {
              step = _s: _r: { state = null; response = null; };
            };
            src = drv (stream.done null);
          in src.value._tag;
        expected = "Done";
      };
    };
  };

  # ── built-in drivers ─────────────────────────────────────────────────────

  drivers = mk {
    doc = ''
      Built-in driver constructors.

      `list xs`      — Read-only driver.  Yields each element of `xs` as the
                       source stream regardless of what sinks send.

      `identity`     — Bidirectional echo driver.  Source mirrors sink exactly
                       (one element in, one element out).

      `fold f z`     — Stateful bidirectional driver.  Accumulates requests with
                       `f z req`, emitting the running total as each source element.
                       Useful for building stateful services (counters, stores).

      `const v`      — Read-only driver.  Always yields `v` as the single source
                       element, ignoring sinks.

      `writeOnly`    — Write-only driver.  Consumes the sink stream and returns an
                       empty source (`stream.done null`).  Use for side-effecting
                       channels (logging, metrics) where `main` never reads back.
                       Equivalent to Cycle.js's one-liner log driver:
                       `run(main, { log: msg$ => { msg$.addListener(...) } })`.

      `props config` — Read-only props driver.  Emits `config` as a single
                       element source stream, ignoring sinks.  Used to pass
                       static configuration ("props") to child components.
                       Equivalent to Cycle.js's `() => xs.of(config)` driver.

      **Factory pattern** — drivers are plain functions; wrap in a factory to\n      capture configuration:

      ```nix
      makeMyDriver = peerId: sinkStream:
        # consume sinkStream, return source stream based on peerId
        ...;

      run main { sock = makeMyDriver "B23A79D5-..."; }
      ```

      Example:

      ```nix
      run myMain {
        nums   = drivers.list [ 1 2 3 ];
        log    = drivers.writeOnly;           # consume only, no source
        props  = drivers.props { label = "Weight"; value = 70; };
        acc    = drivers.fold builtins.add 0;
      }
      ```
    '';
    value = {
      # Read-only: yield each element of xs; ignore sinks.
      list = xs: _sinkStream: stream.fromList xs;

      # Identity: source mirrors sink.
      identity = mkDriver.value {
        step = _s: req: { state = null; response = req; };
      };

      # Stateful fold: accumulate requests, emit running total.
      fold = f: z:
        mkDriver.value {
          initState = z;
          step = acc: req: let next = f acc req; in { state = next; response = next; };
        };

      # Const: always emit a single value, ignore sinks.
      const = v: _sinkStream: stream.fromList [ v ];

      # Write-only: consume sink, return empty source.
      # Equivalent to Cycle.js's one-liner log driver.
      writeOnly = _sinkStream: stream.done null;

      # Props: pass a static configuration attrset as a single-element source.
      # The child component reads `sources.props` and processes the config.
      props = config: _sinkStream: stream.fromList [ config ];
    };
    tests = {
      "drivers-list-yields-elements" = {
        expr = (stream.toList (drivers.value.list [ 10 20 ] (stream.done null))).value;
        expected = [ 10 20 ];
      };
      "drivers-identity-echo" = {
        expr =
          let src = drivers.value.identity (stream.fromList [ "x" "y" ]);
          in (stream.toList src).value;
        expected = [ "x" "y" ];
      };
      "drivers-fold-running-sum" = {
        expr =
          let src = drivers.value.fold builtins.add 0 (stream.fromList [ 1 2 3 ]);
          in (stream.toList src).value;
        expected = [ 1 3 6 ];
      };
      "drivers-const-single-value" = {
        expr =
          let src = drivers.value.const 42 (stream.done null);
          in (stream.toList src).value;
        expected = [ 42 ];
      };
      "drivers-writeOnly-returns-done" = {
        # Write-only driver produces an empty source — main never reads back.
        expr = (drivers.value.writeOnly (stream.fromList [ "a" "b" ])).value._tag;
        expected = "Done";
      };
      "drivers-props-emits-config" = {
        expr =
          let src = drivers.value.props { label = "Weight"; value = 70; } (stream.done null);
          in (stream.toList src).value;
        expected = [ { label = "Weight"; value = 70; } ];
      };
    };
  };

  # ── run ──────────────────────────────────────────────────────────────────

  run = mk {
    doc = ''
      Wire a `main` component to a set of drivers.

      ```
      run : Component -> { name: Driver } -> Sinks
      ```

      `main` is a pure function `Sources -> Sinks`.  `drivers` is an attrset
      mapping driver names to `Stream request -> Stream response` functions.

      The cycle is resolved purely by Nix laziness — no `lib.fix`, no subjects:

      ```nix
      let sinks   = main sources;
          sources = mapAttrs (n: drv: drv (sinks.''${n} or stream.done null)) drivers;
      in sinks
      ```

      When `main` pulls from `sources.foo`, Nix forces the thunk, which pulls
      from `sinks.foo`, which advances `main`.  The pull-step IS the dialogue.

      Any sink name not matched by a driver is silently ignored (and vice-versa
      — drivers whose sink name is absent from sinks receive an empty stream).

      Example:

      ```nix
      let app = run myMain {
            nums = drivers.list [ 1 2 3 ];
            log  = drivers.identity;
          };
      in (stream.toList app.log).value   # => processed elements
      ```
    '';
    value = main: driverMap:
      let
        sinks   = main sources;
        sources = lib.mapAttrs
          (name: drv: drv (sinks.${name} or (stream.done null)))
          driverMap;
      in sinks;
    tests = {
      "run-identity-round-trip" = {
        expr =
          let
            myMain = srcs: { echo = stream.map (x: x * 2) srcs.nums; };
            sinks  = run.value myMain {
              nums = drivers.value.list [ 1 2 3 ];
              echo = drivers.value.identity;
            };
          in (stream.toList sinks.echo).value;
        expected = [ 2 4 6 ];
      };
      "run-missing-driver-sink-ignored" = {
        expr =
          let
            myMain = _srcs: { out = stream.fromList [ "a" ]; };
            sinks  = run.value myMain {};
          in (stream.toList sinks.out).value;
        expected = [ "a" ];
      };
    };
  };

  # ── mkMVI ────────────────────────────────────────────────────────────────

  mkMVI = mk {
    doc = ''
      Decompose a component into Model-View-Intent.

      ```
      mkMVI : { intent  : Sources -> Stream action
              ; model   : state -> action -> state
              ; view    : Stream state -> Sinks
              ; init    : state
              ; handlers? : state -> { effectName = handler }
              } -> Component
      ```

      `mkMVI` composes the three MVI phases into a `Sources -> Sinks` function:

        1. **intent** — filters/transforms source streams into an action stream.
        2. **model**  — `stream.scanl model init actions` produces a state stream.
        3. **view**   — maps the state stream to sinks.

      The optional **handlers** field exposes per-state algebraic effect
      handlers (mirroring `tea.nix`'s `handlers`).  When present, the returned
      component carries a `.handlers : Stream state -> Stream handlers` stream
      so that parent components or `composeHandlers` can aggregate them.

      Example:

      ```nix
      counter = mkMVI {
        init   = 0;
        intent = srcs: stream.filter (x: x != null) srcs.action;
        model  = n: action:
          if action == "inc" then n + 1
          else if action == "dec" then n - 1
          else n;
        view   = state_: {
          dom = stream.map (n: { text = builtins.toString n; }) state_;
        };
      };
      ```
    '';
    value = { intent, model, view, init, handlers ? null }:
      sources:
        let
          actions = intent sources;
          state_  = stream.scanl model init actions;
          sinks   = view state_;
        in
          sinks //
          (lib.optionalAttrs (handlers != null) {
            _handlers = stream.map handlers state_;
          });
    tests = {
      "mkMVI-basic-counter" = {
        expr =
          let
            comp = mkMVI.value {
              init   = 0;
              intent = srcs: srcs.action;
              model  = n: act: if act == "inc" then n + 1 else n;
              view   = state_: { display = stream.map builtins.toString state_; };
            };
            sinks = comp { action = stream.fromList [ "inc" "inc" "inc" ]; };
          in (stream.toList sinks.display).value;
        expected = [ "0" "1" "2" "3" ];
      };
      "mkMVI-with-handlers" = {
        # Call each handler to verify the dynamic value (lambdas can't be equality-compared).
        expr =
          let
            comp = mkMVI.value {
              init   = 0;
              intent = srcs: srcs.action;
              model  = n: act: if act == "inc" then n + 1 else n;
              view   = state_: { display = stream.map builtins.toString state_; };
              handlers = n: { myEffect = _: n; };
            };
            sinks   = comp { action = stream.fromList [ "inc" ]; };
            results = stream.map (h: h.myEffect "req") sinks._handlers;
          in (stream.toList results).value;
        expected = [ 0 1 ];
      };
    };
  };

  # ── isolate ──────────────────────────────────────────────────────────────

  isolate = mk {
    doc = ''
      Namespace a component's sink keys to prevent collision.

      ```
      isolate : Component -> scope:string -> Component
      ```

      All sink keys produced by `component` are prefixed with `"scope-"`.
      Source keys are filtered to only those matching `"scope-*"` and passed
      to the component with the prefix stripped, so the child component sees
      only its own slice of sources.

      This mirrors Cycle.js `isolate(Component, scope)`.

      Example:

      ```nix
      parent = sources:
        let
          childA = isolate MyComp "a" sources;
          childB = isolate MyComp "b" sources;
        in {
          "a-log" = childA."a-log";
          "b-log" = childB."b-log";
        };
      ```
    '';
    value = component: scope: sources:
      let
        # Strip scope prefix from source keys, pass only scoped entries.
        prefix    = "${scope}-";
        prefixLen = builtins.stringLength prefix;
        localSrcs = lib.mapAttrs'
          (k: v: { name = builtins.substring prefixLen (builtins.stringLength k) k; value = v; })
          (lib.filterAttrs (k: _: lib.hasPrefix prefix k) sources);
        localSinks = component localSrcs;
      in
        lib.mapAttrs' (k: v: { name = prefix + k; value = v; }) localSinks;
    tests = {
      "isolate-namespaces-sinks" = {
        expr =
          let
            myComp = srcs: { out = srcs.in_ or (stream.done null); };
            scoped = isolate.value myComp "child" { "child-in_" = stream.fromList [ 1 ]; };
          in builtins.attrNames scoped;
        expected = [ "child-out" ];
      };
      "isolate-passes-correct-source-slice" = {
        expr =
          let
            myComp = srcs: { out = srcs.data; };
            scoped = isolate.value myComp "x" { "x-data" = stream.fromList [ 42 ]; };
          in (stream.toList scoped."x-out").value;
        expected = [ 42 ];
      };
    };
  };

  # ── composeHandlers ───────────────────────────────────────────────────────

  composeHandlers = mk {
    doc = ''
      Aggregate per-component handler streams from multiple components.

      ```
      composeHandlers : [Component output] -> Stream { effectName = handler }
      ```

      Each component output (the sinks attrset) may expose a `_handlers` stream
      (produced by `mkMVI` when `handlers` is set).  `composeHandlers` zips all
      present `_handlers` streams together, merging handler attrsets at each
      step, with later entries in the list taking precedence.

      This mirrors `tea.nix`'s `composedHandlers` for `nest`, allowing a parent
      to collect all child handlers (which themselves may collect grandchildren).

      Example:

      ```nix
      let
        childASinks = isolate CompA "a" sources;
        childBSinks = isolate CompB "b" sources;
        allHandlers = composeHandlers [ childASinks childBSinks mySinks ];
      in ...
      ```
    '';
    value = sinksList:
      let
        handlerStreams = builtins.filter (s: s != null)
          (map (sinks: sinks._handlers or null) sinksList);
      in
        if handlerStreams == [] then stream.done null
        else
          builtins.foldl'
            (acc: hs: stream.map (pair: pair.fst // pair.snd) (stream.zip acc hs))
            (builtins.head handlerStreams)
            (builtins.tail handlerStreams);
    tests = {
      "composeHandlers-merges-two" = {
        expr =
          let
            s1 = { _handlers = stream.fromList [ { a = 1; } ]; };
            s2 = { _handlers = stream.fromList [ { b = 2; } ]; };
            merged = composeHandlers.value [ s1 s2 ];
          in (stream.toList merged).value;
        expected = [ { a = 1; b = 2; } ];
      };
      "composeHandlers-later-takes-precedence" = {
        expr =
          let
            s1 = { _handlers = stream.fromList [ { k = 1; } ]; };
            s2 = { _handlers = stream.fromList [ { k = 2; } ]; };
            merged = composeHandlers.value [ s1 s2 ];
          in (stream.toList merged).value;
        expected = [ { k = 2; } ];
      };
      "composeHandlers-empty-list-is-done" = {
        expr = (composeHandlers.value []).value._tag;
        expected = "Done";
      };
      "composeHandlers-no-handlers-field-ignored" = {
        expr =
          let
            s1 = { out = stream.fromList [ 1 ]; };  # no _handlers
            s2 = { _handlers = stream.fromList [ { x = 9; } ]; };
            merged = composeHandlers.value [ s1 s2 ];
          in (stream.toList merged).value;
        expected = [ { x = 9; } ];
      };
    };
  };

  # ── communication-between-components ────────────────────────────────────
  #
  # Components communicate by sharing sink/source names.  Component A writes to
  # sink "bus"; Component B reads from source "bus".  The driver for "bus" is
  # just `drivers.identity` — the message passes through the pull-step
  # unchanged.  Use `isolate` to prevent naming collisions between siblings.

in mk {
  doc = ''
    cycle.nix — Reactive FRP in the Cycle.js tradition for nix-effects.

    The cycle framework implements the user-computer dialogue pattern:
    `main` (your program) and the drivers (the world) are two sides of a
    reactive conversation mediated by pull-based nix-effects streams.

    ## Quick start — counter (Cycle.js basic example)

    ```nix
    let
      cycle = fx.effects.cycle;

      # intent: merge dec (−1) and inc (+1) action streams
      intent = srcs:
        fx.stream.concat
          (fx.stream.map (_: -1) srcs.dec)
          (fx.stream.map (_: 1)  srcs.inc);

      # model: fold actions into running count
      model  = n: delta: n + delta;

      # view: emit the current count as a display attrset
      view   = state_: {
        dom = fx.stream.map (n: { count = n; }) state_;
      };

      app = cycle.run (cycle.mkMVI { init = 0; inherit intent model view; }) {
        dec = cycle.drivers.list [ null null ];      # 2 dec events
        inc = cycle.drivers.list [ null null null ]; # 3 inc events
        dom = cycle.drivers.identity;
      };
    in (fx.stream.toList app.dom).value
    # => [{count=0} {count=-1} {count=-2} {count=-1} {count=0} {count=1}]
    ```

    ## BMI calculator — AND semantics with `fx.stream.zip`

    ```nix
    main = srcs:
      let state = fx.stream.map
            (pair: let w = pair.fst; h = pair.snd;
                   in { weight = w; height = h;
                        bmi = builtins.div (w * 10000) (h * h); })
            (fx.stream.zip srcs.weight srcs.height);
      in { bmi = state; };

    cycle.run main {
      weight = cycle.drivers.list [ 70 80 ];
      height = cycle.drivers.list [ 170 180 ];
      bmi    = cycle.drivers.identity;
    }
    ```

    ## Props pattern — configuring a child component

    ```nix
    MySlider = sources:
      let value = fx.stream.map (p: p.value) sources.props;
      in { display = fx.stream.map builtins.toString value; };

    cycle.run MySlider {
      props   = cycle.drivers.props { label = "Weight"; unit = "kg"; value = 70; };
      display = cycle.drivers.identity;
    }
    ```

    ## Multiple instances of same component (isolate)

    ```nix
    main = srcs:
      let
        WeightSlider = cycle.isolate LabeledSlider "weight";
        HeightSlider = cycle.isolate LabeledSlider "height";
        w = WeightSlider srcs;
        h = HeightSlider srcs;
      in w // h;

    cycle.run main {
      "weight-props"   = cycle.drivers.props { label = "Weight"; value = 70;  };
      "height-props"   = cycle.drivers.props { label = "Height"; value = 170; };
      "weight-display" = cycle.drivers.identity;
      "height-display" = cycle.drivers.identity;
    }
    ```

    ## Write-only driver (logging, metrics)

    ```nix
    cycle.run main {
      log = cycle.drivers.writeOnly;  # main writes to sinks.log; no source back
    }
    ```

    ## Driver factory pattern

    ```nix
    makeMyDriver = config:      # factory captures config
      mkDriver {
        initState = config.initial;
        step = state: req: { state = state + 1; response = "''${req}-''${builtins.toString state}"; };
      };

    cycle.run main { chan = makeMyDriver { initial = 0; }; }
    ```

    ## API

    | Name               | Type                                              | Purpose                          |
    |--------------------|---------------------------------------------------|----------------------------------|
    | `run`              | `Component -> { name: Driver } -> Sinks`          | Wire main to drivers             |
    | `mkMVI`            | `{ intent; model; view; init; handlers? } -> Component` | MVI component builder      |
    | `isolate`          | `Component -> scope -> Component`                 | Namespace child sinks/sources    |
    | `mkDriver`         | `{ step; initState? } -> Driver`                  | Build a stateful driver          |
    | `composeHandlers`  | `[Sinks] -> Stream handlers`                      | Aggregate per-component handlers |
    | `drivers.list`     | `[a] -> Driver`                                   | Read-only list source            |
    | `drivers.identity` | `Driver`                                          | Echo (sink mirrors source)       |
    | `drivers.fold`     | `(b->a->b) -> b -> Driver`                        | Stateful accumulating driver     |
    | `drivers.const`    | `a -> Driver`                                     | Single-value read-only source    |
    | `drivers.writeOnly`| `Driver`                                          | Consume sink, no source          |
    | `drivers.props`    | `config -> Driver`                                | Static config source             |

    ## Per-component handlers

    Add `handlers : state -> { effectName = handler }` to `mkMVI` to expose
    dynamic algebraic effect handlers.  The returned sinks include `_handlers`,
    a stream of handler attrsets re-derived from each state step.  Use
    `composeHandlers` to merge children's handler streams so effects can bubble
    up from grandchildren to ancestors.
  '';
  value = {
    inherit run mkMVI isolate mkDriver drivers composeHandlers;
  };
  tests = {
    "full-mvi-pipeline" = {
      expr =
        let
          intent = srcs: srcs.action;
          model  = n: act:
            if act == "inc" then n + 1
            else if act == "dec" then n - 1
            else n;
          view = state_: {
            dom = stream.map (n: { count = n; }) state_;
          };
          app = run.value (mkMVI.value { init = 0; inherit intent model view; }) {
            action = drivers.value.list [ "inc" "inc" "dec" ];
            dom    = drivers.value.identity;
          };
        in (stream.toList app.dom).value;
      expected = [
        { count = 0; }
        { count = 1; }
        { count = 2; }
        { count = 1; }
      ];
    };
    "counter-with-merge-and-mapTo" = {
      # The Cycle.js counter: merge dec/inc action streams using mapTo,
      # then fold into a running count with scanl.
      # Cycle.js: xs.merge(dec$.mapTo(-1), inc$.mapTo(+1)).fold((x,y)=>x+y, 0)
      expr =
        let
          decs    = stream.mapTo (-1) (stream.fromList [ null null ]);
          incs    = stream.mapTo   1  (stream.fromList [ null null null ]);
          actions = stream.merge [ decs incs ];         # [-1,-1, 1,1,1]
          count   = stream.scanl (n: a: n + a) 0 actions;
        in (stream.toList count).value;
      expected = [ 0 (-1) (-2) (-1) 0 1 ];
    };
    "startWith-provides-initial-value" = {
      # startWith prepends a seed so the view renders before any user event.
      # Cycle.js: sources.DOM.events('change').startWith(false).map(render)
      expr =
        let
          events = stream.fromList [ "a" "b" "c" ];
          seeded = stream.startWith "init" events;
        in (stream.toList seeded).value;
      expected = [ "init" "a" "b" "c" ];
    };
    "toggle-scanl-as-startWith" = {
      # scanl's seed is always emitted first — equivalent to startWith.
      # Mirrors the Cycle.js checkbox toggle example (Czaplicki 2012).
      expr =
        let
          clicks = stream.fromList [ null null null ]; # 3 clicks
          toggle = stream.scanl (s: _: !s) false clicks;
        in (stream.toList toggle).value;
      expected = [ false true false true ];
    };
    "bmi-combining-two-source-streams" = {
      # The Cycle.js BMI example: zip two independent state streams (AND semantics).
      # Cycle.js: xs.combine(weight$, height$).map(([w,h]) => bmi(w,h))
      # nix-effects: stream.zip (step-by-step pairing, equivalent for finite streams).
      expr =
        let
          weights = stream.fromList [ 70 80 90 ];
          heights = stream.fromList [ 170 170 180 ];
          state   = stream.map
            (pair:
              let w = pair.fst; h = pair.snd;
              in { weight = w; height = h;
                   bmi = builtins.div (w * 10000) (h * h); })
            (stream.zip weights heights);
        in (stream.toList state).value;
      expected = [
        { weight = 70; height = 170; bmi = 24; }
        { weight = 80; height = 170; bmi = 27; }
        { weight = 90; height = 180; bmi = 27; }
      ];
    };
    "props-pattern-child-receives-config" = {
      # Props pattern: child component receives static configuration via a
      # read-only source driver.  Mirrors Cycle.js's props source:
      # `run(LabeledSlider, { props: () => xs.of({label, value, ...}) })`
      expr =
        let
          MySlider = sources:
            let value = stream.map (p: p.value) sources.props;
            in { display = stream.map builtins.toString value; };
          sinks = run.value MySlider {
            props   = drivers.value.props { label = "Weight"; unit = "kg"; value = 70; };
            display = drivers.value.identity;
          };
        in (stream.toList sinks.display).value;
      expected = [ "70" ];
    };
    "write-only-driver-side-effect-channel" = {
      # Write-only driver: main writes to sinks.log; driver consumes it with no
      # source returned.  Mirrors Cycle.js: `run(main, { log: msg$ => ... })`
      expr =
        let
          main  = _srcs: { log = stream.fromList [ "msg1" "msg2" ]; };
          sinks = run.value main { log = drivers.value.writeOnly; };
        in (stream.toList sinks.log).value;
      expected = [ "msg1" "msg2" ];
    };
    "makeDriver-factory-pattern" = {
      # Driver factory: a function that captures config and returns a driver.
      # Mirrors Cycle.js: `function makeSockDriver(peerId) { return sockDriver; }`
      expr =
        let
          makePrefixDriver = prefix:
            mkDriver.value {
              initState = 0;
              step = n: req:
                { state    = n + 1;
                  response = "${prefix}${builtins.toString n}:${req}";
                };
            };
          drv = makePrefixDriver "ev";
          src = drv (stream.fromList [ "x" "y" "z" ]);
        in (stream.toList src).value;
      expected = [ "ev0:x" "ev1:y" "ev2:z" ];
    };
    "component-communication-via-shared-channel" = {
      # Component A produces numbers on "bus"; Component B increments them.
      # The "bus" driver (identity) passes values through the pull-step unchanged.
      expr =
        let
          compA = srcs: { bus = stream.map (x: x * 10) srcs.nums; };
          compB = srcs: { out = stream.map (x: x + 1)  srcs.bus;  };
          main  = srcs:
            let
              sA = compA srcs;
              sB = compB { bus = sA.bus; };
            in { bus = sA.bus; out = sB.out; };
          sinks = run.value main {
            nums = drivers.value.list [ 1 2 3 ];
            bus  = drivers.value.identity;
            out  = drivers.value.identity;
          };
        in (stream.toList sinks.out).value;
      expected = [ 11 21 31 ];
    };
    "multiple-instances-same-component-with-isolate" = {
      # Two instances of the same component with different scopes — no collision.
      # Mirrors the Cycle.js BMI weight/height slider example:
      #   WeightSlider = isolate(LabeledSlider, 'weight');
      #   HeightSlider = isolate(LabeledSlider, 'height');
      expr =
        let
          Counter = sources:
            let count = stream.scanl (n: _: n + 1) 0 sources.action;
            in { display = stream.map builtins.toString count; };
          main = srcs:
            let
              a = isolate.value Counter "a" srcs;
              b = isolate.value Counter "b" srcs;
            in a // b;
          sinks = run.value main {
            "a-action"  = drivers.value.list [ null null ];      # 2 ticks
            "b-action"  = drivers.value.list [ null null null ]; # 3 ticks
            "a-display" = drivers.value.identity;
            "b-display" = drivers.value.identity;
          };
        in {
          a = (stream.toList sinks."a-display").value;
          b = (stream.toList sinks."b-display").value;
        };
      expected = { a = [ "0" "1" "2" ]; b = [ "0" "1" "2" "3" ]; };
    };
    "per-component-handlers-bubble-up" = {
      # Child exposes handlers; parent collects via composeHandlers.
      expr =
        let
          child = mkMVI.value {
            init   = 10;
            intent = srcs: srcs.tick;
            model  = n: _: n + 1;
            view   = state_: { childOut = state_; };
            handlers = n: { childService = _: n; };
          };
          childSinks = child { tick = stream.fromList [ null null ]; };
          merged     = composeHandlers.value [ childSinks ];
          results    = stream.map (h: h.childService "req") merged;
        in (stream.toList results).value;
      expected = [ 10 11 12 ];
    };
    "isolate-sibling-components-no-collision" = {
      expr =
        let
          myComp = srcs: { out = srcs.in_; };
          main   = srcs:
            let
              a = isolate.value myComp "a" srcs;
              b = isolate.value myComp "b" srcs;
            in { "a-out" = a."a-out"; "b-out" = b."b-out"; };
          sinks = run.value main {
            "a-in_" = drivers.value.list [ 1 ];
            "b-in_" = drivers.value.list [ 2 ];
            "a-out" = drivers.value.identity;
            "b-out" = drivers.value.identity;
          };
        in {
          a = (stream.toList sinks."a-out").value;
          b = (stream.toList sinks."b-out").value;
        };
      expected = { a = [ 1 ]; b = [ 2 ]; };
    };
  };
}
