# nix-effects: effects, typed boundaries, and description-backed DSLs in pure Nix
#
# Usage:
#   let fx = import ./. { lib = nixpkgs.lib; };
#   in fx.run (fx.send "get" null) { get = ...; } initialState
{ pkgs ? (import ./pins.nix).nixpkgs { }, lib ? pkgs.lib, exposeInternals ? false, ... }:

let
  api = import ./src/api.nix { inherit lib; };

  # -- readSrc: directory walker --
  #
  # Walks `src/` building the fx tree. Every documented binding is an
  # `api.mk` wrap (or its aliases `api.leaf` / `api.namespace`) carrying
  # `{ description; doc; signature; value; tests }`.
  #
  # Two directory shapes:
  #
  #   Split module (`module.nix` present): sibling `<name>.nix` files
  #     are "parts" returning `{ scope; tests ? {} }`. `scope` is an
  #     attrset of bindings — typically `api.leaf` / `api.namespace`
  #     wraps; un-documented internal helpers may remain bare. `tests`
  #     are aggregated into `partTests` and threaded to `module.nix`,
  #     which assembles the curated public `value` via
  #     `inherit (self) ...;` and returns the wrap.
  #
  #   Plain dir (no `module.nix`): each `<name>.nix` file's return
  #     value becomes the dir's `<name>` slot. Files are expected to
  #     return an `api.mk` / `api.namespace` / `api.leaf` wrap; the
  #     dir aggregates them in an `api.mk` wrap with empty identity.
  #     Dirs that need their own description/doc carry a `module.nix`.
  #
  # `self` (cross-part fixpoint) is built two-view:
  #   - `selfForParts` — part-bindings shallow-unwrapped to bare values;
  #     subdirs left as wraps. Preserves call-site semantics:
  #     `self.<part-binding>` is the bare function/value, `self.<subdir>`
  #     is the wrap (with `.value`, `.tests`, etc.).
  #   - `selfRaw` — wraps everywhere. Passed to `module.nix` so that
  #     `value = { inherit (self) ...; }` carries the docs-bearing form.
  #
  # Collisions (duplicate scope keys, duplicate test names, subdir name
  # vs. scope binding) are hard errors. Each binding has exactly one
  # definition site.
  readSrc = dir: ctx:
    let
      entries = builtins.readDir dir;
      excluded = [ "api.nix" "module.nix" ];
      isNixFile = name: type:
        type == "regular"
        && lib.hasSuffix ".nix" name
        && !(builtins.elem name excluded);
      isSplitModule = entries ? "module.nix";

      # Subdirectories are nested namespaces in both modes. Each subdir's
      # readSrc result is an mk-wrapped node, so parent-level traversals
      # see only mk-wrapped children.
      subDirs = lib.foldlAttrs
        (acc: name: type:
          if type == "directory"
          then acc // { ${name} = readSrc (dir + "/${name}") ctx; }
          else acc
        )
        { }
        entries;

    in
    if isSplitModule then
      let
        partNames = builtins.attrNames (lib.filterAttrs isNixFile entries);
        importPart = n: s: import (dir + "/${n}") (ctx // { self = s; });

        isWrap = v:
          builtins.isAttrs v && (v._type or null) == "nix-effects-api";

        # Shallow unwrap: strip a top-level `api.leaf`/`api.mk` wrap to
        # its bare `.value` for `self.<binding>` consumption. MUST be
        # shallow — `api.extractValue` recurses via `mapAttrs` into every
        # nested attrset, which adds a thunk layer per HOAS term level
        # and stack-overflows on deep terms (e.g. 5000-element cons).
        # Bare bindings (un-documented helpers) pass through unchanged.
        unwrapTop = v: if isWrap v then v.value else v;

        # Single fix over both views. Parts see `selfForParts` (wraps
        # shallow-unwrapped to bare values; subdirs left as wraps).
        # `module.nix` sees `selfRaw` (wraps everywhere) so its curated
        # `value` inherits the docs-bearing form.
        selves = lib.fix (s:
          let
            partsScope = builtins.foldl'
              (acc: n:
                let
                  part = importPart n s.selfForParts;
                  scope = part.scope;
                  collisions = lib.intersectLists
                    (builtins.attrNames acc)
                    (builtins.attrNames scope);
                in
                if collisions != [ ]
                then throw "readSrc: ${toString dir}: duplicate binding(s) ${toString collisions}"
                else acc // scope
              )
              { }
              partNames;
            sdCollisions = lib.intersectLists
              (builtins.attrNames partsScope)
              (builtins.attrNames subDirs);
          in
          if sdCollisions != [ ]
          then throw "readSrc: ${toString dir}: subdirectory name(s) collide with scope binding(s): ${toString sdCollisions}"
          else {
            inherit partsScope;
            selfForParts = (builtins.mapAttrs (_: unwrapTop) partsScope)
              // subDirs;
            selfRaw = partsScope // subDirs;
          });

        self = selves.selfRaw;

        partTests = builtins.foldl'
          (acc: n:
            let
              part = importPart n selves.selfForParts;
              t = part.tests or { };
              collisions = lib.intersectLists
                (builtins.attrNames acc)
                (builtins.attrNames t);
            in
            if collisions != [ ]
            then throw "readSrc: ${toString dir}: duplicate test name(s) ${toString collisions}"
            else acc // t
          )
          { }
          partNames;

      in
      import (dir + "/module.nix") (ctx // { inherit self partTests; })
    else
      let
        rawFiles = lib.foldlAttrs
          (acc: name: type:
            if isNixFile name type
            then
              let
                r = import (dir + "/${name}") ctx;
                bare = lib.removeSuffix ".nix" name;
              in
              acc // { ${bare} = r; }
            else acc
          )
          { }
          entries;
      in
      api.mk {
        doc = "";
        description = "";
        value = rawFiles // subDirs;
        tests = { };
      };

  # -- Library fixpoint via lib.fix --
  #
  # Single fixpoint producing both the raw mk-wrapped tree (for test extraction)
  # and the extracted library (for consumers). Each source file is imported
  # exactly once. Source files receive fx = self.lib (the extracted values).
  internals = lib.fix (self:
    let ctx = { inherit lib api; fx = self.lib; };
    in {
      raw = readSrc ./src ctx;
      lib = api.extractValue self.raw;
    }
  );

  # Aliases matching the namespace structure
  src = internals.lib;
  kernel = src.kernel;
  trampoline = src.trampoline;
  adaptMod = src.adapt;
  types = src.types;
  effects = src.effects;
  stream = src.stream;
  pipeline = src.pipeline;
  build = src.build;
  state = src.state;
  experimentalDescInterp = src.experimental.desc-interp;

  # The public library interface
  fx = {
    # Core ADT
    inherit (kernel) pure impure send map seq pipe kleisli;
    inherit (src.comp) isPure isComp match;

    # Bind combinators
    bind = {
      __functor = _: kernel.bind;
      attrs = src.binds.bindAttrs;
      comp = src.binds.bindComp;
      fn = src.binds.bindFn;
    };

    # Queue (advanced — exposed for custom interpreters)
    inherit (kernel) queue;

    # Interpreter (trampoline)
    inherit (trampoline) run handle rotate;

    # Handler composition (adapt)
    inherit (adaptMod) adapt adaptHandlers;

    # Type system
    types = {
      # Foundation
      inherit (types.foundation) mkType check validate make refine defEq;

      # HOAS type constructors (for mkType kernelType parameter)
      hoas = src.tc.hoas;

      # Primitives
      inherit (types.primitives) String Int Bool Float Attrs Path
        Derivation Function Null Unit Any;

      # Constructors
      inherit (types.constructors) Record ListOf Maybe Either Variant;

      # Dependent (Martin-Löf 1984)
      inherit (types.dependent) Pi Sigma Certified Vector DepRecord;

      # Linear (Orchard et al. 2019 — graded modal types)
      inherit (types.linear) Linear Affine Graded;

      # Refinement
      inherit (types.refinement) refined allOf anyOf negate
        positive nonNegative inRange nonEmpty matching
        positiveInt inRangeInt oneOfStr;

      # Universe
      inherit (types.universe) typeAt level lift liftTo Type_0 Type_1 Type_2 Type_3 Type_4;

      # Elaboration bridge (kernel ↔ Nix values)
      inherit (src.tc.elaborate) elaborateType elaborateValue validateValue extract extractInner reifyType verifyAndExtract decide decideType;

      # Generic programming over levitated descriptions and generated datatypes
      generic = src.tc.generic;

      # Verified combinators (natural syntax for writing type-checked implementations)
      verified = src.tc.verified;
    };

    # Effects (reusable operations + handlers)
    effects = {
      inherit (effects.state) get put modify gets;
      state = effects.state;
      error = effects.error;
      typecheck = effects.typecheck;
      policy = effects.typecheck.policy;
      conditions = effects.conditions;
      reader = effects.reader;
      writer = effects.writer;
      acc = effects.acc;
      choice = effects.choice;
      linear = effects.linear;
      scope = effects.scope;
      hasHandler = effects.hasHandler;
    };

    # Streams (effectful lazy sequences)
    stream = {
      inherit (stream.core) done more fromList iterate range replicate;
      inherit (stream.transform) map flatMap filter scanl;
      inherit (stream.limit) take takeWhile drop;
      inherit (stream.reduce) fold toList length sum signal signalOn any all;
      inherit (stream.combine) concat interleave zip zipWith;
    };

    # Pipeline (typed stage composition with reader/error/acc)
    pipeline = {
      inherit (pipeline) mkStage compose run;
      inherit (pipeline) pure bind map;
      inherit (pipeline) ask asks raise raiseWith warn;
    };

    # Build (effects-powered builder types, eval-time pipeline, materialization)
    build = {
      inherit (build.types) BuildStep BuildPlan;
      plan = build.plan;
      materialize = build.materialize;
    };

    # State-shape helpers for handlers. Carriers that survive the trampoline's
    # mandatory `builtins.deepSeq` on threaded state (see src/trampoline.nix:124).
    state = {
      inherit (state.thunk) mkThunk forceThunk isThunk;
    };

    # Sugar (opt-in syntax-livability layer — see src/sugar/)
    sugar = src.sugar;

    # Type-checker prototype namespace. Exposes the full HOAS surface
    # (`fx.tc.hoas`), elaboration bridge (`fx.tc.elaborate` — `extract`,
    # `embedVal`, `verifyAndExtract`, …), eval (`fx.tc.eval`), quote
    # (`fx.tc.quote`), and downstream layers. Opt-in by reference: stable
    # consumers reach for the curated `fx.types.*` re-exports above.
    tc = src.tc;

    # Surface-language extension framework over the HOAS elaborator.
    surface = src.tc.surface;

    # Parallel-namespace prototypes. Opt-in, never aliased over the stable
    # surface; consumers must reach for `fx.experimental.<name>` explicitly.
    experimental = {
      descInterp = experimentalDescInterp // {
        "_opt-in-marker" = true;
      };
    };

    # API utilities
    inherit api;

    # Documentation rendering utilities for API trees produced by extractDocs.
    docs = src.docs;
  };

  integrationTests = import ./tests { inherit lib fx api; };
  benchGateTests = import ./bench/lib/gate-tests.nix { inherit lib; };
  examplesModule = import ./examples { inherit lib fx api; };
  inlineTests = api.extractTests internals.raw;
  examplesDocs = api.extractDocs examplesModule.module;
  examplesValue = api.extractValue examplesModule.module;

  # nix-unit compatible test attrset. nix-unit requires the "test" prefix on
  # test case attrs; non-prefixed attrs are recursed into as namespaces.
  # We use the module/directory structure as namespaces and prefix leaf tests.
  #
  # A genuine nix-unit test leaf has both `expr` AND `expected`; checking
  # only one would misclassify data records (like a Detail default with a
  # bare `expected = null` field) as tests. The `isAttrs` guards let
  # non-attrset leaves (strings, numbers) fall through untouched.
  prefixTests = lib.mapAttrs' (name: value:
    if builtins.isAttrs value && value ? expr && value ? expected then {
      name = if lib.hasPrefix "test" name then name else "test-${name}";
      inherit value;
    } else {
      inherit name;
      value = if builtins.isAttrs value then prefixTests value else value;
    });

  nixUnitTests = {
    # Inline tests: { expr; expected; } pairs, prefixed for nix-unit
    inline = prefixTests inlineTests;
    # Integration tests: module metadata extracted by tests/default.nix
    integration = prefixTests (integrationTests.tree // { examples = examplesModule.tree; });
    # Pure regression-gate fixtures ({ expr; expected; }).
    bench = prefixTests benchGateTests;
  };

  extractDocs = api.extractDocs internals.raw;

  nix-effects-for-docs = fx // { inherit extractDocs src examplesDocs; raw = internals.raw; };

  # Corpus gates shared by mkDocsContent and `tests`.
  docsCorpusChecks = pkgs: corpus: [
    (import ./tests/anchors-schema.nix {
      inherit pkgs lib src corpus;
    })
    (import ./tests/anchors-golden.nix {
      inherit pkgs lib;
      bookSrc = ./book/src;
      goldenFile = ./tests/anchors-golden.txt;
    })
    (import ./tests/routing-coverage.nix {
      inherit pkgs lib corpus;
    })
  ];

  # Rendered once and shared — corpus rendering is expensive.
  docsCorpus = import ./book/gen/docs-content.nix {
    inherit pkgs lib;
    nix-effects = nix-effects-for-docs;
  };

  bench = import ./bench { inherit lib pkgs; };

in
fx // {
  inherit extractDocs bench examplesDocs;
  examples = examplesValue;

  # Content derivation for an external documentation hub.
  # Returns a directory of markdown files with front matter, structured as
  # nix-effects/{section}/{page}.md. No hub-specific assumptions live in
  # the producer beyond the layout contract.
  # Anchor/routing gates are embedded — the result builds only if they pass.
  mkDocsContent = pkgs:
    import ./book/gen/docs-content.nix {
      inherit pkgs lib;
      nix-effects = nix-effects-for-docs;
      requiredChecks = docsCorpusChecks pkgs;
    };

  # Maintenance tool: regenerate the heading-anchor golden file consumed
  # by `tests.anchors-golden`. See the script's header for usage.
  regenerateAnchorsGolden = import ./tests/regenerate-anchors-golden.nix {
    inherit pkgs;
  };

  tests =
    let
      perModule = builtins.mapAttrs (_: api.runTests) inlineTests;
    in
    perModule // {
      integration = integrationTests;
      examples = examplesModule;
      inline = inlineTests;
      # For nix-unit (flake.nix exposes this as the tests output)
      nix-unit = nixUnitTests;
      # Live HTTP probe of every diag Hint docLink (see file header).
      docs-resolves = import ./tests/docs-resolves.nix {
        inherit pkgs lib src;
      };
      # Schema-driven anchor stability: every Hint key has a matching
      # per-key page + in-page heading in the rendered docs corpus
      # (see file header).
      anchors-schema = import ./tests/anchors-schema.nix {
        inherit pkgs lib src;
        corpus = docsCorpus;
      };
      # Golden-file gate for hand-written book chapters: any H2/H3
      # heading rename or addition fails the build until the golden
      # file is regenerated and committed.
      anchors-golden = import ./tests/anchors-golden.nix {
        inherit pkgs lib;
        bookSrc = ./book/src;
        goldenFile = ./tests/anchors-golden.txt;
      };
      # Schema gate: every .md in the produced docs corpus has a
      # path shape the consumer's route table can serve (see file header).
      routing-coverage = import ./tests/routing-coverage.nix {
        inherit pkgs lib;
        corpus = docsCorpus;
      };
    };
} // lib.optionalAttrs exposeInternals {
  # Raw internal-module namespace. Used by benches and tests that isolate the
  # cost or behavior of a specific module. Not part of the stable consumer API.
  inherit src;
}
