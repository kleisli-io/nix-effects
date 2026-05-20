# nix-effects: effects, typed boundaries, and description-backed DSLs in pure Nix
#
# Usage:
#   let fx = import ./. { lib = nixpkgs.lib; };
#   in fx.run (fx.send "get" null) { get = ...; } initialState
{ pkgs ? import ./nixpkgs.nix { }, lib ? pkgs.lib, exposeInternals ? false, ... }:

let
  api = import ./src/api.nix { inherit lib; };

  # -- readSrc: directory walker --
  #
  # For a directory without `module.nix`: auto-import `.nix` files as
  # namespace entries, recurse into subdirectories as nested namespaces.
  # Each leaf receives `{ fx, api, lib, ... }:` and returns `api.mk { doc;
  # value; tests }`.
  #
  # For a directory with `module.nix`: treat as a split module. Build
  # `self` as the disjoint-union fixpoint of sibling parts' `scope`
  # attrsets. Build `partTests` similarly from parts' `tests`, and
  # `partDocs` similarly from parts' `__docs`. Pass all three to
  # `module.nix`, which is expected to call `api.mkModule` to produce
  # the final `api.mk`-wrapped result. The walker does not
  # post-process `module.nix`'s return — the invariant
  # (`flat-leaf-key-set of value == attrNames partDocs`) and the
  # `__docs` injection are performed inside `api.mkModule`.
  #
  # Each part receives `{ self, fx, api, lib, ... }:` and returns
  # `{ scope; tests ? {}; __docs ? {} }`. Cross-part references go through
  # `self.<binding>`.
  #
  # `__docs` is name-keyed per-binding metadata at the same key-level as
  # `scope` (never inside `scope`); each entry is the standalone-file
  # `__docs.<name>` shape `{ description? signature? doc? tests? }`. The
  # name matches the value-tree convention: in a standalone file `__docs`
  # is a sibling of the bindings; in a split-module part `__docs` is a
  # sibling of `scope` (which holds the bindings).
  #
  # Standalone files may use the `__docs._self` convention instead of a
  # file-level `api.mk` wrap. `__docs._self` carries the file's
  # module-level metadata (description, doc, signature, tests). readSrc
  # routes it to the parent dir's `__docs.<filename>` slot — the slot
  # that holds the file's identity in the parent namespace's docs tree.
  #
  # Two shapes use the convention:
  #
  #   - Single-binding file whose one binding matches the filename:
  #       { <name> = <bare>; __docs._self = { ... }; }
  #     readSrc hoists `<name>` as the file's namespace identity, so
  #     `fx.<dir>.<name>` is the bare value (function, attrset, etc.) —
  #     no wrap. `__docs._self` becomes `parent.__docs.<name>`.
  #
  #   - Multi-binding file (or single-binding with non-matching name):
  #       { <b1> = ...; <b2> = ...; ...; __docs = { _self = { ... };
  #         <b1> = { ... }; ...; }; }
  #     readSrc treats the file as a sub-namespace under `<filename>`;
  #     `_self` is hoisted to `parent.__docs.<filename>` (module-level
  #     metadata), per-binding `__docs.<n>` entries stay inside the
  #     file as the namespace's own docs sibling.
  #
  # Shape guard (strict): every `__docs.<n>` entry other than `_self`
  # must correspond to a top-level binding in the file — no orphan docs.
  # Top-level bindings without docs are allowed (lenient at the
  # standalone-file level; the strict bijection invariant applies only
  # to split-module groups via `api.mkModule`).
  #
  # Files without `__docs._self` keep using a file-level `api.mk` wrap;
  # the two conventions co-exist file-by-file during migration.
  #
  # Collisions (duplicate scope keys, duplicate test names, duplicate
  # doc names) are hard errors — never silent merges. There is no
  # priority system, no `mkDefault`/`mkForce`, no `options`. Each
  # binding has exactly one definition site and exactly one
  # documentation site (always the same part).
  readSrc = dir: ctx:
    let
      entries = builtins.readDir dir;
      excluded = [ "api.nix" "module.nix" ];
      isNixFile = name: type:
        type == "regular"
        && lib.hasSuffix ".nix" name
        && !(builtins.elem name excluded);
      isSplitModule = entries ? "module.nix";

      # Subdirectories are nested namespaces in both split-module and
      # plain-namespace modes. Recursing once here keeps the treatment
      # uniform: a subdir's readSrc result is always an api.mk-wrapped
      # node (split dirs via their module.nix; plain dirs via the wrap
      # below), so parent-level traversals see only mk-wrapped children.
      subDirs = lib.foldlAttrs (acc: name: type:
        if type == "directory"
        then acc // { ${name} = readSrc (dir + "/${name}") ctx; }
        else acc
      ) {} entries;
    in
      if isSplitModule then
        let
          partNames = builtins.attrNames (lib.filterAttrs isNixFile entries);
          importPart = n: s: import (dir + "/${n}") (ctx // { self = s; });

          # Sibling parts contribute flat bindings; subdirectories enter
          # self under their directory name. Collisions between the two
          # (a scope binding colliding with a subdir name) are a hard
          # error — each binding has exactly one definition site.
          self = lib.fix (s:
            let
              partsScope = builtins.foldl' (acc: n:
                let
                  part = importPart n s;
                  scope = part.scope;
                  collisions = lib.intersectLists
                                 (builtins.attrNames acc)
                                 (builtins.attrNames scope);
                in
                  if collisions != []
                  then throw "readSrc: ${toString dir}: duplicate binding(s) ${toString collisions}"
                  else acc // scope
              ) {} partNames;
              sdCollisions = lib.intersectLists
                               (builtins.attrNames partsScope)
                               (builtins.attrNames subDirs);
            in
              if sdCollisions != []
              then throw "readSrc: ${toString dir}: subdirectory name(s) collide with scope binding(s): ${toString sdCollisions}"
              else partsScope // subDirs);

          partTests = builtins.foldl' (acc: n:
            let
              part = importPart n self;
              t = part.tests or {};
              collisions = lib.intersectLists
                             (builtins.attrNames acc)
                             (builtins.attrNames t);
            in
              if collisions != []
              then throw "readSrc: ${toString dir}: duplicate test name(s) ${toString collisions}"
              else acc // t
          ) {} partNames;

          partDocs = builtins.foldl' (acc: n:
            let
              part = importPart n self;
              d = part.__docs or {};
              collisions = lib.intersectLists
                             (builtins.attrNames acc)
                             (builtins.attrNames d);
            in
              if collisions != []
              then throw "readSrc: ${toString dir}: duplicate doc name(s) ${toString collisions}"
              else acc // d
          ) {} partNames;

        in
          import (dir + "/module.nix") (ctx // { inherit self partTests partDocs; })
      else
        let
          rawFiles = lib.foldlAttrs (acc: name: type:
            if isNixFile name type
            then acc // { ${lib.removeSuffix ".nix" name} = import (dir + "/${name}") ctx; }
            else acc
          ) {} entries;

          # `__docs._self` convention. Predicate: file return is a
          # plain (non-mk) attrset whose `__docs` carries a `_self` entry.
          hasSelfDocs = r:
            builtins.isAttrs r
            && (r._type or null) != "nix-effects-api"
            && r ? __docs
            && builtins.isAttrs r.__docs
            && r.__docs ? _self;

          # Shape guard: every `__docs.<n>` entry other than `_self`
          # must correspond to a top-level binding in the file.
          # Top-level bindings without docs are allowed.
          checkSelfDocsShape = name: r:
            let
              bindings = lib.subtractLists [ "__docs" ] (builtins.attrNames r);
              allowed  = [ "_self" ] ++ bindings;
              docKs    = builtins.attrNames r.__docs;
              docExtra = lib.subtractLists allowed docKs;
            in
              if docExtra != []
              then throw "readSrc: ${toString dir}/${name}.nix: __docs entries with no matching binding: ${toString docExtra}"
              else true;

          # Hoist iff the file has exactly one binding whose name
          # matches the filename. Otherwise the file is a sub-namespace.
          shouldHoist = name: r:
            let bindings = lib.subtractLists [ "__docs" ] (builtins.attrNames r);
            in bindings == [ name ];

          # Per-file processing:
          #  - Hoist single-binding-matching-filename to the parent slot.
          #  - For sub-namespace files, strip `_self` from the file's
          #    `__docs` (it's now routed to the parent's `__docs.<file>`)
          #    and pass the rest through. If `__docs` becomes empty after
          #    `_self` removal, drop it entirely.
          #  - Files without `__docs._self` pass through unchanged.
          files = lib.mapAttrs (name: r:
            if hasSelfDocs r
            then
              assert checkSelfDocsShape name r;
              if shouldHoist name r
              then r.${name}
              else
                let
                  restDocs = removeAttrs r.__docs [ "_self" ];
                  rest     = removeAttrs r [ "__docs" ];
                in
                  rest //
                  (lib.optionalAttrs (restDocs != {}) { __docs = restDocs; })
            else r
          ) rawFiles;

          # Aggregate `__docs._self` entries into a single `__docs`
          # sibling for the parent dir's plain-namespace wrap.
          selfDocs = lib.foldlAttrs (acc: name: r:
            if hasSelfDocs r
            then acc // { ${name} = r.__docs._self; }
            else acc
          ) {} rawFiles;

          docsConflict = (selfDocs != {})
                         && ((files ? __docs) || (subDirs ? __docs));
        in
          if docsConflict
          then throw "readSrc: ${toString dir}: __docs._self aggregation collides with existing `__docs` key in namespace (file named __docs.nix or subdir __docs/)"
          else api.mk {
            doc = "";
            value = files // subDirs
                    // (lib.optionalAttrs (selfDocs != {})
                          { __docs = selfDocs; });
            tests = {};
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
              positive nonNegative inRange nonEmpty matching;

      # Universe
      inherit (types.universe) typeAt level Type_0 Type_1 Type_2 Type_3 Type_4;

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

    # Parallel-namespace prototypes. Opt-in, never aliased over the stable
    # surface; consumers must reach for `fx.experimental.<name>` explicitly.
    experimental = {
      descInterp = experimentalDescInterp // {
        "_opt-in-marker" = true;
      };
    };

    # API utilities
    inherit api;
  };

  integrationTests = import ./tests { inherit lib fx; };
  inlineTests = api.extractTests internals.raw;

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

  # Normalize integration tests without forcing boolean leaves while building
  # the nix-unit namespace. Mixed boolean/{ expr; expected; } tests cannot be
  # shape-checked eagerly without evaluating the boolean tests.
  normalizeTest = value:
    {
      expr =
        if builtins.isAttrs value && value ? expr && value ? expected
        then value.expr == value.expected
        else value;
      expected = true;
    };
  nixUnitTests = {
    # Inline tests: { expr; expected; } pairs, prefixed for nix-unit
    inline = prefixTests inlineTests;
    # Integration tests: normalized and prefixed
    integration = prefixTests (builtins.mapAttrs
      (_: normalizeTest)
      (removeAttrs integrationTests [ "allPass" ])
    );
  };

  extractDocs = api.extractDocs internals.raw;

  bench = import ./bench { inherit lib pkgs; };

in fx // {
  inherit extractDocs bench;

  # Content derivation for docs.kleisli.io.
  # Returns a directory of markdown files with front matter, structured as
  # nix-effects/{section}/{page}.md for the kleisli-docs multi-project hub.
  mkKleisliDocsContent = pkgs: import ./book/gen/kleisli-docs.nix {
    inherit pkgs lib;
    nix-effects = fx // { inherit extractDocs src; };
  };

  # Maintenance tool: regenerate the heading-anchor golden file consumed
  # by `tests.anchors-golden`. See the script's header for usage.
  regenerateAnchorsGolden = import ./tests/regenerate-anchors-golden.nix {
    inherit pkgs;
  };

  tests =
    let
      perModule = builtins.mapAttrs (_: api.runTests) inlineTests;
      # Collect all failed tests across modules
      inlineFailed = lib.foldlAttrs (acc: modName: modResult:
        acc // (lib.mapAttrs' (testName: test: {
          name = "${modName}.${testName}";
          value = test;
        }) modResult.failed)
      ) {} perModule;
    in perModule // {
      integration = integrationTests;
      inline = inlineTests;
      allPass = integrationTests.allPass
                && lib.all (m: m.allPass) (builtins.attrValues perModule);
      failed = inlineFailed;
      # For nix-unit (flake.nix exposes this as the tests output)
      nix-unit = nixUnitTests;
      # Live HTTP probe of every diag Hint docLink (see file header).
      docs-resolves = import ./tests/docs-resolves.nix {
        inherit pkgs lib src;
      };
      # Schema-driven anchor stability: every Hint key has a matching
      # per-key page + in-page heading in the rendered kleisli-docs
      # derivation (see file header).
      anchors-schema = import ./tests/anchors-schema.nix {
        inherit pkgs lib src;
        kleisliDocs = import ./book/gen/kleisli-docs.nix {
          inherit pkgs lib;
          nix-effects = fx // { inherit extractDocs src; };
        };
      };
      # Golden-file gate for hand-written book chapters: any H2/H3
      # heading rename or addition fails the build until the golden
      # file is regenerated and committed.
      anchors-golden = import ./tests/anchors-golden.nix {
        inherit pkgs lib;
        bookSrc = ./book/src;
        goldenFile = ./tests/anchors-golden.txt;
      };
    };
} // lib.optionalAttrs exposeInternals {
  # Raw internal-module namespace. Used by benches and tests that isolate the
  # cost or behavior of a specific module. Not part of the stable consumer API.
  inherit src;
}
