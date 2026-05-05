# nix-effects: Algebraic effects, dependent types, and a type-checking kernel in pure Nix
#
# Usage:
#   let fx = import ./. { lib = nixpkgs.lib; };
#   in fx.run (fx.send "get" null) { get = ...; } initialState
{ pkgs ? import ./nixpkgs.nix { }, lib ? pkgs.lib, ... }:

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
  # attrsets. Build `partTests` similarly from parts' `tests`. Pass both
  # to `module.nix`, which returns an `api.mk`-wrapped module. The walker
  # does not post-process `module.nix`'s result.
  #
  # Each part receives `{ self, fx, api, lib, ... }:` and returns
  # `{ scope; tests ? {} }`. `module.nix` receives `{ self, partTests,
  # fx, api, lib, ... }:` and returns `api.mk { doc; value; tests }`.
  # Cross-part references go through `self.<binding>`.
  #
  # Collisions (duplicate scope keys, duplicate test names) are hard
  # errors — never silent merges. There is no priority system, no
  # `mkDefault`/`mkForce`, no `options`. Each binding has exactly one
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
        in
          import (dir + "/module.nix") (ctx // { inherit self partTests; })
      else
        let
          files = lib.foldlAttrs (acc: name: type:
            if isNixFile name type
            then acc // { ${lib.removeSuffix ".nix" name} = import (dir + "/${name}") ctx; }
            else acc
          ) {} entries;
        in api.mk {
          doc = "";
          value = files // subDirs;
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
      inherit (types.foundation) mkType check validate make refine;

      # HOAS type constructors (for mkType kernelType parameter)
      hoas = src.tc.hoas;

      # Primitives
      inherit (types.primitives) String Int Bool Float Attrs Path Function Null Unit Any;

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

      # Verified combinators (natural syntax for writing type-checked implementations)
      verified = src.tc.verified;
    };

    # Effects (reusable operations + handlers)
    effects = {
      inherit (effects.state) get put modify gets;
      state = effects.state;
      error = effects.error;
      typecheck = effects.typecheck;
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

    # Sugar (opt-in syntax-livability layer — see src/sugar/)
    sugar = src.sugar;

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

  # Normalize integration tests: some are booleans, some are { expr; expected; }.
  # Wrap booleans as { expr; expected = true; }, pass through existing pairs.
  normalizeTest = value:
    if builtins.isAttrs value && value ? expr && value ? expected
    then value
    else { expr = value; expected = true; };
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

  # Raw internal-module namespace. Used by bench workloads and tests that
  # isolate the cost of a specific module (e.g. `src.diag.pretty`,
  # `src.tc.check.bindP`). Not part of the stable consumer API — modules under
  # `src` may be reshaped without notice. Consumer code should use the flat
  # `fx.<...>` exports declared above.
  inherit src;

  # Content derivation for docs.kleisli.io.
  # Returns a directory of markdown files with front matter, structured as
  # nix-effects/{section}/{page}.md for the kleisli-docs multi-project hub.
  mkKleisliDocsContent = pkgs: import ./book/gen/kleisli-docs.nix {
    inherit pkgs lib;
    nix-effects = fx // { inherit extractDocs src; };
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
    };
}
