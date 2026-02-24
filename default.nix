# nix-effects: Algebraic effects, dependent types, and a type-checking kernel in pure Nix
#
# Usage:
#   let fx = import ./. { lib = nixpkgs.lib; };
#   in fx.run (fx.send "get" null) { get = ...; } initialState
{ lib, ... }:

let
  api = import ./src/api.nix { inherit lib; };

  # -- readSrc: lightweight directory walker  --
  #
  # Walk a directory, importing .nix files and recursing into subdirectories.
  # Returns a tree of raw mk-wrapped results matching the namespace structure:
  #   { kernel = <mk>; types = { foundation = <mk>; ... }; ... }
  readSrc = dir: ctx:
    let
      entries = builtins.readDir dir;
      excluded = [ "api.nix" "module.nix" ];
      isNixFile = name: type:
        type == "regular"
        && lib.hasSuffix ".nix" name
        && !(builtins.elem name excluded);
      files = lib.foldlAttrs (acc: name: type:
        if isNixFile name type
        then acc // { ${lib.removeSuffix ".nix" name} = import (dir + "/${name}") ctx; }
        else acc
      ) {} entries;
      dirs = lib.foldlAttrs (acc: name: type:
        if type == "directory"
        then acc // { ${name} = readSrc (dir + "/${name}") ctx; }
        else acc
      ) {} entries;
    in files // dirs;

  # -- collectTests: inline test extraction from raw tree --
  #
  # Walk the raw mk-wrapped tree, applying api.extractTests to file results
  # and recursing into directory attrsets. Produces flat test attrset with
  # dotted prefixes: { "kernel.pure-bind-applies-f" = { expr; expected; }; ... }
  collectTests = prefix: tree:
    lib.foldlAttrs (acc: name: node:
      let p = if prefix == "" then name else "${prefix}.${name}"; in
      if node ? _type && node._type == "nix-effects-api"
      then acc // api.extractTests p node
      else if builtins.isAttrs node && !(node ? _tag)
      then acc // collectTests p node
      else acc
    ) {} tree;

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

  # The public library interface
  fx = {
    # Core ADT (kernel)
    inherit (kernel) pure impure send bind map seq;

    # Queue (advanced — exposed for custom interpreters)
    inherit (kernel) queue;

    # Interpreter (trampoline)
    inherit (trampoline) run handle;

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
      inherit (src.tc.elaborate) elaborateType elaborateValue extract extractInner reifyType verifyAndExtract decide decideType;

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
    };

    # Streams (effectful lazy sequences)
    stream = {
      inherit (stream.core) done more fromList iterate range replicate;
      inherit (stream.transform) map filter scanl;
      inherit (stream.limit) take takeWhile drop;
      inherit (stream.reduce) fold toList length sum any all;
      inherit (stream.combine) concat interleave zip zipWith;
    };

    # API utilities
    inherit api;
  };

  integrationTests = import ./tests { inherit lib fx; };
  inlineTests = collectTests "" internals.raw;

  # nix-unit compatible test attrset. nix-unit requires the "test" prefix on
  # test case attrs; non-prefixed attrs are recursed into as namespaces.
  # We use the module/directory structure as namespaces and prefix leaf tests.
  prefixTests = lib.mapAttrs' (name: value: {
    name = "test ${name}";
    inherit value;
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

in fx // {
  inherit extractDocs;

  # Content derivation for docs.kleisli.io.
  # Returns a directory of markdown files with front matter, structured as
  # nix-effects/{section}/{page}.md for the kleisli-docs multi-project hub.
  mkKleisliDocsContent = pkgs: import ./book/gen/kleisli-docs.nix {
    inherit pkgs lib;
    nix-effects = fx // { inherit extractDocs; };
  };

  tests = {
    integration = integrationTests;
    inline = inlineTests;
    allPass = integrationTests.allPass
              && (api.runTests inlineTests).allPass;
    # For nix-unit (flake.nix exposes this as the tests output)
    nix-unit = nixUnitTests;
  };
}
