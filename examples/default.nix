{ fx, lib ? null, api ? fx.api, ... }:

let
  proofBasics = import ./proof-basics.nix { inherit fx; };
  equalityProofs = import ./equality-proofs.nix { inherit fx; };
  verifiedFunctions = import ./verified-functions.nix { inherit fx; };
  handlerSwapValidation = import ./handler-swap-validation.nix { inherit fx; };
  stlc = import ./stlc { inherit fx lib api; };

  concatMap = f: xs: builtins.concatLists (map f xs);

  testNamesFor = suite:
    concatMap (section: section.tests or [ ])
      (suite.__example.sections or [ ]);

  boolTests = names: suite:
    builtins.listToAttrs (map
      (name: {
        inherit name;
        value = { expr = suite.${name}; expected = true; };
      })
      names);

  mkExample = suite:
    api.namespace {
      title = suite.__example.title or "";
      description = suite.__example.description or "";
      doc = suite.__example.introduction or "";
      sections = suite.__example.sections or [ ];
      value = { };
      tests = boolTests (testNamesFor suite) suite;
    };

  module = api.namespace {
    title = "Examples";
    description = "Worked examples for proofs, effect-handler policy, and small surface languages over HOAS.";
    doc = ''
      The examples show nix-effects in complete, small programs. They move
      from proof construction, to effect-handler policy, to surface languages
      built over the HOAS kernel.

      The same examples live in the source tree under `examples/` if you want
      to run or adapt them locally.
    '';
    sections = [
      {
        title = "Where to start";
        prose = ''
          Start with proof examples when you want to see values checked by the
          kernel. Use the effect example to compare validation policies without
          changing the computation. Use the surface-language examples when you
          want to build a small syntax layer over HOAS.
        '';
        code = ''
          examples/
            proof-basics.nix
            equality-proofs.nix
            verified-functions.nix
            handler-swap-validation.nix
            stlc/
        '';
        tests = [ ];
      }
    ];
    value = {
      proofBasics = mkExample proofBasics;
      equalityProofs = mkExample equalityProofs;
      verifiedFunctions = mkExample verifiedFunctions;
      handlerSwapValidation = mkExample handlerSwapValidation;
      stlc = stlc.module;
    };
    tests = { };
  };

  tree = api.extractTests module;
  results = api.runTests tree;

in
{
  inherit module tree results;
  inherit proofBasics equalityProofs verifiedFunctions handlerSwapValidation stlc;
}
