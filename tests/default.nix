# nix-effects test suite
#
# Integration tests validating effects + types + streams working together.
{ lib, fx, api }:

let
  trampolineTests = import ./trampoline-test.nix { inherit lib fx; };
  typesTests = import ./types-test.nix { inherit lib fx; };
  effectsTests = import ./effects-test.nix { inherit lib fx; };
  lawTests = import ./law-test.nix { inherit lib fx; };
  errorPathTests = import ./error-path-test.nix { inherit lib fx; };
  newEffectsTests = import ./new-effects-test.nix { inherit lib fx; };
  streamTests = import ./stream-test.nix { inherit lib fx; };
  linearTests = import ./linear-test.nix { inherit lib fx; };
  exampleDocsForDocsTests = api.extractDocs
    (import ../examples { inherit lib fx api; }).module;
  docsTests = import ./docs-test.nix {
    inherit lib fx;
    examplesDocs = exampleDocsForDocsTests;
  };
  pipelineTests = import ./pipeline-test.nix { inherit lib fx; };
  scopeTests = import ./scope-test.nix { inherit lib fx; };
  sugarEffectsTests = import ./sugar-effects-test.nix { inherit lib fx; };
  sugarTypesTests = import ./sugar-types-test.nix { inherit lib fx; };
  sugarCompatTests = import ./sugar-compat-test.nix { inherit lib fx; };
  thunkTests = import ./thunk-test.nix { inherit lib fx; };
  layerLeakRegression = import ./regression-layer-leak.nix { inherit lib fx; };
  descInterpParityTests = import ./experimental/desc-interp-parity { inherit lib fx; };
  descInterpLawsTests = import ./experimental/desc-interp-laws { inherit lib fx; };

  testNamespace = args: api.namespace (args // { docHidden = true; });

  suiteTests = suite: suite;

  mkMixedSuite = boolNames: suite:
    let
      boolSet = lib.genAttrs boolNames (_: true);
    in
    testNamespace {
      value = { };
      tests = builtins.mapAttrs
        (name: value:
          if builtins.hasAttr name boolSet then
            { expr = value; expected = true; }
          else
            value)
        (suiteTests suite);
    };

  mkBoolSuite = suite: mkMixedSuite (builtins.attrNames (suiteTests suite)) suite;

  mkDescriptorSuite = mkMixedSuite [ ];

  mkAllDescriptorSuite = suite:
    testNamespace {
      value = { };
      tests = suiteTests suite;
    };

  errorPathBoolTests = [
    "unhandledEffectRunThrows"
    "unhandledEffectHandleThrows"
    "partialHandlerThrows"
    "unhandledEffectNames"
    "badProtocolValueThrows"
    "badProtocolEmptyThrows"
    "badProtocolStateOnlyThrows"
    "allBadProtocolsThrow"
    "errorStrictThrowsParametric"
    "errorStrictWithContextThrows"
    "errorStrictMidChainThrows"
    "conditionsFailThrowsParametric"
    "errorResultParametric"
    "errorResultPureParametric"
    "abortAtPositionN"
    "abortValueTypes"
    "seqParametricLengths"
    "runNullThrows"
    "runIntThrows"
    "runStringThrows"
    "runAttrsetNoTagThrows"
    "handleNullThrows"
    "handleIntThrows"
    "effectCollisionSilent"
  ];

  newEffectsBoolTests = [
    "readerAsksParametric"
    "writerParametric"
    "accParametric"
  ];

  streamBoolTests = [
    "fromListParametric"
    "rangeParametric"
    "mapPreservesLength"
    "mapIdentity"
    "mapComposition"
    "takeParametric"
    "sumRangeParametric"
  ];

  rootModule = testNamespace {
    description = "Integration tests";
    value = {
      trampoline = mkBoolSuite trampolineTests;
      types = mkBoolSuite typesTests;
      effects = mkDescriptorSuite effectsTests;
      laws = mkBoolSuite lawTests;
      errorPath = mkMixedSuite errorPathBoolTests errorPathTests;
      newEffects = mkMixedSuite newEffectsBoolTests newEffectsTests;
      stream = mkMixedSuite streamBoolTests streamTests;
      linear = mkDescriptorSuite linearTests;
      docs = mkBoolSuite docsTests;
      pipeline = mkDescriptorSuite pipelineTests;
      scope = mkDescriptorSuite scopeTests;
      thunk = mkBoolSuite thunkTests;
      layerLeak = mkBoolSuite layerLeakRegression;

      sugar = testNamespace {
        value = {
          effects = mkDescriptorSuite sugarEffectsTests;
          types = mkDescriptorSuite sugarTypesTests;
          compat = mkDescriptorSuite sugarCompatTests;
        };
        tests = { };
      };

      experimental = testNamespace {
        value = {
          descInterp = testNamespace {
            value = {
              parity = testNamespace {
                value = {
                  state = mkAllDescriptorSuite descInterpParityTests.effects.state;
                  error = mkAllDescriptorSuite descInterpParityTests.effects.error;
                  composed = mkAllDescriptorSuite descInterpParityTests.effects.composed;
                };
                tests = { };
              };
              laws = testNamespace {
                value = {
                  state = mkAllDescriptorSuite descInterpLawsTests.state;
                  error = mkAllDescriptorSuite descInterpLawsTests.error;
                  bindAssoc = mkAllDescriptorSuite descInterpLawsTests.bindAssoc;
                  composed = mkAllDescriptorSuite descInterpLawsTests.composed;
                };
                tests = { };
              };
            };
            tests = { };
          };
        };
        tests = { };
      };
    };
    tests = { };
  };

  tree = api.extractTests rootModule;
  results = api.runTests tree;

in
{
  module = rootModule;
  inherit tree results;
}
