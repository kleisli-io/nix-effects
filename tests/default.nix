# nix-effects test suite
#
# Integration tests validating effects + types + streams working together.
{ lib, fx }:

let
  trampolineTests = import ./trampoline-test.nix { inherit lib fx; };
  typesTests = import ./types-test.nix { inherit lib fx; };
  effectsTests = import ./effects-test.nix { inherit lib fx; };
  lawTests = import ./law-test.nix { inherit lib fx; };
  errorPathTests = import ./error-path-test.nix { inherit lib fx; };
  newEffectsTests = import ./new-effects-test.nix { inherit lib fx; };
  streamTests = import ./stream-test.nix { inherit lib fx; };
  linearTests = import ./linear-test.nix { inherit lib fx; };
  proofBasicsTests = import ../examples/proof-basics.nix { inherit lib fx; };
  equalityProofTests = import ../examples/equality-proofs.nix { inherit lib fx; };
  verifiedFunctionTests = import ../examples/verified-functions.nix { inherit lib fx; };
  docsTests = import ./docs-test.nix { inherit lib fx; };
  pipelineTests = import ./pipeline-test.nix { inherit lib fx; };

in {
  inherit (trampolineTests) pureComputation singleEffect simpleCounter
          tenThousandOps hundredThousandOps
          multipleEffects returnValueFlow
          statefulAccumulation earlyPure pureBindChain
          handleWithReturn adaptState adaptHandlersTest
          leftNestedBind
          qAppPureChain viewlGoLeftNested;

  inherit (typesTests) validPortTest vectorTest universeTest
          recordRefinementTest maybeTest depRecordTest
          makeThrowsTest variantTest predicateTest universeSafetyTest
          piCheckAtIsEffectful
          strictHandlerPassesTest collectingHandlerTest loggingHandlerTest
          sameCompDifferentHandlerTest
          sigmaValidateIsEffectful sigmaStrictHandlerTest
          certifiedCertifyETest certifiedCertifyECollectingTest certifiedCertifyEFailTest
          vectorIsEffectful vectorCheckAtStrictTest
          depRecordIsEffectful depRecordValidateStrictTest
          foundationValidateIsEffectful
          piValidateIsGuard piAdequacy sigmaAdequacy piCheckAtDiffersFromValidate
          certifiedAdequacy depRecordAdequacy primitiveAdequacy vectorAdequacy
          sigmaValidateEmpty sigmaValidateMissingSnd sigmaValidateMissingFst
          sigmaValidateWrongSnd
          piCheckAtDomainFailure
          certifyECrashingPredicate certifyEWrongBase
          depRecordValidateNonAttrset depRecordValidateMissingField depRecordValidateWrongTypes
          pairEThroughHandlers composeCheckAt
          sigmaHandlerDiversity
          sigmaShortCircuitGuardsCrash sigmaAdequacyWrongFst piCheckAtShortCircuit
          universeTrustBoundary
          listOfValidateIsEffectful listOfCollectingPerElement
          listOfEmptyValidatePure listOfNonListTotality listOfAdequacy
          sigmaDeepCollecting depRecordDeepBlame sigmaDeepAdequacy
          sigmaDeepShortCircuit pairEDeepBlame certifyEDeepBlame
          crossTypeAdequacy;

  inherit (effectsTests) stateCounterTest stateModifyTest stateGetsTest stateFinalStateTest
          errorCollectingTest errorContextTest
          typecheckStrictPassesTest typecheckCollectingErrorsTest
          typecheckLoggingAllChecksTest typecheckLoggingAllPassTest
          conditionsSignalRestartTest conditionsCollectTest conditionsIgnoreTest
          composedWithAdaptTest;

  inherit (lawTests) monadLeftIdPure monadLeftIdEffectful
          monadRightIdPure monadRightIdEffectful
          monadAssocPure monadAssocEffectful
          functorIdentity functorComposition
          stateGetGet stateGetPut statePutGet statePutPut
          lensGetPut lensPutGet lensPutPut
          sigmaCurryUncurry sigmaUncurryCurry
          sigmaPullbackIdentity sigmaPullbackComposition
          depRecordPackUnpack depRecordUnpackPack;

  inherit (errorPathTests) unhandledEffectRunThrows unhandledEffectHandleThrows
          partialHandlerThrows unhandledEffectNames
          badProtocolValueThrows badProtocolEmptyThrows
          badProtocolStateOnlyThrows allBadProtocolsThrow
          errorStrictThrowsParametric errorStrictWithContextThrows
          errorStrictMidChainThrows
          conditionsFailThrowsParametric
          errorResultAbortsTest errorResultWithContextTest
          errorResultParametric errorResultPurePassesTest errorResultPureParametric
          errorResultDiscardsContTest
          abortAtStartTest abortMidChainTest
          bothResumeAndAbortTakesAbort
          abortAtPositionN abortValueTypes
          seqEffectsTest seqEmptyTest seqReturnsLastTest seqParametricLengths
          handlerMergeRightBiasTest
          runNullThrows runIntThrows runStringThrows runAttrsetNoTagThrows
          handleNullThrows handleIntThrows
          effectNameCollision effectCollisionSilent;

  inherit (newEffectsTests) readerAskTest readerAsksTest readerLocalTest readerChainTest
          readerAsksParametric
          writerTellTest writerTellAllTest writerEmptyTest writerParametric
          accEmitTest accEmitAllTest accEmptyCollectTest accParametric
          chooseFirstTest choiceFailTest
          choiceGuardTrueTest choiceGuardFalseTest choicePendingTest
          readerWriterComposedTest;

  inherit (streamTests) fromListToListTest fromListEmptyTest
          rangeTest rangeEmptyTest replicateTest replicateZeroTest
          fromListParametric rangeParametric
          mapTest filterTest filterAllTest filterNoneTest
          mapPreservesLength mapIdentity mapComposition
          pipelineTest
          takeTest takeMoreThanAvailable takeZeroTest
          takeWhileTest takeFromInfinite
          dropTest dropAllTest
          foldTest sumTest lengthTest
          anyTrueTest anyFalseTest allTrueTest allFalseTest
          sumRangeParametric
          concatTest concatEmptyLeftTest
          interleaveTest interleaveUnevenTest
          zipTest zipUnevenTest zipWithTest;

  inherit (linearTests) linearHappyPath linearMultiResource linearAffineRelease
          linearGradedExact linearUnlimited
          linearLeakDetected linearDoubleConsumeAborts
          linearConsumeAfterReleaseAborts linearDoubleReleaseAborts
          linearMultiLeakReportsAll
          linearGradedUnderuseDetected linearGradedOveruseAborts
          compositionThreeEffects compositionTypeErrorPlusLeak
          compositionStatePreservation compositionAbortPreservesState
          stressDeepSeq100Pairs stressComposed50Cycles
          typeLinearCheckValid typeLinearCheckInvalid typeLinearCheckNonToken
          typeGradedName typeLinearRoundTrip
          mixedGradedResources;

  inherit (proofBasicsTests) addZeroZero addThreeFive addTenSeven
          doubleNegTrue doubleNegFalse lengthThree appendTwoOne
          witnessZero witnessAddResult witnessDoubleNeg
          natElimDouble natElimMul
          boolElimTrue boolElimFalse
          listSum listMapSucc
          sumElimLeft sumElimRight
          polyId exFalso;

  inherit (equalityProofTests) congType congConcrete
          symType symConcrete
          transType transConcrete
          transportType transportConcrete
          combinedProof;

  inherit (verifiedFunctionTests) succApply5 succApply0
          notTrue notFalse
          add2and3 add0and7 add4and0
          isZeroOf0 isZeroOf5
          predOf0 predOf1 predOf5
          mapSuccCorrect mapEmptyCorrect
          filterZerosCorrect
          foldSumCorrect
          composedCorrect
          sumLeftCorrect sumRightCorrect
          letCorrect
          pairFstCorrect pairSndCorrect
          recordGetXCorrect recordGetYCorrect recordSuccXCorrect
          strEqSame strEqDiff strEqEmpty
          strElemFound strElemMissing strElemEmptyList
          recordStrEqMatch recordStrEqNoMatch;

  inherit (docsTests) portExample depContractExample stateEffectExample apiSurfaceSanity;

  inherit (pipelineTests) fullPipelineTest pureOnlyTest;

  allPass = trampolineTests.allPass && typesTests.allPass && effectsTests.allPass
            && lawTests.allPass && errorPathTests.allPass
            && newEffectsTests.allPass && streamTests.allPass
            && linearTests.allPass
            && proofBasicsTests.allPass
            && equalityProofTests.allPass
            && verifiedFunctionTests.allPass
            && docsTests.allPass
            && pipelineTests.allPass;
}
