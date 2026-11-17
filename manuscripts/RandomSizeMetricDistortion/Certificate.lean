import Voting.Distortion.Certificate
import RandomSizeMetricDistortion.Numerics.StarLaw
import RandomSizeMetricDistortion.Numerics.WitnessData
import RandomSizeMetricDistortion.Numerics.TableCoverage
import RandomSizeMetricDistortion.Numerics.RationalBernstein
import RandomSizeMetricDistortion.Numerics.CorrectionSigns
import RandomSizeMetricDistortion.Numerics.ShiftedCoefficients
import RandomSizeMetricDistortion.Numerics.MeasureSigns
import RandomSizeMetricDistortion.Numerics.MeasureMass
import RandomSizeMetricDistortion.Numerics.PolynomialExpressions
import RandomSizeMetricDistortion.Numerics.RationalIntervals
import RandomSizeMetricDistortion.Numerics.DerivativeBounds
import RandomSizeMetricDistortion.Numerics.CenteredBounds
import RandomSizeMetricDistortion.Numerics.MonotoneFaces
import RandomSizeMetricDistortion.Numerics.TreeSoundness
import RandomSizeMetricDistortion.Numerics.MeasureIntervals
import RandomSizeMetricDistortion.Numerics.RankMeasurePrimitive
import RandomSizeMetricDistortion.Numerics.DomainTemplates
import RandomSizeMetricDistortion.Numerics.TapeReplay
import RandomSizeMetricDistortion.Numerics.EndpointBounds
import RandomSizeMetricDistortion.Numerics.MixedDifference
import RandomSizeMetricDistortion.Numerics.FactorIdentities
import RandomSizeMetricDistortion.Numerics.BranchComposition
import RandomSizeMetricDistortion.Numerics.Robustness
import RandomSizeMetricDistortion.Numerics.Benchmark
import RandomSizeMetricDistortion.Numerics.FiniteTemplates
import RandomSizeMetricDistortion.Numerics.RoundedTapeCandidates
import RandomSizeMetricDistortion.Numerics.SourceCancellations
import RandomSizeMetricDistortion.Numerics.FixedTapeCandidates
import RandomSizeMetricDistortion.Numerics.StrongCrossing0
import RandomSizeMetricDistortion.Numerics.FiniteCoordinates
import RandomSizeMetricDistortion.Numerics.FiniteFamily0
import RandomSizeMetricDistortion.Numerics.StrongCrossing1
import RandomSizeMetricDistortion.Numerics.FiniteFamily1
import RandomSizeMetricDistortion.Numerics.StrongCrossing2
import RandomSizeMetricDistortion.Numerics.FiniteFamily2
import RandomSizeMetricDistortion.Numerics.StrongCrossing3
import RandomSizeMetricDistortion.Numerics.FiniteFamily3
import RandomSizeMetricDistortion.Numerics.StrongCrossing4
import RandomSizeMetricDistortion.Numerics.FiniteFamily4
import RandomSizeMetricDistortion.Numerics.StrongCrossing5
import RandomSizeMetricDistortion.Numerics.FiniteFamily5
import RandomSizeMetricDistortion.Numerics.StrongCrossing6
import RandomSizeMetricDistortion.Numerics.FiniteFamily6
import RandomSizeMetricDistortion.Numerics.StrongCrossing7
import RandomSizeMetricDistortion.Numerics.FiniteFamily7
import RandomSizeMetricDistortion.Numerics.StrongCrossing8
import RandomSizeMetricDistortion.Numerics.FiniteFamily8
import RandomSizeMetricDistortion.Numerics.CompleteWitness
import RandomSizeMetricDistortion.Results.ExactStarDistortion
import RandomSizeMetricDistortion.Results.MainUpper
import RandomSizeMetricDistortion.Lower.ReferenceLotteries
import RandomSizeMetricDistortion.Lower.FiniteElectorate
import RandomSizeMetricDistortion.Lower.SymmetricAverages
import RandomSizeMetricDistortion.Lower.PermutationInvariance
import RandomSizeMetricDistortion.Lower.Symmetrization
import RandomSizeMetricDistortion.Lower.ForcedMass
import RandomSizeMetricDistortion.Lower.OffsetCost
import RandomSizeMetricDistortion.Lower.RationalPerturbation
import RandomSizeMetricDistortion.Lower.ScoreFormula
import RandomSizeMetricDistortion.Lower.FirstCase
import RandomSizeMetricDistortion.Lower.NormalizedTail
import RandomSizeMetricDistortion.Lower.IntegerPowerGaps
import RandomSizeMetricDistortion.Lower.AveragedPowerGap
import RandomSizeMetricDistortion.Lower.SecondCase
import RandomSizeMetricDistortion.Results.IntegerLower
import RandomSizeMetricDistortion.Computation.RealMachine
import RandomSizeMetricDistortion.Computation.Preprocessing
import RandomSizeMetricDistortion.Computation.MWTrajectory
import RandomSizeMetricDistortion.Computation.IterationCount
import RandomSizeMetricDistortion.Computation.ScoreScan
import RandomSizeMetricDistortion.Computation.RunRules
import RandomSizeMetricDistortion.Computation.ProgramSetup
import RandomSizeMetricDistortion.Computation.ProgramInverse
import RandomSizeMetricDistortion.Computation.ProgramPrune
import RandomSizeMetricDistortion.Computation.ProgramRelabel
import RandomSizeMetricDistortion.Computation.ProgramRanking
import RandomSizeMetricDistortion.Computation.ProgramPreprocess
import RandomSizeMetricDistortion.Computation.ProgramScores
import RandomSizeMetricDistortion.Computation.ProgramCount
import RandomSizeMetricDistortion.Computation.ProgramSingleton
import RandomSizeMetricDistortion.Computation.ProgramInitialize
import RandomSizeMetricDistortion.Computation.ProgramRound
import RandomSizeMetricDistortion.Computation.ProgramFinish
import RandomSizeMetricDistortion.Computation.ProgramMW
import RandomSizeMetricDistortion.Computation.Program
import RandomSizeMetricDistortion.Shared.ExponentialWeights
import RandomSizeMetricDistortion.Comparison.ScoreBounds
import RandomSizeMetricDistortion.Computation.MWGuarantee
import RandomSizeMetricDistortion.Computation.DiameterBound
import RandomSizeMetricDistortion.Computation.ScoreErrorDistortion
import RandomSizeMetricDistortion.Computation.RestrictionLift
import RandomSizeMetricDistortion.Computation.ProgramCorrectness
import RandomSizeMetricDistortion.Computation.ProgramCost
import RandomSizeMetricDistortion.Computation.Approximation
import RandomSizeMetricDistortion.Appendix.MixingCounterexample
import RandomSizeMetricDistortion.Examples.TwoCandidateGap
import RandomSizeMetricDistortion.Results.PolynomialCorollary

/-! Every selected mathematical interface is instantiated below from actual child proofs. -/
noncomputable section
namespace MetricDistortion.Certified

theorem Numerics_StarLaw : MetricDistortion.Contracts.Numerics_StarLaw.Statement := MetricDistortion.Contracts.Numerics_StarLaw.from_children {child_0 := Model_DrawLaws}
theorem Numerics_WitnessData : MetricDistortion.Contracts.Numerics_WitnessData.Statement := MetricDistortion.witnessData_contract
theorem Numerics_TableCoverage : MetricDistortion.Contracts.Numerics_TableCoverage.Statement := MetricDistortion.Contracts.Numerics_TableCoverage.from_children {child_0 := Numerics_WitnessData}
theorem Numerics_RationalBernstein : MetricDistortion.Contracts.Numerics_RationalBernstein.Statement := MetricDistortion.Contracts.Numerics_RationalBernstein.proved
theorem Numerics_CorrectionSigns : MetricDistortion.Contracts.Numerics_CorrectionSigns.Statement := MetricDistortion.Contracts.Numerics_CorrectionSigns.from_children {child_0 := Numerics_TableCoverage, child_1 := Numerics_RationalBernstein}
theorem Numerics_ShiftedCoefficients : MetricDistortion.Contracts.Numerics_ShiftedCoefficients.Statement := MetricDistortion.Contracts.Numerics_ShiftedCoefficients.proved
theorem Numerics_MeasureSigns : MetricDistortion.Contracts.Numerics_MeasureSigns.Statement := MetricDistortion.Contracts.Numerics_MeasureSigns.from_children {child_0 := Numerics_WitnessData, child_1 := Numerics_ShiftedCoefficients}
theorem Numerics_MeasureMass : MetricDistortion.Contracts.Numerics_MeasureMass.Statement := MetricDistortion.Contracts.Numerics_MeasureMass.from_children {child_0 := Numerics_MeasureSigns, child_1 := Numerics_StarLaw}
theorem Numerics_PolynomialExpressions : MetricDistortion.Contracts.Numerics_PolynomialExpressions.Statement := MetricDistortion.Contracts.Numerics_PolynomialExpressions.proved
theorem Numerics_RationalIntervals : MetricDistortion.Contracts.Numerics_RationalIntervals.Statement := MetricDistortion.Contracts.Numerics_RationalIntervals.from_children {child_0 := Numerics_PolynomialExpressions}
theorem Numerics_DerivativeBounds : MetricDistortion.Contracts.Numerics_DerivativeBounds.Statement := MetricDistortion.Contracts.Numerics_DerivativeBounds.from_children {child_0 := Numerics_PolynomialExpressions}
theorem Numerics_CenteredBounds : MetricDistortion.Contracts.Numerics_CenteredBounds.Statement := MetricDistortion.Contracts.Numerics_CenteredBounds.from_children {child_0 := Numerics_RationalIntervals, child_1 := Numerics_DerivativeBounds, child_2 := Numerics_PolynomialExpressions}
theorem Numerics_MonotoneFaces : MetricDistortion.Contracts.Numerics_MonotoneFaces.Statement := MetricDistortion.Contracts.Numerics_MonotoneFaces.from_children {child_0 := Numerics_RationalIntervals, child_1 := Numerics_DerivativeBounds}
theorem Numerics_TreeSoundness : MetricDistortion.Contracts.Numerics_TreeSoundness.Statement := MetricDistortion.Contracts.Numerics_TreeSoundness.from_children {child_0 := Numerics_RationalIntervals, child_1 := Numerics_CenteredBounds, child_2 := Numerics_MonotoneFaces}
theorem Numerics_MeasureIntervals : MetricDistortion.Contracts.Numerics_MeasureIntervals.Statement := MetricDistortion.Contracts.Numerics_MeasureIntervals.from_children {child_0 := Numerics_MeasureSigns, child_1 := Numerics_MeasureMass}
theorem Numerics_RankMeasurePrimitive : MetricDistortion.Contracts.Numerics_RankMeasurePrimitive.Statement := MetricDistortion.Contracts.Numerics_RankMeasurePrimitive.from_children {child_0 := Numerics_MeasureIntervals, child_1 := Numerics_MeasureMass, child_2 := Numerics_MeasureSigns}
theorem Numerics_DomainTemplates : MetricDistortion.Contracts.Numerics_DomainTemplates.Statement := MetricDistortion.Contracts.Numerics_DomainTemplates.proved
theorem Numerics_TapeReplay : MetricDistortion.Contracts.Numerics_TapeReplay.Statement := MetricDistortion.Contracts.Numerics_TapeReplay.from_children {child_0 := Numerics_DerivativeBounds, child_1 := Numerics_RationalIntervals}
theorem Numerics_EndpointBounds : MetricDistortion.Contracts.Numerics_EndpointBounds.Statement := MetricDistortion.Contracts.Numerics_EndpointBounds.from_children {child_0 := Numerics_TreeSoundness, child_1 := Numerics_MeasureIntervals, child_2 := Numerics_StarLaw, child_3 := Numerics_CorrectionSigns, child_4 := Numerics_RankMeasurePrimitive, child_5 := Numerics_MeasureSigns, child_6 := Numerics_DomainTemplates, child_7 := Numerics_TableCoverage, child_8 := Numerics_TapeReplay}
theorem Numerics_MixedDifference : MetricDistortion.Contracts.Numerics_MixedDifference.Statement := MetricDistortion.Contracts.Numerics_MixedDifference.from_children {child_0 := Numerics_ShiftedCoefficients}
theorem Numerics_FactorIdentities : MetricDistortion.Contracts.Numerics_FactorIdentities.Statement := MetricDistortion.Contracts.Numerics_FactorIdentities.from_children {child_0 := Numerics_WitnessData}
theorem Numerics_BranchComposition : MetricDistortion.Contracts.Numerics_BranchComposition.Statement := MetricDistortion.Contracts.Numerics_BranchComposition.from_children {child_0 := Numerics_MixedDifference, child_1 := Numerics_MeasureIntervals, child_2 := Numerics_DomainTemplates, child_3 := Numerics_FactorIdentities, child_4 := Numerics_MeasureSigns, child_5 := Numerics_StarLaw, child_6 := Numerics_TableCoverage, child_7 := Numerics_MeasureMass, child_8 := Numerics_CorrectionSigns, child_9 := Numerics_RankMeasurePrimitive}
theorem Numerics_Robustness : MetricDistortion.Contracts.Numerics_Robustness.Statement := MetricDistortion.Contracts.Numerics_Robustness.from_children {child_0 := Numerics_WitnessData, child_1 := Numerics_RationalBernstein, child_2 := Numerics_TableCoverage}
theorem Numerics_Benchmark : MetricDistortion.Contracts.Numerics_Benchmark.Statement := MetricDistortion.Contracts.Numerics_Benchmark.from_children {child_0 := Numerics_TreeSoundness}
theorem Numerics_FiniteTemplates : MetricDistortion.Contracts.Numerics_FiniteTemplates.Statement := MetricDistortion.Contracts.Numerics_FiniteTemplates.from_children {child_0 := Numerics_FactorIdentities}
theorem Numerics_RoundedTapeCandidates : MetricDistortion.Contracts.Numerics_RoundedTapeCandidates.Statement := MetricDistortion.Contracts.Numerics_RoundedTapeCandidates.proved
theorem Numerics_SourceCancellations : MetricDistortion.Contracts.Numerics_SourceCancellations.Statement := MetricDistortion.Contracts.Numerics_SourceCancellations.proved
theorem Numerics_FixedTapeCandidates : MetricDistortion.Contracts.Numerics_FixedTapeCandidates.Statement := MetricDistortion.Contracts.Numerics_FixedTapeCandidates.proved
theorem Numerics_StrongCrossing0 : MetricDistortion.Contracts.Numerics_StrongCrossing0.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing0.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteCoordinates : MetricDistortion.Contracts.Numerics_FiniteCoordinates.Statement := MetricDistortion.Contracts.Numerics_FiniteCoordinates.proved
theorem Numerics_FiniteFamily0 : MetricDistortion.Contracts.Numerics_FiniteFamily0.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily0.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing0, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing1 : MetricDistortion.Contracts.Numerics_StrongCrossing1.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing1.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily1 : MetricDistortion.Contracts.Numerics_FiniteFamily1.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily1.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing1, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing2 : MetricDistortion.Contracts.Numerics_StrongCrossing2.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing2.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily2 : MetricDistortion.Contracts.Numerics_FiniteFamily2.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily2.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing2, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing3 : MetricDistortion.Contracts.Numerics_StrongCrossing3.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing3.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily3 : MetricDistortion.Contracts.Numerics_FiniteFamily3.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily3.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing3, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing4 : MetricDistortion.Contracts.Numerics_StrongCrossing4.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing4.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily4 : MetricDistortion.Contracts.Numerics_FiniteFamily4.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily4.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing4, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing5 : MetricDistortion.Contracts.Numerics_StrongCrossing5.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing5.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily5 : MetricDistortion.Contracts.Numerics_FiniteFamily5.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily5.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing5, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing6 : MetricDistortion.Contracts.Numerics_StrongCrossing6.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing6.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily6 : MetricDistortion.Contracts.Numerics_FiniteFamily6.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily6.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing6, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing7 : MetricDistortion.Contracts.Numerics_StrongCrossing7.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing7.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily7 : MetricDistortion.Contracts.Numerics_FiniteFamily7.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily7.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing7, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_StrongCrossing8 : MetricDistortion.Contracts.Numerics_StrongCrossing8.Statement := MetricDistortion.Contracts.Numerics_StrongCrossing8.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_TableCoverage, child_3 := Numerics_TapeReplay, child_4 := Numerics_RoundedTapeCandidates, child_5 := Numerics_SourceCancellations, child_6 := Numerics_FixedTapeCandidates}
theorem Numerics_FiniteFamily8 : MetricDistortion.Contracts.Numerics_FiniteFamily8.Statement := MetricDistortion.Contracts.Numerics_FiniteFamily8.from_children {child_0 := Numerics_FiniteTemplates, child_1 := Numerics_TreeSoundness, child_2 := Numerics_ShiftedCoefficients, child_3 := Numerics_TableCoverage, child_4 := Numerics_TapeReplay, child_5 := Numerics_RoundedTapeCandidates, child_6 := Numerics_StrongCrossing8, child_7 := Numerics_MeasureSigns, child_8 := Numerics_SourceCancellations, child_9 := Numerics_FiniteCoordinates, child_10 := Numerics_FixedTapeCandidates}
theorem Numerics_CompleteWitness : MetricDistortion.Contracts.Numerics_CompleteWitness.Statement := MetricDistortion.Contracts.Numerics_CompleteWitness.from_children {child_0 := Numerics_StarLaw, child_1 := Numerics_TableCoverage, child_2 := Numerics_CorrectionSigns, child_3 := Numerics_MeasureMass, child_4 := Numerics_EndpointBounds, child_5 := Numerics_BranchComposition, child_6 := Numerics_Robustness, child_7 := Numerics_Benchmark, child_8 := Numerics_FiniteFamily0, child_9 := Numerics_FiniteFamily1, child_10 := Numerics_FiniteFamily2, child_11 := Numerics_FiniteFamily3, child_12 := Numerics_FiniteFamily4, child_13 := Numerics_FiniteFamily5, child_14 := Numerics_FiniteFamily6, child_15 := Numerics_FiniteFamily7, child_16 := Numerics_FiniteFamily8, child_17 := Numerics_StrongCrossing0, child_18 := Numerics_StrongCrossing1, child_19 := Numerics_StrongCrossing2, child_20 := Numerics_StrongCrossing3, child_21 := Numerics_StrongCrossing4, child_22 := Numerics_StrongCrossing5, child_23 := Numerics_StrongCrossing6, child_24 := Numerics_StrongCrossing7, child_25 := Numerics_StrongCrossing8}
theorem Results_ExactStarDistortion : MetricDistortion.Contracts.Results_ExactStarDistortion.Statement := MetricDistortion.Contracts.Results_ExactStarDistortion.from_children {child_0 := Geometry_RankCutCriterion, child_1 := Numerics_CompleteWitness}
theorem Results_MainUpper : MetricDistortion.Contracts.Results_MainUpper.Statement := MetricDistortion.Contracts.Results_MainUpper.from_children {child_0 := Stability_Existence, child_1 := Numerics_CompleteWitness, child_2 := Results_ExactStarDistortion}
theorem Lower_ReferenceLotteries : MetricDistortion.Contracts.Lower_ReferenceLotteries.Statement := MetricDistortion.Contracts.Lower_ReferenceLotteries.from_children {child_0 := Model_Lotteries}
theorem Lower_FiniteElectorate : MetricDistortion.Contracts.Lower_FiniteElectorate.Statement := MetricDistortion.Contracts.Lower_FiniteElectorate.from_children {child_0 := Model_Profiles}
theorem Lower_SymmetricAverages : MetricDistortion.Contracts.Lower_SymmetricAverages.Statement := MetricDistortion.Contracts.Lower_SymmetricAverages.proved
theorem Lower_PermutationInvariance : MetricDistortion.Contracts.Lower_PermutationInvariance.Statement := MetricDistortion.Contracts.Lower_PermutationInvariance.from_children {child_0 := Comparison_CandidateDraws, child_1 := Lower_SymmetricAverages}
theorem Lower_Symmetrization : MetricDistortion.Contracts.Lower_Symmetrization.Statement := MetricDistortion.Contracts.Lower_Symmetrization.from_children {child_0 := Comparison_CandidateDraws, child_1 := Lower_ReferenceLotteries, child_2 := Lower_FiniteElectorate, child_3 := Lower_SymmetricAverages, child_4 := Lower_PermutationInvariance}
theorem Lower_ForcedMass : MetricDistortion.Contracts.Lower_ForcedMass.Statement := MetricDistortion.Contracts.Lower_ForcedMass.from_children {child_0 := Lower_Symmetrization, child_1 := Comparison_SelfPlay, child_2 := Comparison_CandidateDraws, child_3 := Lower_PermutationInvariance, child_4 := Lower_ReferenceLotteries}
theorem Lower_OffsetCost : MetricDistortion.Contracts.Lower_OffsetCost.Statement := MetricDistortion.Contracts.Lower_OffsetCost.from_children {child_0 := Offsets_MetricRealization, child_1 := Lower_FiniteElectorate, child_2 := Lower_SymmetricAverages}
theorem Lower_RationalPerturbation : MetricDistortion.Contracts.Lower_RationalPerturbation.Statement := MetricDistortion.Contracts.Lower_RationalPerturbation.proved
theorem Lower_ScoreFormula : MetricDistortion.Contracts.Lower_ScoreFormula.Statement := MetricDistortion.Contracts.Lower_ScoreFormula.from_children {child_0 := Comparison_CandidateDraws, child_1 := Lower_ReferenceLotteries, child_2 := Lower_SymmetricAverages, child_3 := Analysis_GeneratingFunction}
theorem Lower_FirstCase : MetricDistortion.Contracts.Lower_FirstCase.Statement := MetricDistortion.Contracts.Lower_FirstCase.from_children {child_0 := Lower_ForcedMass, child_1 := Lower_OffsetCost, child_2 := Lower_RationalPerturbation, child_3 := Comparison_CandidateDraws, child_4 := Lower_ScoreFormula, child_5 := Lower_ReferenceLotteries}
theorem Lower_NormalizedTail : MetricDistortion.Contracts.Lower_NormalizedTail.Statement := MetricDistortion.Contracts.Lower_NormalizedTail.proved
theorem Lower_IntegerPowerGaps : MetricDistortion.Contracts.Lower_IntegerPowerGaps.Statement := MetricDistortion.Contracts.Lower_IntegerPowerGaps.from_children {child_0 := Lower_NormalizedTail}
theorem Lower_AveragedPowerGap : MetricDistortion.Contracts.Lower_AveragedPowerGap.Statement := MetricDistortion.Contracts.Lower_AveragedPowerGap.from_children {child_0 := Lower_IntegerPowerGaps, child_1 := Analysis_IntegralMixture, child_2 := Model_DrawLaws}
theorem Lower_SecondCase : MetricDistortion.Contracts.Lower_SecondCase.Statement := MetricDistortion.Contracts.Lower_SecondCase.from_children {child_0 := Lower_ScoreFormula, child_1 := Lower_AveragedPowerGap, child_2 := Lower_ForcedMass, child_3 := Lower_OffsetCost, child_4 := Lower_RationalPerturbation, child_5 := Lower_ReferenceLotteries}
theorem Results_IntegerLower : MetricDistortion.Contracts.Results_IntegerLower.Statement := MetricDistortion.Contracts.Results_IntegerLower.from_children {child_0 := Lower_FirstCase, child_1 := Lower_SecondCase, child_2 := Lower_RationalPerturbation, child_3 := Lower_FiniteElectorate}
theorem Computation_RealMachine : MetricDistortion.Contracts.Computation_RealMachine.Statement := MetricDistortion.Contracts.Computation_RealMachine.proved
theorem Computation_Preprocessing : MetricDistortion.Contracts.Computation_Preprocessing.Statement := MetricDistortion.Contracts.Computation_Preprocessing.from_children {child_0 := Model_Profiles, child_1 := Model_Metrics}
theorem Computation_MWTrajectory : MetricDistortion.Contracts.Computation_MWTrajectory.Statement := MetricDistortion.Contracts.Computation_MWTrajectory.from_children {child_0 := Model_Lotteries, child_1 := Comparison_CandidateDraws}
theorem Computation_IterationCount : MetricDistortion.Contracts.Computation_IterationCount.Statement := MetricDistortion.Contracts.Computation_IterationCount.proved
theorem Computation_ScoreScan : MetricDistortion.Contracts.Computation_ScoreScan.Statement := MetricDistortion.Contracts.Computation_ScoreScan.from_children {child_0 := Comparison_CandidateDraws, child_1 := Numerics_StarLaw}
theorem Computation_RunRules : MetricDistortion.Contracts.Computation_RunRules.Statement := MetricDistortion.Contracts.Computation_RunRules.proved
theorem Computation_ProgramSetup : MetricDistortion.Contracts.Computation_ProgramSetup.Statement := MetricDistortion.Contracts.Computation_ProgramSetup.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramInverse : MetricDistortion.Contracts.Computation_ProgramInverse.Statement := MetricDistortion.Contracts.Computation_ProgramInverse.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramPrune : MetricDistortion.Contracts.Computation_ProgramPrune.Statement := MetricDistortion.Contracts.Computation_ProgramPrune.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramRelabel : MetricDistortion.Contracts.Computation_ProgramRelabel.Statement := MetricDistortion.Contracts.Computation_ProgramRelabel.from_children {child_0 := Computation_RunRules, child_1 := Computation_Preprocessing}
theorem Computation_ProgramRanking : MetricDistortion.Contracts.Computation_ProgramRanking.Statement := MetricDistortion.Contracts.Computation_ProgramRanking.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramPreprocess : MetricDistortion.Contracts.Computation_ProgramPreprocess.Statement := MetricDistortion.Contracts.Computation_ProgramPreprocess.from_children {child_0 := Computation_RealMachine, child_1 := Computation_Preprocessing, child_2 := Computation_RunRules, child_3 := Computation_ProgramSetup, child_4 := Computation_ProgramInverse, child_5 := Computation_ProgramPrune, child_6 := Computation_ProgramRelabel, child_7 := Computation_ProgramRanking}
theorem Computation_ProgramScores : MetricDistortion.Contracts.Computation_ProgramScores.Statement := MetricDistortion.Contracts.Computation_ProgramScores.from_children {child_0 := Computation_RunRules, child_1 := Computation_ScoreScan}
theorem Computation_ProgramCount : MetricDistortion.Contracts.Computation_ProgramCount.Statement := MetricDistortion.Contracts.Computation_ProgramCount.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramSingleton : MetricDistortion.Contracts.Computation_ProgramSingleton.Statement := MetricDistortion.Contracts.Computation_ProgramSingleton.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramInitialize : MetricDistortion.Contracts.Computation_ProgramInitialize.Statement := MetricDistortion.Contracts.Computation_ProgramInitialize.from_children {child_0 := Computation_RunRules, child_1 := Computation_ProgramCount, child_2 := Computation_MWTrajectory, child_3 := Numerics_StarLaw}
theorem Computation_ProgramRound : MetricDistortion.Contracts.Computation_ProgramRound.Statement := MetricDistortion.Contracts.Computation_ProgramRound.from_children {child_0 := Computation_RunRules, child_1 := Computation_ProgramScores}
theorem Computation_ProgramFinish : MetricDistortion.Contracts.Computation_ProgramFinish.Statement := MetricDistortion.Contracts.Computation_ProgramFinish.from_children {child_0 := Computation_RunRules}
theorem Computation_ProgramMW : MetricDistortion.Contracts.Computation_ProgramMW.Statement := MetricDistortion.Contracts.Computation_ProgramMW.from_children {child_0 := Computation_RunRules, child_1 := Computation_ProgramScores, child_2 := Computation_MWTrajectory, child_3 := Computation_IterationCount, child_4 := Numerics_StarLaw, child_5 := Computation_ProgramCount, child_6 := Computation_ProgramSingleton, child_7 := Computation_ProgramInitialize, child_8 := Computation_ProgramRound, child_9 := Computation_ProgramFinish}
theorem Computation_Program : MetricDistortion.Contracts.Computation_Program.Statement := MetricDistortion.Contracts.Computation_Program.from_children {child_0 := Computation_RealMachine, child_1 := Computation_Preprocessing, child_2 := Computation_MWTrajectory, child_3 := Computation_IterationCount, child_4 := Computation_ScoreScan, child_5 := Computation_RunRules, child_6 := Computation_ProgramPreprocess, child_7 := Computation_ProgramMW}
theorem Shared_ExponentialWeights : MetricDistortion.Contracts.Shared_ExponentialWeights.Statement := MetricDistortion.Contracts.Shared_ExponentialWeights.proved
theorem Comparison_ScoreBounds : MetricDistortion.Contracts.Comparison_ScoreBounds.Statement := MetricDistortion.Contracts.Comparison_ScoreBounds.from_children {child_0 := Comparison_CandidateDraws, child_1 := Analysis_GeneratingFunction, child_2 := Model_DrawLaws}
theorem Computation_MWGuarantee : MetricDistortion.Contracts.Computation_MWGuarantee.Statement := MetricDistortion.Contracts.Computation_MWGuarantee.from_children {child_0 := Shared_ExponentialWeights, child_1 := Computation_MWTrajectory, child_2 := Computation_IterationCount, child_3 := Comparison_SelfPlay, child_4 := Comparison_CandidateDraws, child_5 := Comparison_ScoreBounds}
theorem Computation_DiameterBound : MetricDistortion.Contracts.Computation_DiameterBound.Statement := MetricDistortion.Contracts.Computation_DiameterBound.from_children {child_0 := Computation_Preprocessing, child_1 := Model_Metrics}
theorem Computation_ScoreErrorDistortion : MetricDistortion.Contracts.Computation_ScoreErrorDistortion.Statement := MetricDistortion.Contracts.Computation_ScoreErrorDistortion.from_children {child_0 := Geometry_RankCutCriterion, child_1 := Numerics_CompleteWitness, child_2 := Computation_DiameterBound, child_3 := Geometry_AverageAndDistortion}
theorem Computation_RestrictionLift : MetricDistortion.Contracts.Computation_RestrictionLift.Statement := MetricDistortion.Contracts.Computation_RestrictionLift.from_children {child_0 := Computation_Preprocessing, child_1 := Model_Metrics}
theorem Computation_ProgramCorrectness : MetricDistortion.Contracts.Computation_ProgramCorrectness.Statement := MetricDistortion.Contracts.Computation_ProgramCorrectness.from_children {child_0 := Computation_Program, child_1 := Computation_MWGuarantee, child_2 := Computation_ScoreErrorDistortion, child_3 := Computation_Preprocessing, child_4 := Computation_RestrictionLift, child_5 := Computation_RealMachine}
theorem Computation_ProgramCost : MetricDistortion.Contracts.Computation_ProgramCost.Statement := MetricDistortion.Contracts.Computation_ProgramCost.from_children {child_0 := Computation_Program, child_1 := Computation_ProgramCorrectness, child_2 := Computation_ScoreScan, child_3 := Computation_IterationCount}
theorem Computation_Approximation : MetricDistortion.Contracts.Computation_Approximation.Statement := MetricDistortion.Contracts.Computation_Approximation.from_children {child_0 := Computation_Program, child_1 := Computation_ProgramCorrectness, child_2 := Computation_ProgramCost}
theorem Appendix_MixingCounterexample : MetricDistortion.Contracts.Appendix_MixingCounterexample.Statement := MetricDistortion.Contracts.Appendix_MixingCounterexample.from_children {child_0 := Comparison_CandidateDraws, child_1 := Model_Lotteries}
theorem Examples_TwoCandidateGap : MetricDistortion.Contracts.Examples_TwoCandidateGap.Statement := MetricDistortion.Contracts.Examples_TwoCandidateGap.from_children {child_0 := Model_Metrics, child_1 := Model_Lotteries, child_2 := Model_DistortionConventions}
theorem Results_PolynomialCorollary : MetricDistortion.Contracts.Results_PolynomialCorollary.Statement := MetricDistortion.Contracts.Results_PolynomialCorollary.from_children {child_0 := Computation_Approximation}
theorem Certificate : MetricDistortion.Contracts.Certificate.Statement := ⟨Results_MainUpper, Results_IntegerLower, Computation_Approximation⟩

end MetricDistortion.Certified

namespace MetricDistortion

theorem certificate : Contracts.Certificate.Statement := Certified.Certificate
theorem main_upper_bound : Contracts.Results_MainUpper.Statement := Certified.Results_MainUpper
theorem integer_draw_lower_bound : Contracts.Results_IntegerLower.Statement := Certified.Results_IntegerLower
theorem approximation_program : Contracts.Computation_Approximation.Statement := Certified.Computation_Approximation
theorem polynomial_time_corollary : Contracts.Results_PolynomialCorollary.Statement := Certified.Results_PolynomialCorollary

#print axioms certificate
end MetricDistortion
