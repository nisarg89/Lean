import RandomSizeMetricDistortion.Certificate
import RandomSizeMetricDistortion.StarCertificate
import Lean.Util.CollectAxioms
import Lean.Util.FindExpr

set_option maxRecDepth 0
set_option maxHeartbeats 0

namespace MetricDistortion.Audit
open Lean Elab Command Meta

private def auditTheorem (name : Name) (expected : Expr) : CommandElabM Unit := do
  let some info := (← getEnv).find? name | throwError "missing certified theorem: {name}"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "certified export is not a theorem: {name}"
  unless (← liftTermElabM <| withTransparency .all <| isDefEq info.type expected) do
    throwError "certified theorem does not have its exact stated contract: {name}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun ax => !allowed.contains ax
  unless bad.isEmpty do
    throwError "nonstandard axioms in {name}: {bad.toList}"
  let ty ← liftTermElabM <| withTransparency .all <| whnf info.type
  if ty.hasExprMVar then throwError "unresolved metavariable in {name}"
  let provider := ty.find? fun e =>
    match e with
    | .const (.str _ "Needs") _ => true
    | _ => false
  if provider.isSome then throwError "unresolved provider interface in {name}"

elab "#metric_distortion_audit " id:ident " : " expected:term : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let target ← liftTermElabM <| Term.elabTerm expected (some (mkSort .zero))
  if target.hasExprMVar then throwError "unresolved expected theorem contract"
  names.forM fun name => auditTheorem name target

/-- Check the exact type and allowed transitive axioms of a released definition. -/
private def auditDefinition (name : Name) (expected : Expr) : CommandElabM Unit := do
  let some info := (← getEnv).find? name | throwError "missing certified definition: {name}"
  match info with
  | .defnInfo _ => pure ()
  | _ => throwError "certified export is not a definition: {name}"
  unless (← liftTermElabM <| withTransparency .all <| isDefEq info.type expected) do
    throwError "certified definition does not have its exact stated type: {name}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms name
  let bad := axioms.filter fun ax => !allowed.contains ax
  unless bad.isEmpty do
    throwError "nonstandard axioms in {name}: {bad.toList}"
  let ty ← liftTermElabM <| withTransparency .all <| whnf info.type
  if ty.hasExprMVar then throwError "unresolved metavariable in {name}"
  let provider := ty.find? fun e =>
    match e with
    | .const (.str _ "Needs") _ => true
    | _ => false
  if provider.isSome then throwError "unresolved provider interface in {name}"

elab "#metric_distortion_audit_def " id:ident " : " expected:term : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let target ← liftTermElabM <| Term.elabTerm expected none
  if target.hasExprMVar then throwError "unresolved expected definition type"
  names.forM fun name => auditDefinition name target

end MetricDistortion.Audit

#metric_distortion_audit MetricDistortion.Certified.Shared_CompactConvexMinimax : MetricDistortion.Contracts.Shared_CompactConvexMinimax.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_DrawLaws : MetricDistortion.Contracts.Model_DrawLaws.Statement
#metric_distortion_audit MetricDistortion.Certified.Analysis_DrawSummability : MetricDistortion.Contracts.Analysis_DrawSummability.Statement
#metric_distortion_audit MetricDistortion.Certified.Analysis_IntegralMixture : MetricDistortion.Contracts.Analysis_IntegralMixture.Statement
#metric_distortion_audit MetricDistortion.Certified.Analysis_GeneratingFunction : MetricDistortion.Contracts.Analysis_GeneratingFunction.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_Lotteries : MetricDistortion.Contracts.Model_Lotteries.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_ScoreRegularity : MetricDistortion.Contracts.Comparison_ScoreRegularity.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_ChallengerLinearity : MetricDistortion.Contracts.Comparison_ChallengerLinearity.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_PowerIntegral : MetricDistortion.Contracts.Comparison_PowerIntegral.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_LabeledTie : MetricDistortion.Contracts.Comparison_LabeledTie.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_FixedDrawIntegral : MetricDistortion.Contracts.Comparison_FixedDrawIntegral.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_Profiles : MetricDistortion.Contracts.Model_Profiles.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_RankIntervals : MetricDistortion.Contracts.Model_RankIntervals.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_Exchangeability : MetricDistortion.Contracts.Comparison_Exchangeability.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_CountableMixture : MetricDistortion.Contracts.Comparison_CountableMixture.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_SelfPlay : MetricDistortion.Contracts.Comparison_SelfPlay.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_AffineSubstitution : MetricDistortion.Contracts.Comparison_AffineSubstitution.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_CandidateDraws : MetricDistortion.Contracts.Comparison_CandidateDraws.Statement
#metric_distortion_audit MetricDistortion.Certified.Stability_MinimaxApplication : MetricDistortion.Contracts.Stability_MinimaxApplication.Statement
#metric_distortion_audit MetricDistortion.Certified.Stability_SupportEquality : MetricDistortion.Contracts.Stability_SupportEquality.Statement
#metric_distortion_audit MetricDistortion.Certified.Stability_Existence : MetricDistortion.Contracts.Stability_Existence.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StarLaw : MetricDistortion.Contracts.Numerics_StarLaw.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_WitnessData : MetricDistortion.Contracts.Numerics_WitnessData.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_TableCoverage : MetricDistortion.Contracts.Numerics_TableCoverage.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_RationalBernstein : MetricDistortion.Contracts.Numerics_RationalBernstein.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_CorrectionSigns : MetricDistortion.Contracts.Numerics_CorrectionSigns.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_ShiftedCoefficients : MetricDistortion.Contracts.Numerics_ShiftedCoefficients.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_MeasureSigns : MetricDistortion.Contracts.Numerics_MeasureSigns.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_MeasureMass : MetricDistortion.Contracts.Numerics_MeasureMass.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_PolynomialExpressions : MetricDistortion.Contracts.Numerics_PolynomialExpressions.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_RationalIntervals : MetricDistortion.Contracts.Numerics_RationalIntervals.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_DerivativeBounds : MetricDistortion.Contracts.Numerics_DerivativeBounds.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_CenteredBounds : MetricDistortion.Contracts.Numerics_CenteredBounds.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_MonotoneFaces : MetricDistortion.Contracts.Numerics_MonotoneFaces.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_TreeSoundness : MetricDistortion.Contracts.Numerics_TreeSoundness.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_MeasureIntervals : MetricDistortion.Contracts.Numerics_MeasureIntervals.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_RankMeasurePrimitive : MetricDistortion.Contracts.Numerics_RankMeasurePrimitive.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_DomainTemplates : MetricDistortion.Contracts.Numerics_DomainTemplates.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_TapeReplay : MetricDistortion.Contracts.Numerics_TapeReplay.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_EndpointBounds : MetricDistortion.Contracts.Numerics_EndpointBounds.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_MixedDifference : MetricDistortion.Contracts.Numerics_MixedDifference.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FactorIdentities : MetricDistortion.Contracts.Numerics_FactorIdentities.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_BranchComposition : MetricDistortion.Contracts.Numerics_BranchComposition.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_Robustness : MetricDistortion.Contracts.Numerics_Robustness.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_Benchmark : MetricDistortion.Contracts.Numerics_Benchmark.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteTemplates : MetricDistortion.Contracts.Numerics_FiniteTemplates.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_RoundedTapeCandidates : MetricDistortion.Contracts.Numerics_RoundedTapeCandidates.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_SourceCancellations : MetricDistortion.Contracts.Numerics_SourceCancellations.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FixedTapeCandidates : MetricDistortion.Contracts.Numerics_FixedTapeCandidates.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing0 : MetricDistortion.Contracts.Numerics_StrongCrossing0.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteCoordinates : MetricDistortion.Contracts.Numerics_FiniteCoordinates.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily0 : MetricDistortion.Contracts.Numerics_FiniteFamily0.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing1 : MetricDistortion.Contracts.Numerics_StrongCrossing1.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily1 : MetricDistortion.Contracts.Numerics_FiniteFamily1.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing2 : MetricDistortion.Contracts.Numerics_StrongCrossing2.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily2 : MetricDistortion.Contracts.Numerics_FiniteFamily2.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing3 : MetricDistortion.Contracts.Numerics_StrongCrossing3.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily3 : MetricDistortion.Contracts.Numerics_FiniteFamily3.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing4 : MetricDistortion.Contracts.Numerics_StrongCrossing4.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily4 : MetricDistortion.Contracts.Numerics_FiniteFamily4.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing5 : MetricDistortion.Contracts.Numerics_StrongCrossing5.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily5 : MetricDistortion.Contracts.Numerics_FiniteFamily5.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing6 : MetricDistortion.Contracts.Numerics_StrongCrossing6.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily6 : MetricDistortion.Contracts.Numerics_FiniteFamily6.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing7 : MetricDistortion.Contracts.Numerics_StrongCrossing7.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily7 : MetricDistortion.Contracts.Numerics_FiniteFamily7.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_StrongCrossing8 : MetricDistortion.Contracts.Numerics_StrongCrossing8.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_FiniteFamily8 : MetricDistortion.Contracts.Numerics_FiniteFamily8.Statement
#metric_distortion_audit MetricDistortion.Certified.Numerics_CompleteWitness : MetricDistortion.Contracts.Numerics_CompleteWitness.Statement
#metric_distortion_audit MetricDistortion.Certified.Analysis_MonotoneSetIntegral : MetricDistortion.Contracts.Analysis_MonotoneSetIntegral.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_Rearrangement : MetricDistortion.Contracts.Geometry_Rearrangement.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_Metrics : MetricDistortion.Contracts.Model_Metrics.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_CutoffProperties : MetricDistortion.Contracts.Geometry_CutoffProperties.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_ThresholdStepFunctions : MetricDistortion.Contracts.Geometry_ThresholdStepFunctions.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_MetricTail : MetricDistortion.Contracts.Geometry_MetricTail.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_CrossingDiameter : MetricDistortion.Contracts.Geometry_CrossingDiameter.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_CrossingMeasure : MetricDistortion.Contracts.Geometry_CrossingMeasure.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_MetricRankCuts : MetricDistortion.Contracts.Geometry_MetricRankCuts.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_IntegratedLocalCut : MetricDistortion.Contracts.Geometry_IntegratedLocalCut.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_CommonCharge : MetricDistortion.Contracts.Geometry_CommonCharge.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_ApproximateCancellation : MetricDistortion.Contracts.Geometry_ApproximateCancellation.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_DistortionConventions : MetricDistortion.Contracts.Model_DistortionConventions.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_AverageAndDistortion : MetricDistortion.Contracts.Geometry_AverageAndDistortion.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_RankCutCriterion : MetricDistortion.Contracts.Geometry_RankCutCriterion.Statement
#metric_distortion_audit MetricDistortion.Certified.Results_ExactStarDistortion : MetricDistortion.Contracts.Results_ExactStarDistortion.Statement
#metric_distortion_audit MetricDistortion.Certified.Results_MainUpper : MetricDistortion.Contracts.Results_MainUpper.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_ReferenceLotteries : MetricDistortion.Contracts.Lower_ReferenceLotteries.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_FiniteElectorate : MetricDistortion.Contracts.Lower_FiniteElectorate.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_SymmetricAverages : MetricDistortion.Contracts.Lower_SymmetricAverages.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_PermutationInvariance : MetricDistortion.Contracts.Lower_PermutationInvariance.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_Symmetrization : MetricDistortion.Contracts.Lower_Symmetrization.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_ForcedMass : MetricDistortion.Contracts.Lower_ForcedMass.Statement
#metric_distortion_audit MetricDistortion.Certified.Offsets_BipartiteExtension : MetricDistortion.Contracts.Offsets_BipartiteExtension.Statement
#metric_distortion_audit MetricDistortion.Certified.Model_OffsetDefinitions : MetricDistortion.Contracts.Model_OffsetDefinitions.Statement
#metric_distortion_audit MetricDistortion.Certified.Offsets_CrossDistanceProperties : MetricDistortion.Contracts.Offsets_CrossDistanceProperties.Statement
#metric_distortion_audit MetricDistortion.Certified.Offsets_MetricRealization : MetricDistortion.Contracts.Offsets_MetricRealization.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_OffsetCost : MetricDistortion.Contracts.Lower_OffsetCost.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_RationalPerturbation : MetricDistortion.Contracts.Lower_RationalPerturbation.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_ScoreFormula : MetricDistortion.Contracts.Lower_ScoreFormula.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_FirstCase : MetricDistortion.Contracts.Lower_FirstCase.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_NormalizedTail : MetricDistortion.Contracts.Lower_NormalizedTail.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_IntegerPowerGaps : MetricDistortion.Contracts.Lower_IntegerPowerGaps.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_AveragedPowerGap : MetricDistortion.Contracts.Lower_AveragedPowerGap.Statement
#metric_distortion_audit MetricDistortion.Certified.Lower_SecondCase : MetricDistortion.Contracts.Lower_SecondCase.Statement
#metric_distortion_audit MetricDistortion.Certified.Results_IntegerLower : MetricDistortion.Contracts.Results_IntegerLower.Statement
#metric_distortion_audit MetricDistortion.Certified.Geometry_RankStability : MetricDistortion.Contracts.Geometry_RankStability.Statement
#metric_distortion_audit MetricDistortion.Certified.Offsets_MetricDomination : MetricDistortion.Contracts.Offsets_MetricDomination.Statement
#metric_distortion_audit MetricDistortion.Certified.Offsets_ReductionToOffsets : MetricDistortion.Contracts.Offsets_ReductionToOffsets.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_RealMachine : MetricDistortion.Contracts.Computation_RealMachine.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_Preprocessing : MetricDistortion.Contracts.Computation_Preprocessing.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_MWTrajectory : MetricDistortion.Contracts.Computation_MWTrajectory.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_IterationCount : MetricDistortion.Contracts.Computation_IterationCount.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ScoreScan : MetricDistortion.Contracts.Computation_ScoreScan.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_RunRules : MetricDistortion.Contracts.Computation_RunRules.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramSetup : MetricDistortion.Contracts.Computation_ProgramSetup.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramInverse : MetricDistortion.Contracts.Computation_ProgramInverse.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramPrune : MetricDistortion.Contracts.Computation_ProgramPrune.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramRelabel : MetricDistortion.Contracts.Computation_ProgramRelabel.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramRanking : MetricDistortion.Contracts.Computation_ProgramRanking.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramPreprocess : MetricDistortion.Contracts.Computation_ProgramPreprocess.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramScores : MetricDistortion.Contracts.Computation_ProgramScores.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramCount : MetricDistortion.Contracts.Computation_ProgramCount.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramSingleton : MetricDistortion.Contracts.Computation_ProgramSingleton.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramInitialize : MetricDistortion.Contracts.Computation_ProgramInitialize.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramRound : MetricDistortion.Contracts.Computation_ProgramRound.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramFinish : MetricDistortion.Contracts.Computation_ProgramFinish.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramMW : MetricDistortion.Contracts.Computation_ProgramMW.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_Program : MetricDistortion.Contracts.Computation_Program.Statement
#metric_distortion_audit MetricDistortion.Certified.Shared_ExponentialWeights : MetricDistortion.Contracts.Shared_ExponentialWeights.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_ScoreBounds : MetricDistortion.Contracts.Comparison_ScoreBounds.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_MWGuarantee : MetricDistortion.Contracts.Computation_MWGuarantee.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_DiameterBound : MetricDistortion.Contracts.Computation_DiameterBound.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ScoreErrorDistortion : MetricDistortion.Contracts.Computation_ScoreErrorDistortion.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_RestrictionLift : MetricDistortion.Contracts.Computation_RestrictionLift.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramCorrectness : MetricDistortion.Contracts.Computation_ProgramCorrectness.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_ProgramCost : MetricDistortion.Contracts.Computation_ProgramCost.Statement
#metric_distortion_audit MetricDistortion.Certified.Computation_Approximation : MetricDistortion.Contracts.Computation_Approximation.Statement
#metric_distortion_audit MetricDistortion.Certified.Appendix_MixingCounterexample : MetricDistortion.Contracts.Appendix_MixingCounterexample.Statement
#metric_distortion_audit MetricDistortion.Certified.Examples_TwoCandidateGap : MetricDistortion.Contracts.Examples_TwoCandidateGap.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_FixedDrawSpecialization : MetricDistortion.Contracts.Comparison_FixedDrawSpecialization.Statement
#metric_distortion_audit MetricDistortion.Certified.Comparison_MaximalLottery : MetricDistortion.Contracts.Comparison_MaximalLottery.Statement
#metric_distortion_audit MetricDistortion.Certified.Results_PolynomialCorollary : MetricDistortion.Contracts.Results_PolynomialCorollary.Statement
#metric_distortion_audit MetricDistortion.Certified.Certificate : MetricDistortion.Contracts.Certificate.Statement
#metric_distortion_audit MetricDistortion.certificate : MetricDistortion.Contracts.Certificate.Statement
#metric_distortion_audit MetricDistortion.main_upper_bound : MetricDistortion.Contracts.Results_MainUpper.Statement
#metric_distortion_audit MetricDistortion.integer_draw_lower_bound : MetricDistortion.Contracts.Results_IntegerLower.Statement
#metric_distortion_audit MetricDistortion.approximation_program : MetricDistortion.Contracts.Computation_Approximation.Statement
#metric_distortion_audit MetricDistortion.polynomial_time_corollary : MetricDistortion.Contracts.Results_PolynomialCorollary.Statement

namespace MetricDistortion.Audit.Star

/-- Exact exported type of the paper-specific draw law. -/
def lawType : Type := MetricDistortion.DrawLaw
/-- Exact exported type of the paper-specific certificate constructor. -/
def certificateForType : Type := ∀ law : MetricDistortion.DrawLaw,
  MetricDistortion.IsStarLaw law → Voting.Distortion.UpperBoundCertificate law
/-- Exact exported type of the paper-specific certificate. -/
def certificateType : Type := Voting.Distortion.UpperBoundCertificate MetricDistortion.starLaw
/-- Exact statement of the paper-specific draw law. -/
def lawSpec : Prop := MetricDistortion.IsStarLaw MetricDistortion.starLaw
/-- Exact numerical conclusion of the paper-specific certificate. -/
def bound : Prop := MetricDistortion.starCertificate.bound = (213609 / 100000 : ℝ)
/-- Exact approximation condition with the paper's constant. -/
def approximation : Prop := Voting.Distortion.ApproximationCertificate
  MetricDistortion.starCertificate 16

end MetricDistortion.Audit.Star

#metric_distortion_audit_def MetricDistortion.starLaw : MetricDistortion.Audit.Star.lawType
#metric_distortion_audit_def MetricDistortion.starCertificateFor : MetricDistortion.Audit.Star.certificateForType
#metric_distortion_audit_def MetricDistortion.starCertificate : MetricDistortion.Audit.Star.certificateType
#metric_distortion_audit MetricDistortion.starLaw_spec : MetricDistortion.Audit.Star.lawSpec
#metric_distortion_audit MetricDistortion.starCertificate_bound : MetricDistortion.Audit.Star.bound
#metric_distortion_audit MetricDistortion.starCertificate_approximation : MetricDistortion.Audit.Star.approximation
