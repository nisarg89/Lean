import Voting.Distortion
import Lean.Util.CollectAxioms
import Lean.Util.FindExpr

set_option maxRecDepth 0
set_option maxHeartbeats 0

namespace Voting.Distortion.Audit
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

elab "#distortion_audit " id:ident " : " expected:term : command => do
  let names ← liftCoreM <| realizeGlobalConstWithInfos id
  let target ← liftTermElabM <| Term.elabTerm expected (some (mkSort .zero))
  if target.hasExprMVar then throwError "unresolved expected theorem contract"
  names.forM fun name => auditTheorem name target

end Voting.Distortion.Audit

namespace Voting.Distortion.Audit

def stable_existsExpected : Prop :=
  ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Distortion.Profile n m) (law : Voting.Distortion.DrawLaw), ∃ lottery : Voting.Distortion.Lottery m, Voting.Distortion.Stable law profile lottery

def rank_cut_boundExpected : Prop :=
  ∀ (law : Voting.Distortion.DrawLaw) (witness : Voting.Distortion.CutWitness), Voting.Distortion.ValidCut law witness → ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Distortion.Profile n m) (lottery : Voting.Distortion.Lottery m), Voting.Distortion.Stable law profile lottery → Voting.Distortion.distortion profile lottery ≤ ENNReal.ofReal (1 + 2 * witness.C0)

def upperBoundExpected : Prop :=
  ∀ (law : Voting.Distortion.DrawLaw) (certificate : Voting.Distortion.UpperBoundCertificate law) {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Distortion.Profile n m) (lottery : Voting.Distortion.Lottery m), Voting.Distortion.Stable law profile lottery → Voting.Distortion.distortion profile lottery ≤ ENNReal.ofReal certificate.bound

def existsBoundedExpected : Prop :=
  ∀ (law : Voting.Distortion.DrawLaw) (certificate : Voting.Distortion.UpperBoundCertificate law) {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Distortion.Profile n m), ∃ lottery : Voting.Distortion.Lottery m, Voting.Distortion.Stable law profile lottery ∧ Voting.Distortion.distortion profile lottery ≤ ENNReal.ofReal certificate.bound

def approxCostExpected : Prop :=
  ∀ (law : Voting.Distortion.DrawLaw) (certificate : Voting.Distortion.UpperBoundCertificate law) (B : ℝ), Voting.Distortion.ApproximationCertificate certificate B → ∀ {n m : ℕ}, 0 < n → 0 < m → ∀ (profile : Voting.Distortion.Profile n m) (lottery : Voting.Distortion.Lottery m) (δ : ℝ), 0 ≤ δ → Voting.Distortion.ApproxStable law profile lottery δ → ∀ (metric : MetricDistortion.Metric n m), MetricDistortion.Consistent profile metric → ∀ (optimal : Fin m), MetricDistortion.Optimal metric optimal → MetricDistortion.expectedCost metric lottery ≤ certificate.bound * MetricDistortion.sc metric optimal + B * δ * sSup (Set.range fun c => MetricDistortion.distance metric (.inr optimal) (.inr c))

end Voting.Distortion.Audit

#distortion_audit MetricDistortion.Certified.Geometry_AverageAndDistortion : MetricDistortion.Contracts.Geometry_AverageAndDistortion.Statement
#distortion_audit MetricDistortion.Certified.Geometry_CommonCharge : MetricDistortion.Contracts.Geometry_CommonCharge.Statement
#distortion_audit MetricDistortion.Certified.Geometry_CrossingDiameter : MetricDistortion.Contracts.Geometry_CrossingDiameter.Statement
#distortion_audit MetricDistortion.Certified.Geometry_CrossingMeasure : MetricDistortion.Contracts.Geometry_CrossingMeasure.Statement
#distortion_audit MetricDistortion.Certified.Geometry_CutoffProperties : MetricDistortion.Contracts.Geometry_CutoffProperties.Statement
#distortion_audit MetricDistortion.Certified.Geometry_IntegratedLocalCut : MetricDistortion.Contracts.Geometry_IntegratedLocalCut.Statement
#distortion_audit MetricDistortion.Certified.Geometry_MetricRankCuts : MetricDistortion.Contracts.Geometry_MetricRankCuts.Statement
#distortion_audit MetricDistortion.Certified.Geometry_MetricTail : MetricDistortion.Contracts.Geometry_MetricTail.Statement
#distortion_audit MetricDistortion.Certified.Geometry_RankCutCriterion : MetricDistortion.Contracts.Geometry_RankCutCriterion.Statement
#distortion_audit MetricDistortion.Certified.Geometry_ThresholdStepFunctions : MetricDistortion.Contracts.Geometry_ThresholdStepFunctions.Statement
#distortion_audit MetricDistortion.Certified.Model_DistortionConventions : MetricDistortion.Contracts.Model_DistortionConventions.Statement
#distortion_audit MetricDistortion.Certified.Model_Metrics : MetricDistortion.Contracts.Model_Metrics.Statement
#distortion_audit MetricDistortion.Certified.Model_OffsetDefinitions : MetricDistortion.Contracts.Model_OffsetDefinitions.Statement
#distortion_audit MetricDistortion.Certified.Offsets_BipartiteExtension : MetricDistortion.Contracts.Offsets_BipartiteExtension.Statement
#distortion_audit MetricDistortion.Certified.Offsets_CrossDistanceProperties : MetricDistortion.Contracts.Offsets_CrossDistanceProperties.Statement
#distortion_audit MetricDistortion.Certified.Offsets_MetricDomination : MetricDistortion.Contracts.Offsets_MetricDomination.Statement
#distortion_audit MetricDistortion.Certified.Offsets_MetricRealization : MetricDistortion.Contracts.Offsets_MetricRealization.Statement
#distortion_audit MetricDistortion.Certified.Offsets_ReductionToOffsets : MetricDistortion.Contracts.Offsets_ReductionToOffsets.Statement
#distortion_audit Voting.Distortion.stable_exists : Voting.Distortion.Audit.stable_existsExpected
#distortion_audit Voting.Distortion.rank_cut_bound : Voting.Distortion.Audit.rank_cut_boundExpected
#distortion_audit Voting.Distortion.rank_cut_criterion : Voting.Distortion.RankCutCriterion
#distortion_audit Voting.Distortion.distortion_le_of_certificate : Voting.Distortion.Audit.upperBoundExpected
#distortion_audit Voting.Distortion.exists_stable_with_distortion_bound : Voting.Distortion.Audit.existsBoundedExpected
#distortion_audit Voting.Distortion.approx_cost_bound : Voting.Distortion.Audit.approxCostExpected
