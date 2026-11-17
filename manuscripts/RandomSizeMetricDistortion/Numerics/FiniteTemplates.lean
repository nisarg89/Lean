import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_FiniteTemplates

theorem from_children (h : Needs) : Statement := by
  intro j a p A r ha hap hpA hAr hr
  unfold internalResidual HStar psiStar
  ring
#print axioms from_children
end MetricDistortion.Contracts.Numerics_FiniteTemplates
