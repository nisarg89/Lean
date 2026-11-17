import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_FactorIdentities

theorem from_children (h : Needs) : Statement := by
  constructor
  · intro x
    rfl
  · intro j a p A r
    unfold internalResidual firstResidual
    ring
#print axioms from_children
end MetricDistortion.Contracts.Numerics_FactorIdentities
