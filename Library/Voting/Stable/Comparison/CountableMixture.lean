import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_CountableMixture
theorem from_children (h : Needs) : Statement := by
  intro m D r P c
  unfold compare
  apply tsum_congr
  intro k
  rw [h.child_0 m r P c (k+1)]
#print axioms from_children
end MetricDistortion.Contracts.Comparison_CountableMixture
