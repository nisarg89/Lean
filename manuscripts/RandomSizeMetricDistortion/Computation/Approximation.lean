import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_Approximation
theorem from_children (h : Needs) : Statement := by
  obtain ⟨prog, himplements, hcost⟩ := h.child_0
  exact ⟨prog, h.child_2 prog himplements hcost (h.child_1 prog himplements)⟩
#print axioms from_children
end MetricDistortion.Contracts.Computation_Approximation
