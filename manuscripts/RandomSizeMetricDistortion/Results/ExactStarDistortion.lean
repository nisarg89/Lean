import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Results_ExactStarDistortion
theorem from_children (h : Needs) : Statement := by
  intro D hD n m hn hm σ P hP
  have hv : ValidCut D fixedWitness := h.child_1.2.1 D hD
  have hd := (h.child_0 D fixedWitness hv).1 n m hn hm σ P hP
  convert hd using 1 <;> norm_num [fixedWitness, cStar]
#print axioms from_children
end MetricDistortion.Contracts.Results_ExactStarDistortion
