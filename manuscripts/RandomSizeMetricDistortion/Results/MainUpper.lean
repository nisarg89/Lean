import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Results_MainUpper
theorem from_children (h : Needs) : Statement := by
  classical
  obtain ⟨D, hD⟩ := h.child_1.1
  let R : VotingRule := fun n m hn hm σ => Classical.choose (h.child_0.1 n m hn hm σ D)
  refine ⟨R, ?_⟩
  intro n m hn hm σ
  exact h.child_2 D hD n m hn hm σ _ (Classical.choose_spec (h.child_0.1 n m hn hm σ D))
#print axioms from_children
end MetricDistortion.Contracts.Results_MainUpper
