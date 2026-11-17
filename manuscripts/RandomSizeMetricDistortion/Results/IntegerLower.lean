import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Results_IntegerLower
theorem from_children (h : Needs) : Statement := by
  intro D
  by_cases hd : phi D (71/125) < mu D
  · obtain ⟨z, hz, hz1, bound⟩ := h.child_0 D hd
    obtain ⟨n, hn, σ, hσ⟩ := h.child_3 125 71 (by norm_num) (by norm_num) z hz hz1
    exact ⟨n, 126, hn, by norm_num, by norm_num, σ, bound n hn σ hσ⟩
  · obtain ⟨z, hz, hz1, bound⟩ := h.child_1 D (le_of_not_gt hd)
    obtain ⟨n, hn, σ, hσ⟩ := h.child_3 39 1 (by norm_num) (by norm_num) z hz hz1
    exact ⟨n, 40, hn, by norm_num, by norm_num, σ, bound n hn σ hσ⟩
#print axioms from_children
end MetricDistortion.Contracts.Results_IntegerLower
