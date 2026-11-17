import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Analysis_DrawSummability
theorem from_children (h : Needs) : Statement := by
  intro D t ht
  have hw : ∀ k, 0 ≤ drawWeight D k := (h.child_0 D).1
  have hbounds : ∀ k, drawWeight D k*t^(k+1) ∈ Icc (0 : ℝ) (drawWeight D k) := by
    intro k
    exact ⟨mul_nonneg (hw k) (pow_nonneg ht.1 _),
      mul_le_of_le_one_right (hw k) (pow_le_one₀ ht.1 ht.2)⟩
  refine ⟨Summable.of_nonneg_of_le (fun k => (hbounds k).1)
    (fun k => (hbounds k).2) (h.child_0 D).2.summable,hbounds⟩
#print axioms from_children
end MetricDistortion.Contracts.Analysis_DrawSummability
