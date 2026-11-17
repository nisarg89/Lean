import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_FixedDrawSpecialization
theorem from_children (h : Needs) : Statement := by
  intro n m σ P c k
  unfold score
  congr 1
  funext v
  unfold compare
  refine (tsum_eq_single k ?_).trans ?_
  · intro i hi
    simp [drawWeight,PMF.pure_apply,hi]
  · simp [drawWeight,PMF.pure_apply]
#print axioms from_children
end MetricDistortion.Contracts.Comparison_FixedDrawSpecialization
