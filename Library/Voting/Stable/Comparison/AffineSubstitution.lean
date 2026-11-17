import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_AffineSubstitution
theorem from_children (h : Needs) : Statement := by
  intro D b z hb hz hsum
  simpa [mul_comm,smul_eq_mul,div_eq_mul_inv] using
    (intervalIntegral.integral_comp_add_mul (phi D) (a := 0) (b := 1)
      (c := z) (ne_of_gt hz) b)
#print axioms from_children
end MetricDistortion.Contracts.Comparison_AffineSubstitution
