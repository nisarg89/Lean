import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_ShiftedCoefficients

theorem proved : Statement := by
  intro e he x hx
  rw [Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by change (0 : ℝ) ≤ (e.coeff i : ℝ); exact_mod_cast he i) (pow_nonneg hx i)
#print axioms proved
end MetricDistortion.Contracts.Numerics_ShiftedCoefficients
