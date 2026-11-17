import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_RationalBernstein

theorem proved : Statement := by
  intro n a ha t ht
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (ha k) (Nat.cast_nonneg _)) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)
#print axioms proved
end MetricDistortion.Contracts.Numerics_RationalBernstein
