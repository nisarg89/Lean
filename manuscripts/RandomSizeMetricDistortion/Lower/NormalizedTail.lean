import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_NormalizedTail

theorem proved : Statement := by
  intro d hd
  constructor
  · rw [pow_succ]
    have hnonneg : 0 ≤ (7/26 : ℝ)*((7/26 : ℝ)/(3/4 : ℝ))^d := by positivity
    nlinarith
  · rw [pow_succ]
    have hp : 0 < ((71/125 : ℝ)/(3/4 : ℝ))^d := by positivity
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hcoeff : ((d+2 : ℕ) : ℝ)*((71/125 : ℝ)/(3/4 : ℝ)) < ((d+1 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    nlinarith

#print axioms proved
end MetricDistortion.Contracts.Lower_NormalizedTail
