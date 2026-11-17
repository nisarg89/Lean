import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_PowerIntegral
theorem proved : Statement := by
  intro k
  rw [integral_pow]
  simp
#print axioms proved
end MetricDistortion.Contracts.Comparison_PowerIntegral
