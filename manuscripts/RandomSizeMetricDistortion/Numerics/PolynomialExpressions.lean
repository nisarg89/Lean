import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_PolynomialExpressions

theorem proved : Statement := by
  intro e
  induction e with
  | const q => intro x; rfl
  | var i => intro x; rfl
  | add a b ha hb =>
    intro x
    simp [eval, qEval, ha, hb]
  | mul a b ha hb =>
    intro x
    simp [eval, qEval, ha, hb]
  | neg a ha =>
    intro x
    simp [eval, qEval, ha]
#print axioms proved
end MetricDistortion.Contracts.Numerics_PolynomialExpressions
