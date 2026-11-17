import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Numerics_DerivativeBounds

theorem from_children (h : Needs) : Statement := by
  intro e i x
  induction e with
  | const q => simpa [eval,derivative] using hasDerivAt_const (x i) (q : ℝ)
  | var j =>
    by_cases hij : i = j
    · subst j
      have hid := hasDerivAt_id (x i)
      rw [hasDerivAt_iff_isLittleO] at hid ⊢
      simpa [eval,derivative,smul_eq_mul] using hid
    · have hji : j ≠ i := Ne.symm hij
      simpa [eval,derivative,hij,hji] using hasDerivAt_const (x i) (x j)
  | add a b ha hb =>
    have hd := ha.add hb
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa [eval,derivative,smul_eq_mul] using hd
  | mul a b ha hb =>
    have hd := ha.mul hb
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa [eval,derivative,Function.update_eq_self,smul_eq_mul] using hd
  | neg a ha =>
    have hd := ha.neg
    rw [hasDerivAt_iff_isLittleO] at hd ⊢
    simpa [eval,derivative,smul_eq_mul] using hd
#print axioms from_children
end MetricDistortion.Contracts.Numerics_DerivativeBounds
