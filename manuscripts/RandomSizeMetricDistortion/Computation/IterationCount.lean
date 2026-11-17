import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_IterationCount
theorem proved : Statement := by
  intro m hm δ hδ
  let N := Nat.ceil (Real.log m/(2*δ^2))
  have hmR : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlog : 0 < Real.log m := Real.log_pos hmR
  have hden : 0 < 2*δ^2 := by positivity
  have hx : 0 < Real.log m/(2*δ^2) := div_pos hlog hden
  have hN : 0 < N := Nat.ceil_pos.mpr hx
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hceil : Real.log m/(2*δ^2) ≤ (N : ℝ) := Nat.le_ceil _
  have hbound : Real.log m ≤ 2*δ^2*N := by
    have := (div_le_iff₀ hden).mp hceil
    nlinarith
  refine ⟨hN, ?_, le_of_lt (Nat.ceil_lt_add_one (le_of_lt hx))⟩
  have hterm : Real.log m/(4*δ*N) ≤ δ/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*δ*N)).2
    nlinarith
  linarith
#print axioms proved
end MetricDistortion.Contracts.Computation_IterationCount
