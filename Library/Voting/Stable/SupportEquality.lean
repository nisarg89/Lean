import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Stability_SupportEquality
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ P hP c hc
  have hz : (∑ b, P.val b*(mu D-score D σ P b)) = 0 := by
    calc
      _ = mu D*(∑ b, P.val b)-payoff D σ P P := by
        simp only [payoff, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = 0 := by rw [P.property.2, h.child_0 n m hn hm D σ P]; ring
  have hnon (b : Fin m) (_ : b ∈ Finset.univ) : 0 ≤ P.val b*(mu D-score D σ P b) :=
    mul_nonneg (P.property.1 b) (sub_nonneg.mpr (hP b))
  have hc0 := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hz c (Finset.mem_univ c)
  have hdiff := (mul_eq_zero.mp hc0).resolve_left (ne_of_gt hc)
  linarith
#print axioms from_children
end MetricDistortion.Contracts.Stability_SupportEquality
