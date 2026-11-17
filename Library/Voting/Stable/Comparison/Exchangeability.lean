import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_Exchangeability

theorem from_children (h : Needs) : Statement := by
  intro m r P k
  have hb (c : Fin m) : P.val c*fixedCompare r P c k = ∫ u in block r P c, u^k := by
    rw [h.child_0 m r P c k]
    calc
      P.val c*(∫ s in (0 : ℝ)..1, (below r P c+s*P.val c)^k) =
          ∫ u in below r P c..(below r P c+P.val c), u^k := by
        simpa [mul_comm] using
          (intervalIntegral.mul_integral_comp_add_mul (f := fun u : ℝ => u^k)
            (a := 0) (b := 1) (P.val c) (below r P c))
      _ = ∫ u in block r P c, u^k := by
        unfold block
        rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (P.property.1 c)),
          integral_Ico_eq_integral_Ioc]
  have hparts := h.child_1 m r P
  have hi (c : Fin m) : IntegrableOn (fun u : ℝ => u^k) (block r P c) volume := by
    exact ((continuous_pow k).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
  calc
    (∑ c, P.val c*fixedCompare r P c k) = ∑ c, ∫ u in block r P c, u^k := by
      apply Finset.sum_congr rfl
      intro c _
      exact hb c
    _ = ∫ u in ⋃ c, block r P c, u^k :=
      (integral_iUnion_fintype (fun _ => measurableSet_Ico) hparts.2.1 hi).symm
    _ = ∫ u in Ico (0 : ℝ) 1, u^k := by rw [hparts.2.2.2]
    _ = ∫ u in (0 : ℝ)..1, u^k := by
      rw [intervalIntegral.integral_of_le zero_le_one,integral_Ico_eq_integral_Ioc]
    _ = 1/(k+1 : ℕ) := by rw [integral_pow]; simp

#print axioms from_children
end MetricDistortion.Contracts.Comparison_Exchangeability
