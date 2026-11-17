import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Offsets_MetricRealization

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ x hx o hxo
  let w := fun v c => deltaOffset (σ v) x/2+sOffset (σ v) x c
  obtain ⟨hwn,hwt,hwp⟩ := h.child_1 n m σ x hx
  obtain ⟨d,hd⟩ := h.child_0 n m hn hm w hwn hwt
  have hs0 (v : Fin n) : sOffset (σ v) x o = 0 := by
    have hs := (h.child_2 m (σ v) x hx).1 o
    exact le_antisymm (hxo ▸ hs.2) hs.1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hbase : sc d o = scale σ x/2 := by
    unfold sc scale avg
    simp_rw [hd]
    dsimp [w]
    simp_rw [hs0,add_zero]
    rw [← Finset.sum_div]
    ring
  have hdiff (c : Fin m) : sc d c-sc d o = avg (fun v => sOffset (σ v) x c) := by
    unfold sc avg
    simp_rw [hd]
    dsimp [w]
    simp_rw [hs0,add_zero]
    rw [Finset.sum_add_distrib]
    ring
  have hopt : Optimal d o := by
    intro c
    have hsnon : 0 ≤ avg (fun v => sOffset (σ v) x c) := by
      exact div_nonneg (Finset.sum_nonneg fun v _ => ((h.child_2 m (σ v) x hx).1 c).1)
        (Nat.cast_nonneg _)
    linarith [hdiff c]
  refine ⟨d, ?_, hopt, hbase, hdiff, ?_⟩
  · intro v a b hab
    rw [hd,hd]
    exact hwp v a b hab
  · intro P
    have hcost : expectedCost d P = sc d o+loss σ P x := by
      have hc (c : Fin m) : sc d c = sc d o+avg (fun v => sOffset (σ v) x c) := by
        linarith [hdiff c]
      unfold expectedCost
      have hexp : (∑ c, P.val c*sc d c) =
          ∑ c, P.val c*(sc d o+avg (fun v => sOffset (σ v) x c)) := by
        apply Finset.sum_congr rfl
        intro c hc'
        exact congrArg (fun t => P.val c*t) (hc c)
      rw [hexp]
      simp_rw [mul_add,Finset.sum_add_distrib]
      rw [← Finset.sum_mul,P.property.2,one_mul]
      congr 1
      unfold loss avg
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have hL : 0 ≤ loss σ P x := by
      unfold loss avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun c _ =>
        mul_nonneg (P.property.1 c) (((h.child_2 m (σ v) x hx).1 c).1)) (Nat.cast_nonneg _)
    have hS : 0 ≤ scale σ x := by
      unfold scale avg
      exact div_nonneg (Finset.sum_nonneg fun v _ => (h.child_2 m (σ v) x hx).2)
        (Nat.cast_nonneg _)
    rw [hcost,hbase]
    by_cases hzero : scale σ x = 0
    · by_cases hLzero : loss σ P x = 0
      · simp [ratio,offsetRatio,hzero,hLzero]
      · simp [ratio,offsetRatio,hzero,hLzero]
    · have hbase0 : scale σ x/2 ≠ 0 := div_ne_zero hzero (by norm_num)
      have hreal : (scale σ x/2+loss σ P x)/(scale σ x/2) = 1+2*(loss σ P x/scale σ x) := by
        field_simp
        <;> ring
      simp only [ratio,offsetRatio,if_neg hbase0,if_neg hzero]
      rw [hreal,ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg (by norm_num) (div_nonneg hL hS)),ENNReal.ofReal_mul (by norm_num)]
      norm_num

#print axioms from_children
end MetricDistortion.Contracts.Offsets_MetricRealization
