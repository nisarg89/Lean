import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_MaximalLottery

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ P
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hmu : mu (PMF.pure 0) = (1/2 : ℝ) := by
    unfold mu
    refine (tsum_eq_single 0 ?_).trans ?_
    · intro i hi
      simp [drawWeight,PMF.pure_apply,hi]
    · norm_num [drawWeight,PMF.pure_apply]
  have hfixed (v : Fin n) (c : Fin m) :
      fixedCompare (σ v) P c 1 = below (σ v) P c+P.val c/2 := by
    rw [h.child_1 m (σ v) P c 1]
    simp only [pow_one]
    have hi : IntervalIntegrable (fun s : ℝ => s*P.val c) volume 0 1 := by
      simpa only [id_eq] using ((continuous_id.mul_const (P.val c)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_add intervalIntegrable_const hi]
    simp [intervalIntegral.integral_mul_const,integral_id,smul_eq_mul]
    ring
  have hscore (c : Fin m) : score (PMF.pure 0) σ P c = avg (fun v => below (σ v) P c)+P.val c/2 := by
    rw [h.child_0 n m σ P c 0]
    simp only [Nat.zero_add,hfixed]
    unfold avg
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  change (∀ c, score (PMF.pure 0) σ P c ≤ mu (PMF.pure 0)) ↔ _
  simp only [hscore,hmu]

#print axioms from_children
end MetricDistortion.Contracts.Comparison_MaximalLottery
