import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_SelfPlay

private lemma fixed_bounds {m : ℕ} (r : Ranking m) (P : Lottery m) (c : Fin m) (k : ℕ) :
    fixedCompare r P c k ∈ Icc (0 : ℝ) 1 := by
  have hn (xs : Fin k → Fin m) : 0 ≤ ∏ i, P.val (xs i) :=
    Finset.prod_nonneg fun i _ => P.property.1 (xs i)
  have hratio (xs : Fin k → Fin m) :
      (if ∀ i, r (xs i) ≤ r c then
        (1 : ℝ)/(1+((Finset.univ.filter fun i => xs i=c).card : ℝ)) else 0) ∈ Icc (0 : ℝ) 1 := by
    split_ifs
    · constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · constructor <;> norm_num
  constructor
  · exact Finset.sum_nonneg fun xs _ => mul_nonneg (hn xs) (hratio xs).1
  · calc
      fixedCompare r P c k ≤ ∑ xs : Fin k → Fin m, ∏ i, P.val (xs i) :=
        Finset.sum_le_sum fun xs _ => mul_le_of_le_one_right (hn xs) (hratio xs).2
      _ = (∑ j, P.val j)^k := (Fintype.sum_pow P.val k).symm
      _ = 1 := by rw [P.property.2,one_pow]

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ P
  have hweights : Summable (drawWeight D) := ENNReal.summable_toReal D.tsum_coe_ne_top
  have hseries (v : Fin n) (c : Fin m) :
      Summable (fun k => drawWeight D k*fixedCompare (σ v) P c (k+1)) := by
    apply Summable.of_nonneg_of_le _ _ hweights
    · intro k
      exact mul_nonneg ENNReal.toReal_nonneg (fixed_bounds (σ v) P c (k+1)).1
    · intro k
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (fixed_bounds (σ v) P c (k+1)).2
  have hsum (v : Fin n) : (∑ c, P.val c*compare D (σ v) P c) = mu D := by
    calc
      (∑ c, P.val c*compare D (σ v) P c) =
        ∑ c, ∑' k, P.val c*(drawWeight D k*fixedCompare (σ v) P c (k+1)) := by
          simp_rw [compare,tsum_mul_left]
      _ = ∑' k, ∑ c, P.val c*(drawWeight D k*fixedCompare (σ v) P c (k+1)) :=
        (Summable.tsum_finsetSum (fun c _ => (hseries v c).mul_left (P.val c))).symm
      _ = ∑' k, drawWeight D k/(k+2 : ℕ) := by
        apply tsum_congr
        intro k
        calc
          (∑ c, P.val c*(drawWeight D k*fixedCompare (σ v) P c (k+1))) =
            drawWeight D k*(∑ c, P.val c*fixedCompare (σ v) P c (k+1)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c _
              ring
          _ = drawWeight D k/(k+2 : ℕ) := by
            rw [h.child_0 m (σ v) P (k+1)]
            simp [div_eq_mul_inv,add_assoc]
      _ = mu D := rfl
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  calc
    payoff D σ P P = (∑ v, ∑ c, P.val c*compare D (σ v) P c)/(n : ℝ) := by
      unfold payoff score avg
      simp_rw [← mul_div_assoc,Finset.mul_sum]
      rw [← Finset.sum_div,Finset.sum_comm]
    _ = mu D := by
      simp_rw [hsum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

#print axioms from_children
end MetricDistortion.Contracts.Comparison_SelfPlay
