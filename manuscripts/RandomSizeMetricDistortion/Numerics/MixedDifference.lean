import RandomSizeMetricDistortion.Statements
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
namespace MetricDistortion.Contracts.Numerics_MixedDifference

private theorem power_mixed_nonneg (n : ℕ) (y h w : ℝ)
    (hy : 0 ≤ y) (hh : 0 ≤ h) (hw : 0 ≤ w) :
    0 ≤ (y+h+w)^n-(y+h)^n-(y+w)^n+y^n := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range n,
      ((y+h)^k-y^k)*w^(n-k)*(Nat.choose n k : ℝ) := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy (by linarith) k)) (pow_nonneg hw _))
      (Nat.cast_nonneg _)
  have heq : (y+h+w)^n-(y+h)^n-(y+w)^n+y^n =
      ∑ k ∈ Finset.range n, ((y+h)^k-y^k)*w^(n-k)*(Nat.choose n k : ℝ) := by
    calc
      _ = (∑ k ∈ Finset.range n, (y+h)^k*w^(n-k)*(Nat.choose n k : ℝ)) -
          ∑ k ∈ Finset.range n, y^k*w^(n-k)*(Nat.choose n k : ℝ) := by
        rw [add_pow (y+h) w n,add_pow y w n,Finset.sum_range_succ,Finset.sum_range_succ]
        simp only [Nat.sub_self,Nat.choose_self,Nat.cast_one,pow_zero,mul_one]
        ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [heq]
  exact hsum

theorem from_children (h : Needs) : Statement := by
  intro y a w hy ha hw
  have h2 := power_mixed_nonneg 2 y a w hy ha hw
  have h3 := power_mixed_nonneg 3 y a w hy ha hw
  have h33 := power_mixed_nonneg 33 y a w hy ha hw
  have hp := add_nonneg
    (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 19/146) h2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 35/438) h3))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/66) h33)
  convert hp using 1 <;> unfold HStar PhiStar <;> ring

#print axioms from_children
end MetricDistortion.Contracts.Numerics_MixedDifference
