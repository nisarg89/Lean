import EF1FPO.Contraction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Rational series used by the polynomial-time logarithm subroutine. -/

set_option autoImplicit false

namespace EF1FPO

def logSeries (a : ℚ) (terms : ℕ) : ℚ :=
  let x := (a - 1) / (a + 1)
  2 * ∑ i ∈ Finset.range terms, x ^ (2 * i + 1) / (2 * (i : ℚ) + 1)

theorem logSeries_error (a : ℚ) (terms : ℕ) (h₁ : 1 ≤ a) (h₂ : a ≤ 2) :
    |(logSeries a terms : ℝ) - Real.log (a : ℝ)| ≤ precisionError terms := by
  let r : ℝ := (a : ℝ)
  let x := (r - 1) / (r + 1)
  let total : ℝ := ∑ i ∈ Finset.range terms, x ^ (2 * i + 1) / ((2 : ℝ) * i + 1)
  have hLow : 1 ≤ r := by
    change (1 : ℝ) ≤ (a : ℝ)
    exact_mod_cast h₁
  have hHigh : r ≤ 2 := by
    change (a : ℝ) ≤ (2 : ℝ)
    exact_mod_cast h₂
  have hPlus : 0 < r + 1 := by linarith
  have hX : 0 ≤ x := div_nonneg (sub_nonneg.mpr hLow) hPlus.le
  have hThird : x ≤ (1 / 3 : ℝ) := (div_le_iff₀ hPlus).mpr (by linarith)
  have hAbs : |x| = x := abs_of_nonneg hX
  have hLt : |x| < 1 := by rw [hAbs]; linarith
  have hRatio : (1 + x) / (1 - x) = r := by
    apply (div_eq_iff (ne_of_gt (show 0 < 1 - x by linarith))).mpr
    dsimp [x]
    field_simp [hPlus.ne']
    ring
  have hCast : (logSeries a terms : ℝ) = 2 * total := by
    simp [logSeries, total, x, r]
  have hRaw := Real.sum_range_sub_log_div_le hLt terms
  rw [hRatio, hAbs] at hRaw
  have hTotalError : |1 / 2 * Real.log r - total| ≤ x ^ (2 * terms + 1) / (1 - x ^ 2) := by
    simpa only [total, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hRaw
  change |(logSeries a terms : ℝ) - Real.log r| ≤ precisionError terms
  rw [hCast, show 2 * total - Real.log r = -(2 * (1 / 2 * Real.log r - total)) by ring,
    abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  refine (mul_le_mul_of_nonneg_left hTotalError (by norm_num)).trans ?_
  have hSq : x ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hX hThird 2
  have hDenom : (2 / 3 : ℝ) ≤ 1 - x ^ 2 := by linarith
  have hPower : x ^ (2 * terms + 1) ≤ (1 / 2 : ℝ) ^ terms * (1 / 3) := by
    rw [pow_succ, pow_mul]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (show x ^ 2 ≤ (1 / 2 : ℝ) by linarith) terms)
      hThird hX (by positivity)
  rw [precisionError, ← inv_pow, ← one_div, ← mul_div_assoc]
  apply (div_le_iff₀ (show 0 < 1 - x ^ 2 by linarith)).mpr
  calc
    2 * x ^ (2 * terms + 1) ≤ 2 * ((1 / 2 : ℝ) ^ terms * (1 / 3)) :=
      mul_le_mul_of_nonneg_left hPower (by norm_num)
    _ = (1 / 2 : ℝ) ^ terms * (2 / 3) := by ring
    _ ≤ (1 / 2 : ℝ) ^ terms * (1 - x ^ 2) :=
      mul_le_mul_of_nonneg_left hDenom (by positivity)

end EF1FPO
