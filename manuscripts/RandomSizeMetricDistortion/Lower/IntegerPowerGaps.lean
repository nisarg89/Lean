import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_IntegerPowerGaps

private def A (d : ℕ) : ℝ := (7/26)*((7/26 : ℝ)/(3/4 : ℝ))^d
private def B (d : ℕ) : ℝ := (71/125-7/26)*(d+1)*((71/125 : ℝ)/(3/4 : ℝ))^d

theorem from_children (h : Needs) : Statement := by
  have hstep (d : ℕ) (hd : 3 ≤ d) : A (d+1)+B (d+1) ≤ A d+B d := by
    obtain ⟨ha,hb⟩ := h.child_0 d hd
    have hb' := mul_le_mul_of_nonneg_left hb.le (by norm_num : (0 : ℝ) ≤ 71/125-7/26)
    dsimp [A,B]
    push_cast at hb' ⊢
    nlinarith
  have hbound : ∀ d, 3 ≤ d → A d+B d ≤ A 3+B 3 := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => exact le_rfl
    | succ d hd ih => exact (hstep d hd).trans ih
  have hmain : ∀ d : ℕ, 0 < d → 0 < lowerGap d := by
    intro d hd
    by_cases hd3 : 3 ≤ d
    · have hnorm : A d+B d < (71/125 : ℝ)-1/52 :=
        (hbound d hd3).trans_lt (by norm_num [A,B])
      have hpow : (0 : ℝ) < (3/4 : ℝ)^d := by positivity
      have ha : ((7/26 : ℝ)/(3/4 : ℝ))^d*(3/4 : ℝ)^d = (7/26 : ℝ)^d := by
        rw [← mul_pow]
        congr 1
        norm_num
      have hb : ((71/125 : ℝ)/(3/4 : ℝ))^d*(3/4 : ℝ)^d = (71/125 : ℝ)^d := by
        rw [← mul_pow]
        congr 1
        norm_num
      have hA : A d*(3/4 : ℝ)^d = (7/26 : ℝ)^(d+1) := by
        dsimp [A]
        rw [mul_assoc,ha,pow_succ]
        ring
      have hB : B d*(3/4 : ℝ)^d = ((71/125 : ℝ)-7/26)*(d+1)*(71/125 : ℝ)^d := by
        dsimp [B]
        calc
          _ = ((71/125 : ℝ)-7/26)*(d+1)*
            (((71/125 : ℝ)/(3/4 : ℝ))^d*(3/4 : ℝ)^d) := by ring
          _ = _ := by rw [hb]
      have hh := mul_lt_mul_of_pos_right hnorm hpow
      rw [add_mul,hA,hB] at hh
      have hapos : (0 : ℝ) < (1/52 : ℝ)^(d+1) := by positivity
      dsimp [lowerGap]
      linarith
    · have he : d = 1 ∨ d = 2 := by omega
      rcases he with rfl | rfl <;> norm_num [lowerGap]
  refine ⟨hmain, ?_, ?_, ?_⟩ <;> norm_num [lowerGap]

#print axioms from_children
end MetricDistortion.Contracts.Lower_IntegerPowerGaps
