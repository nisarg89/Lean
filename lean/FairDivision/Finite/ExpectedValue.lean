import FairDivision.Definitions

/-!
# Values on either side of a finite lottery mean

The conversion from an equitable compatible lottery begins by finding, at
each position, supported bundle values bracketing the common expectation.
This is a finite weighted-average fact and does not require topology.
-/

set_option autoImplicit false

namespace FairDivision

/-- A nonnegative finite probability vector with total mass one gives
positive mass to some point of its indexing set. -/
theorem exists_positive_weight {α : Type*}
    (S : Finset α) (p : α → ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1) :
    ∃ x ∈ S, 0 < p x := by
  by_contra h
  have hpzero : ∀ x ∈ S, p x = 0 := by
    intro x hx
    have hnot : ¬ 0 < p x := by
      intro hpos
      exact h ⟨x, hx, hpos⟩
    exact le_antisymm (le_of_not_gt hnot) (hp x hx)
  have hzero : ∑ x ∈ S, p x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hpzero x hx
  linarith

/-- The common expectation of a finite lottery lies between two supported
values, even when the values have no order structure beyond the real order. -/
theorem weighted_average_brackets {α : Type*}
    (S : Finset α) (p v : α → ℝ) (t : ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1)
    (hmean : ∑ x ∈ S, p x * v x = t) :
    (∃ x ∈ S, v x ≤ t) ∧ (∃ x ∈ S, t ≤ v x) := by
  obtain ⟨xpos, hxpos, hpos⟩ := exists_positive_weight S p hp hsum
  have hconstant : ∑ x ∈ S, p x * t = t := by
    rw [← Finset.sum_mul, hsum, one_mul]
  constructor
  · by_contra hlow
    have hgt : ∀ x ∈ S, t < v x := by
      intro x hx
      exact lt_of_not_ge (fun hle => hlow ⟨x, hx, hle⟩)
    have hlt : (∑ x ∈ S, p x * t) < ∑ x ∈ S, p x * v x := by
      apply Finset.sum_lt_sum
      · intro x hx
        exact mul_le_mul_of_nonneg_left (le_of_lt (hgt x hx)) (hp x hx)
      · exact ⟨xpos, hxpos, mul_lt_mul_of_pos_left (hgt xpos hxpos) hpos⟩
    linarith
  · by_contra hhigh
    have hlt : ∀ x ∈ S, v x < t := by
      intro x hx
      exact lt_of_not_ge (fun hle => hhigh ⟨x, hx, hle⟩)
    have hsumlt : (∑ x ∈ S, p x * v x) < ∑ x ∈ S, p x * t := by
      apply Finset.sum_lt_sum
      · intro x hx
        exact mul_le_mul_of_nonneg_left (le_of_lt (hlt x hx)) (hp x hx)
      · exact ⟨xpos, hxpos, mul_lt_mul_of_pos_left (hlt xpos hxpos) hpos⟩
    linarith

/-- Some positive-probability outcome attains at least the mean. -/
theorem weighted_average_exists_ge_pos {α : Type*}
    (S : Finset α) (p v : α → ℝ) (t : ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1)
    (hmean : ∑ x ∈ S, p x * v x = t) :
    ∃ x ∈ S, 0 < p x ∧ t ≤ v x := by
  obtain ⟨xpos, hxpos, hpos⟩ := exists_positive_weight S p hp hsum
  by_contra h
  have hconstant : ∑ x ∈ S, p x * t = t := by
    rw [← Finset.sum_mul, hsum, one_mul]
  have hle (x : α) (hx : x ∈ S) : p x * v x ≤ p x * t := by
    by_cases hpx : p x = 0
    · simp [hpx]
    · have hlt : v x < t := lt_of_not_ge (by
        intro ht
        exact h ⟨x, hx, lt_of_le_of_ne (hp x hx) (Ne.symm hpx), ht⟩)
      exact mul_le_mul_of_nonneg_left hlt.le (hp x hx)
  have hstrict : p xpos * v xpos < p xpos * t := by
    have hlt : v xpos < t := lt_of_not_ge (by
      intro ht
      exact h ⟨xpos, hxpos, hpos, ht⟩)
    exact mul_lt_mul_of_pos_left hlt hpos
  have hsumlt : (∑ x ∈ S, p x * v x) < ∑ x ∈ S, p x * t := by
    apply Finset.sum_lt_sum
    · intro x hx
      exact hle x hx
    · exact ⟨xpos, hxpos, hstrict⟩
  linarith

end FairDivision
