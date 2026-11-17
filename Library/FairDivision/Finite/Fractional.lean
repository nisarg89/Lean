import FairDivision.Definitions

/-! Bridges between integral allocations and the balanced fractional polytope. -/

set_option autoImplicit false

namespace FairDivision

/-- The indicator matrix of an integral allocation. -/
def integralFractional {n m : ℕ} (A : Allocation n m) (i : Fin n)
    (g : Fin m) : ℝ := if A g = i then 1 else 0

@[simp] theorem integralFractional_nonneg {n m : ℕ}
    (A : Allocation n m) (i : Fin n) (g : Fin m) :
    0 ≤ integralFractional A i g := by
  unfold integralFractional
  split_ifs <;> norm_num

@[simp] theorem integralFractional_column {n m : ℕ}
    (A : Allocation n m) (g : Fin m) :
    ∑ i : Fin n, integralFractional A i g = 1 := by
  simp [integralFractional]

@[simp] theorem integralFractional_row {n m : ℕ}
    (A : Allocation n m) (i : Fin n) :
    ∑ g : Fin m, integralFractional A i g = (bundle A i).card := by
  simp [integralFractional, bundle]

/-- An integral balanced allocation is feasible in the fractional polytope. -/
theorem balanced_integral_fractional {n m : ℕ} (A : Allocation n m)
    (hA : IsBalanced A) : IsBalancedFractional (integralFractional A) := by
  refine ⟨integralFractional_nonneg A, integralFractional_column A, ?_⟩
  intro i
  rw [integralFractional_row]
  rcases hA i with hcard | hcard
  · have hcardR : ((bundle A i).card : ℝ) = ((m / n : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [hcardR]
    constructor <;> linarith
  · have hlo : m / n ≤ upperSize n m := by
      simp only [upperSize]
      split_ifs <;> omega
    have hhi : upperSize n m ≤ m / n + 1 := by
      simp only [upperSize]
      split_ifs <;> omega
    have hcardR : ((bundle A i).card : ℝ) = (upperSize n m : ℝ) := by
      exact_mod_cast hcard
    rw [hcardR]
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi

/-- The indicator matrix gives exactly the original additive utility. -/
@[simp] theorem fractionalValue_integral {n m : ℕ}
    (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i : Fin n) :
    fractionalValue v (integralFractional A) i =
      additiveValue v i (bundle A i) := by
  simp [fractionalValue, integralFractional, additiveValue, bundle, Finset.sum_filter]

end FairDivision
