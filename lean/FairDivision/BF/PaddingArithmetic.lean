import FairDivision.Definitions

/-!
# Arithmetic for BF's minimal dummy padding

The manuscript pads `m` real items to `nq` items where
`q = ceil(m/n)`. For `n > 0` the dummy count `nq-m` is strictly below `n`.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- Ceiling padding has enough positions for every real item and needs
fewer than one dummy per agent on average. -/
theorem upperSize_padding (n m : ℕ) (hn : 0 < n) :
    m ≤ n * FairDivision.upperSize n m ∧
      n * FairDivision.upperSize n m - m < n := by
  have hmod := Nat.mod_lt m hn
  have hdiv := Nat.mod_add_div m n
  by_cases hz : m % n = 0
  · have hq : FairDivision.upperSize n m = m / n := by
      simp [FairDivision.upperSize, hz]
    rw [hq]
    have hm : m = n * (m / n) := by omega
    constructor
    · omega
    · rw [← hm, Nat.sub_self]
      exact hn
  · have hq : FairDivision.upperSize n m = m / n + 1 := by
      simp [FairDivision.upperSize, hz]
    rw [hq]
    simp only [Nat.mul_add, mul_one]
    have hrem : 0 < m % n := Nat.pos_of_ne_zero hz
    constructor <;> omega


/-- The nontrivial padding branch has bundle size at least two. This is
exactly the arithmetic already used by the Section 3 finite conversion. -/
theorem upperSize_two_le_of_lt (n m : ℕ) (hn : 0<n) (hm : n< m) :
    2≤FairDivision.upperSize n m := by
  have hEnough: m≤n*FairDivision.upperSize n m := (upperSize_padding n m hn).1
  by_contra hNot
  have hSmall:FairDivision.upperSize n m=0 ∨FairDivision.upperSize n m=1:=by omega
  rcases hSmall with hZero|hOne
  ·simp [hZero] at hEnough
   omega
  ·simp [hOne] at hEnough
   omega

end FairDivision.BF
