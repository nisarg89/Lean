import FairDivision.Finite.SlotExpansion

/-!
# Fractional matrix for the square slot expansion

Each agent's real row mass is split equally among its `r` regular slots;
its remaining real mass uses the designated slot. Dummy mass is supported
only in designated slots. This module records the matrix and its elementary
nonnegativity and conservation identities.
-/

set_option autoImplicit false

namespace FairDivision

/-- Real item mass assigned to one agent in a fractional allocation. -/
def rowMass {n m : ℕ} (x : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ g : Fin m, x i g

theorem rowMass_nonneg {n m : ℕ} (x : Fin n → Fin m → ℝ)
    (hx : IsBalancedFractional x) (i : Fin n) :
    0 ≤ rowMass x i := by
  unfold rowMass
  exact Finset.sum_nonneg (fun g _ => hx.1 i g)

theorem rowMass_bounds {n m : ℕ} (x : Fin n → Fin m → ℝ)
    (hx : IsBalancedFractional x) (i : Fin n) :
    ((m / n : ℕ) : ℝ) ≤ rowMass x i ∧
      rowMass x i ≤ (slotsPerAgent n m : ℝ) := by
  simpa only [rowMass, slotsPerAgent, Nat.cast_add, Nat.cast_one]
    using hx.2.2 i

theorem rowMass_zero_item_zero {n m : ℕ} (x : Fin n → Fin m → ℝ)
    (hx : IsBalancedFractional x) (i : Fin n) (g : Fin m)
    (hzero : rowMass x i = 0) : x i g = 0 := by
  have hle : x i g ≤ rowMass x i := by
    unfold rowMass
    exact Finset.single_le_sum (fun h _ => hx.1 i h) (Finset.mem_univ g)
  rw [hzero] at hle
  exact le_antisymm hle (hx.1 i g)

/-- A regular slot exists only when the real row mass is positive. -/
theorem rowMass_pos_of_regular_slot {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) (k : Fin (m / n)) : 0 < rowMass x i := by
  have hr : 0 < m / n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hrR : (0 : ℝ) < ((m / n : ℕ) : ℝ) := by exact_mod_cast hr
  exact lt_of_lt_of_le hrR (rowMass_bounds x hx i).1

/-- The rectangular fractional allocation expanded to agent slots and
real/dummy columns. -/
noncomputable def expandedMatrix {n m : ℕ} (x : Fin n → Fin m → ℝ) :
    Matrix (AssignmentSlot n m) (AssignmentColumn n m) ℝ :=
  fun s c =>
    match s.2, c with
    | .inl _, .inl g => x s.1 g / rowMass x s.1
    | .inl _, .inr _ => 0
    | .inr _, .inl g =>
        ((rowMass x s.1 - ((m / n : ℕ) : ℝ)) / rowMass x s.1) * x s.1 g
    | .inr _, .inr _ =>
        ((slotsPerAgent n m : ℝ) - rowMass x s.1) /
          (dummyCount n m : ℝ)

/-- Every entry of the expanded matrix is nonnegative. -/
theorem expandedMatrix_nonneg {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (s : AssignmentSlot n m) (c : AssignmentColumn n m) :
    0 ≤ expandedMatrix x s c := by
  obtain ⟨i, slot⟩ := s
  cases slot with
  | inl k =>
    cases c with
    | inl g =>
      change 0 ≤ x i g / rowMass x i
      exact div_nonneg (hx.1 i g) (rowMass_nonneg x hx i)
    | inr d =>
      change 0 ≤ (0 : ℝ)
      norm_num
  | inr _ =>
    cases c with
    | inl g =>
      change 0 ≤ ((rowMass x i - ((m / n : ℕ) : ℝ)) /
        rowMass x i) * x i g
      exact mul_nonneg
        (div_nonneg (sub_nonneg.mpr (rowMass_bounds x hx i).1)
          (rowMass_nonneg x hx i)) (hx.1 i g)
    | inr d =>
      change 0 ≤ ((slotsPerAgent n m : ℝ) - rowMass x i) /
        (dummyCount n m : ℝ)
      have hd : (0 : ℝ) ≤ (dummyCount n m : ℝ) := by
        exact_mod_cast (dummyCount_pos (m := m) hn).le
      exact div_nonneg (sub_nonneg.mpr (rowMass_bounds x hx i).2) hd

/-- Across all slots of one agent, the contribution of one real item is
unchanged. The zero-mass case is handled without division by zero. -/
theorem expanded_real_factor_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) (g : Fin m) :
    ((m / n : ℕ) : ℝ) * (x i g / rowMass x i) +
      ((rowMass x i - ((m / n : ℕ) : ℝ)) / rowMass x i) *
        x i g = x i g := by
  by_cases hR : rowMass x i = 0
  · have hxg := rowMass_zero_item_zero x hx i g hR
    simp [hR, hxg]
  · field_simp [hR]
    ring

end FairDivision
