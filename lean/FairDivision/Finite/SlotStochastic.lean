import FairDivision.Finite.SlotMatrix
import Mathlib.Algebra.BigOperators.Field

/-!
# Stochasticity of the square slot expansion

The expanded matrix has unit row and column sums. These are the conservation
facts needed to invoke Birkhoff's theorem after reindexing the columns.
-/

set_option autoImplicit false

namespace FairDivision

/-- Every regular slot has one unit of real-item mass and no dummy mass. -/
theorem expanded_regular_row_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) (k : Fin (m / n)) :
    (∑ c : AssignmentColumn n m,
      expandedMatrix x (i, .inl k) c) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [expandedMatrix, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_div]
  change rowMass x i / rowMass x i = 1
  exact div_self (ne_of_gt (rowMass_pos_of_regular_slot x hx i k))

/-- The designated slot receives precisely the row mass left after
filling the regular slots. -/
theorem expanded_designated_real_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) :
    (∑ g : Fin m,
      ((rowMass x i - ((m / n : ℕ) : ℝ)) / rowMass x i) * x i g) =
      rowMass x i - ((m / n : ℕ) : ℝ) := by
  by_cases hR : rowMass x i = 0
  · have hr0 : ((m / n : ℕ) : ℝ) = 0 := by
      have hlo := (rowMass_bounds x hx i).1
      rw [hR] at hlo
      exact le_antisymm hlo (Nat.cast_nonneg _)
    simp [hR, hr0]
  · rw [← Finset.mul_sum]
    change ((rowMass x i - ((m / n : ℕ) : ℝ)) /
      rowMass x i) * rowMass x i = _
    field_simp [hR]

/-- The dummy columns collectively fill the unoccupied designated-slot mass. -/
theorem expanded_designated_dummy_sum {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (i : Fin n) :
    (∑ d : Fin (dummyCount n m),
      ((slotsPerAgent n m : ℝ) - rowMass x i) /
        (dummyCount n m : ℝ)) =
      (slotsPerAgent n m : ℝ) - rowMass x i := by
  have hd : (dummyCount n m : ℝ) ≠ 0 := by
    exact_mod_cast (dummyCount_pos (m := m) hn).ne'
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  field_simp [hd]

/-- The designated slot also has total mass one. -/
theorem expanded_designated_row_sum {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) :
    (∑ c : AssignmentColumn n m,
      expandedMatrix x (i, .inr ()) c) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [expandedMatrix]
  rw [expanded_designated_real_sum x hx i,
    expanded_designated_dummy_sum hn x i]
  simp only [slotsPerAgent, Nat.cast_add, Nat.cast_one]
  ring

/-- Across one agent's slots, each real item retains its original
fractional assignment. -/
theorem expanded_real_agent_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (i : Fin n) (g : Fin m) :
    (∑ slot : Fin (m / n) ⊕ Unit,
      expandedMatrix x (i, slot) (.inl g)) = x i g := by
  rw [Fintype.sum_sum_type]
  simp only [expandedMatrix, Finset.sum_const, Fintype.card_fin,
    Finset.card_univ, Fintype.card_unit, nsmul_eq_mul, Nat.cast_one,
    one_mul]
  exact expanded_real_factor_sum x hx i g

/-- Every real item column of the expanded matrix sums to one. -/
theorem expanded_real_column_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (g : Fin m) :
    (∑ s : AssignmentSlot n m, expandedMatrix x s (.inl g)) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [expanded_real_agent_sum x hx]
  exact hx.2.1 g

/-- Summing all agent row masses counts each real item once. -/
theorem total_rowMass {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x) :
    (∑ i : Fin n, rowMass x i) = (m : ℝ) := by
  calc
    (∑ i : Fin n, rowMass x i) =
        ∑ g : Fin m, ∑ i : Fin n, x i g := by
      simp only [rowMass]
      exact Finset.sum_comm
    _ = ∑ g : Fin m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro g _
      exact hx.2.1 g
    _ = (m : ℝ) := by simp

/-- For one agent, a dummy column is present only in its designated slot. -/
theorem expanded_dummy_agent_sum {n m : ℕ}
    (x : Fin n → Fin m → ℝ) (i : Fin n)
    (d : Fin (dummyCount n m)) :
    (∑ slot : Fin (m / n) ⊕ Unit,
      expandedMatrix x (i, slot) (.inr d)) =
      ((slotsPerAgent n m : ℝ) - rowMass x i) /
        (dummyCount n m : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp [expandedMatrix]

/-- Every dummy column of the expanded matrix sums to one. -/
theorem expanded_dummy_column_sum {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (d : Fin (dummyCount n m)) :
    (∑ s : AssignmentSlot n m, expandedMatrix x s (.inr d)) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [expanded_dummy_agent_sum]
  rw [← Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, total_rowMass x hx]
  have hd : (dummyCount n m : ℝ) ≠ 0 := by
    exact_mod_cast (dummyCount_pos (m := m) hn).ne'
  have hcast : (dummyCount n m : ℝ) =
      (n : ℝ) * (slotsPerAgent n m : ℝ) - (m : ℝ) := by
    unfold dummyCount
    rw [Nat.cast_sub (Nat.le_of_lt (items_lt_slot_count (m := m) hn)),
      Nat.cast_mul]
  rw [← hcast]
  exact div_self hd

/-- Every row of the expanded matrix sums to one. -/
theorem expanded_row_sum {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (s : AssignmentSlot n m) :
    (∑ c : AssignmentColumn n m, expandedMatrix x s c) = 1 := by
  obtain ⟨i, slot⟩ := s
  cases slot with
  | inl k => exact expanded_regular_row_sum x hx i k
  | inr u =>
    cases u
    exact expanded_designated_row_sum hn x hx i

/-- Every column of the expanded matrix sums to one. -/
theorem expanded_column_sum {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) (hx : IsBalancedFractional x)
    (c : AssignmentColumn n m) :
    (∑ s : AssignmentSlot n m, expandedMatrix x s c) = 1 := by
  cases c with
  | inl g => exact expanded_real_column_sum x hx g
  | inr d => exact expanded_dummy_column_sum hn x hx d

end FairDivision
