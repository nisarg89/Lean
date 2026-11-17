import FairDivision.Finite.Fractional
import Mathlib.Data.Fintype.EquivFin

/-!
# Slots and dummy columns for rectangular balanced assignment

To apply the square Birkhoff theorem when `m` items are assigned to `n`
agents, create `r + 1` slots per agent where `r = m / n`, and add
`n(r + 1) - m` dummy columns. Every agent has one designated final slot
that may receive a dummy.
-/

set_option autoImplicit false

namespace FairDivision

/-- The number of slots per agent in the Birkhoff expansion. -/
def slotsPerAgent (n m : ℕ) : ℕ := m / n + 1

/-- The number of dummy columns needed to make the slot matrix square. -/
def dummyCount (n m : ℕ) : ℕ := n * slotsPerAgent n m - m

/-- Agent-slot pairs form the row type of the square expansion. -/
abbrev AssignmentSlot (n m : ℕ) := Fin n × (Fin (m / n) ⊕ Unit)

/-- Real items and dummy columns form the column type. -/
abbrev AssignmentColumn (n m : ℕ) := Fin m ⊕ Fin (dummyCount n m)

/-- There is always positive dummy capacity when at least one agent exists. -/
theorem items_lt_slot_count {n m : ℕ} (hn : 0 < n) :
    m < n * slotsPerAgent n m := by
  have hmod := Nat.mod_lt m hn
  have hdiv := Nat.mod_add_div m n
  simp only [slotsPerAgent, mul_add, mul_one]
  omega

theorem dummyCount_pos {n m : ℕ} (hn : 0 < n) :
    0 < dummyCount n m := by
  have h := items_lt_slot_count (m := m) hn
  unfold dummyCount
  omega

theorem item_dummy_count {n m : ℕ} (hn : 0 < n) :
    m + dummyCount n m = n * slotsPerAgent n m := by
  have h := items_lt_slot_count (m := m) hn
  unfold dummyCount
  omega

/-- A fixed equivalence reindexes real and dummy columns by the square
matrix's agent-slot row type. -/
noncomputable def assignmentColumnEquiv (n m : ℕ) (hn : 0 < n) :
    AssignmentColumn n m ≃ AssignmentSlot n m :=
  Fintype.equivOfCardEq (by
    simp only [AssignmentColumn, AssignmentSlot, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_prod, Fintype.card_unit]
    change m + dummyCount n m = n * slotsPerAgent n m
    exact item_dummy_count hn)

end FairDivision
