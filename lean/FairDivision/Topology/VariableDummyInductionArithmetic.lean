import FairDivision.Topology.VariableDummySlack

/-!
# Slack arithmetic after forcing one real item

In the item-cover branch of the manuscript, the real stock loses one item
and the selected position's requirement falls by one. The useful dummy
total falls by at most one. Hence, if the original dummy stock was below
useful capacity (or useful capacity was zero), the connectivity slack is
unchanged.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Decrease the selected position's required bundle size by one. -/
def variableDecreasedRequirement {k : ℕ}
    (r : Fin k → ℕ) (a : Fin k) : Fin k → ℕ :=
  Function.update r a (r a - 1)

@[simp] theorem variableDecreasedRequirement_at {k : ℕ}
    (r : Fin k → ℕ) (a : Fin k) :
    variableDecreasedRequirement r a a = r a - 1 := by
  simp [variableDecreasedRequirement]

@[simp] theorem variableDecreasedRequirement_other {k : ℕ}
    (r : Fin k → ℕ) (a i : Fin k) (hia : i ≠ a) :
    variableDecreasedRequirement r a i = r i := by
  simp [variableDecreasedRequirement, hia]

/-- Decreasing a positive requirement removes exactly one from the total. -/
theorem variableRequirementTotal_decrease_add_one {k : ℕ}
    (r : Fin k → ℕ) (a : Fin k) (hra : 0 < r a) :
    variableRequirementTotal (variableDecreasedRequirement r a) + 1 =
      variableRequirementTotal r := by
  classical
  unfold variableRequirementTotal variableDecreasedRequirement
  rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hsum := Finset.sum_erase_add Finset.univ r (Finset.mem_univ a)
  rw [Finset.erase_eq] at hsum
  omega

/-- Useful dummy capacity cannot increase when one requirement falls. -/
theorem variableUsefulDummyTotal_decrease_le {k : ℕ}
    (r c : Fin k → ℕ) (a : Fin k) :
    variableUsefulDummyTotal (variableDecreasedRequirement r a) c ≤
      variableUsefulDummyTotal r c := by
  unfold variableUsefulDummyTotal
  apply Finset.sum_le_sum
  intro i _
  by_cases hia : i = a
  · subst i
    simp only [variableDecreasedRequirement_at]
    omega
  · rw [variableDecreasedRequirement_other r a i hia]

/-- Useful dummy capacity falls by at most one. -/
theorem variableUsefulDummyTotal_le_decrease_add_one {k : ℕ}
    (r c : Fin k → ℕ) (a : Fin k) (hra : 0 < r a) :
    variableUsefulDummyTotal r c ≤
      variableUsefulDummyTotal (variableDecreasedRequirement r a) c + 1 := by
  classical
  have hfun : (fun i : Fin k =>
      min (variableDecreasedRequirement r a i) (c i)) =
      Function.update (fun i : Fin k => min (r i) (c i))
        a (min (r a - 1) (c a)) := by
    funext i
    by_cases hia : i = a
    · subst i
      simp
    · simp [hia]
  unfold variableUsefulDummyTotal
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ a)]
  have hsum := Finset.sum_erase_add Finset.univ
    (fun i : Fin k => min (r i) (c i)) (Finset.mem_univ a)
  rw [Finset.erase_eq] at hsum
  have hmin : min (r a) (c a) ≤ min (r a - 1) (c a) + 1 := by
    omega
  omega

/-- In the item-cover branch, the usable-dummy term is unchanged after
removing one required real item. -/
theorem variableMinDummy_decrease_eq {k : ℕ}
    (d : ℕ) (r c : Fin k → ℕ) (a : Fin k)
    (hra : 0 < r a)
    (hBranch : d < variableUsefulDummyTotal r c ∨
      variableUsefulDummyTotal r c = 0) :
    min d (variableUsefulDummyTotal (variableDecreasedRequirement r a) c) =
      min d (variableUsefulDummyTotal r c) := by
  have hle := variableUsefulDummyTotal_decrease_le r c a
  have hnear := variableUsefulDummyTotal_le_decrease_add_one r c a hra
  rcases hBranch with hd | hu
  · omega
  · omega

/-- Real-stock and requirement decrements cancel, leaving the manuscript's
connectivity slack unchanged. -/
theorem variableSlack_decrease_eq {k : ℕ}
    (N d : ℕ) (r c : Fin k → ℕ) (a : Fin k)
    (hN : 0 < N) (hra : 0 < r a)
    (hBranch : d < variableUsefulDummyTotal r c ∨
      variableUsefulDummyTotal r c = 0) :
    variableSlack (N - 1) d (variableDecreasedRequirement r a) c =
      variableSlack N d r c := by
  have hreq := variableRequirementTotal_decrease_add_one r a hra
  have hmin := variableMinDummy_decrease_eq d r c a hra hBranch
  unfold variableSlack
  rw [hmin]
  omega

end FairDivision.Topology
