import FairDivision.BF.Applications.NonlinearDiscrepancy

/-!
# The exact sharp examples for nonlinear discrepancy

These are precisely the manuscript's four-item nonmonotone valuation and
two-item additive valuation. Every balanced bipartition in the first
example has spread two; every balanced bipartition in the second has
spread one, even though both parts have the same size.
-/

set_option autoImplicit false

namespace FairDivision.BF.Applications

open FairDivision

/-- Odd-cardinality sets have value one; pairs containing the distinguished
item have value two; all other even-cardinality sets have value zero. -/
def fourItemSharpValue (S : Finset (Fin 4)) : ℝ :=
  if S.card % 2 = 1 then 1 else if S.card = 2 ∧ (0 : Fin 4) ∈ S then 2 else 0

/-- Every single-item addition joins an odd set of value one to an even
set of value zero or two. -/
theorem fourItemSharpValue_lipschitz : SingleItemLipschitz fourItemSharpValue 1 := by
  intro S x hx
  have hCard : S.card ≤ 3 := by
    have hBound := Finset.card_le_univ (insert x S)
    rw [Finset.card_insert_of_notMem hx] at hBound
    norm_num at hBound
    omega
  interval_cases hSize : S.card <;>
    simp [fourItemSharpValue, Finset.card_insert_of_notMem hx, hSize] <;>
    split_ifs <;> norm_num

/-- In a two-agent allocation there is always an agent other than the
owner of a distinguished item. This makes the sharpness examples literal
allocation examples rather than abstract lists of parts. -/
theorem distinguished_item_two_owners {m : ℕ} (g : Fin m) (A : Allocation 2 m) :
    ∃ i j : Fin 2, g ∈ bundle A i ∧ g ∉ bundle A j := by
  let j : Fin 2 := if A g = 0 then 1 else 0
  have hOther : A g ≠ j := by
    by_cases hOwner : A g = 0
    · simp [j, hOwner]
    · simpa only [j, if_neg hOwner] using hOwner
  refine ⟨A g, j, ?_, ?_⟩
  · simp [bundle]
  · simpa [bundle] using hOther

/-- Both parts are pairs, and exactly one contains the distinguished item.
Their values are therefore two and zero, in every balanced bipartition. -/
theorem fourItemSharpValue_every_balanced_partition (A : Allocation 2 4)
    (hBalanced : IsBalanced A) :
    (∀ i : Fin 2, (bundle A i).card = 2) ∧
      ∃ i j : Fin 2, |fourItemSharpValue (bundle A i) -
        fourItemSharpValue (bundle A j)| = 2 := by
  have hCard (i : Fin 2) : (bundle A i).card = 2 := by
    rcases hBalanced i with h | h <;> simpa [upperSize] using h
  refine ⟨hCard, ?_⟩
  obtain ⟨i, j, hi, hj⟩ := distinguished_item_two_owners (0 : Fin 4) A
  refine ⟨i, j, ?_⟩
  norm_num [fourItemSharpValue, hCard i, hCard j, hi, hj]

/-- No constant strictly below two bounds the spread of every balanced
partition, even for the manuscript's fixed four-item 1-Lipschitz example. -/
theorem nonlinear_constant_two_sharp (c : ℝ) (hc : c < 2) :
    ∃ f : Finset (Fin 4) → ℝ, SingleItemLipschitz f 1 ∧
      ∀ A : Allocation 2 4, IsBalanced A → ¬HasValueSpreadAtMost f A c := by
  refine ⟨fourItemSharpValue, fourItemSharpValue_lipschitz, ?_⟩
  intro A hBalanced hSpread
  obtain ⟨_, i, j, hValue⟩ := fourItemSharpValue_every_balanced_partition A hBalanced
  have := hSpread i j
  rw [hValue] at this
  linarith

/-- The additive two-item example: the distinguished item is worth one,
and the other item is worth zero. -/
def twoItemSharpValue (S : Finset (Fin 2)) : ℝ :=
  if (0 : Fin 2) ∈ S then 1 else 0

theorem twoItemSharpValue_monotone : Monotone twoItemSharpValue := by
  intro S T hST
  by_cases hS : (0 : Fin 2) ∈ S
  · simp [twoItemSharpValue, hS, hST hS]
  · by_cases hT : (0 : Fin 2) ∈ T <;> norm_num [twoItemSharpValue, hS, hT]

theorem twoItemSharpValue_lipschitz : SingleItemLipschitz twoItemSharpValue 1 := by
  intro S x _
  simp only [twoItemSharpValue]
  split_ifs <;> norm_num

/-- Balanced parts in this example are singletons, and their additive
values differ by exactly one. -/
theorem twoItemSharpValue_every_balanced_partition (A : Allocation 2 2)
    (hBalanced : IsBalanced A) :
    (∀ i : Fin 2, (bundle A i).card = 1) ∧
      ∃ i j : Fin 2, |twoItemSharpValue (bundle A i) -
        twoItemSharpValue (bundle A j)| = 1 := by
  have hCard (i : Fin 2) : (bundle A i).card = 1 := by
    rcases hBalanced i with h | h <;> simpa [upperSize] using h
  refine ⟨hCard, ?_⟩
  obtain ⟨i, j, hi, hj⟩ := distinguished_item_two_owners (0 : Fin 2) A
  refine ⟨i, j, ?_⟩
  norm_num [twoItemSharpValue, hi, hj]

/-- No monotone constant strictly below one works, even for two items and
two equally sized parts. -/
theorem monotone_constant_one_sharp (c : ℝ) (hc : c < 1) :
    ∃ f : Finset (Fin 2) → ℝ, Monotone f ∧ SingleItemLipschitz f 1 ∧
      ∀ A : Allocation 2 2, IsBalanced A → ¬HasValueSpreadAtMost f A c := by
  refine ⟨twoItemSharpValue, twoItemSharpValue_monotone,
    twoItemSharpValue_lipschitz, ?_⟩
  intro A hBalanced hSpread
  obtain ⟨_, i, j, hValue⟩ := twoItemSharpValue_every_balanced_partition A hBalanced
  have := hSpread i j
  rw [hValue] at this
  linarith

end FairDivision.BF.Applications
