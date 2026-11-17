import Mathlib

/-!
# Counting unallocated items among disjoint short and full bundles

When the total stock has one full bundle's worth per position, each short
bundle accounts for exactly one unallocated item. This is the counting
invariant in the BF completion procedure.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- For pairwise disjoint bundles of sizes `r` or `r+1`, the number of
unallocated items equals the number of short positions. -/
theorem card_unallocated_eq_short_count {α : Type*} [DecidableEq α]
    (k r : ℕ) (U : Finset α) (B : Fin k → Finset α)
    (hBU : ∀ i, B i ⊆ U)
    (hPair : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))
    (hTotal : U.card = k * (r + 1))
    (hSize : ∀ i, (B i).card = r ∨ (B i).card = r + 1) :
    (U \ Finset.univ.biUnion B).card =
      (Finset.univ.filter (fun i : Fin k => (B i).card = r)).card := by
  classical
  have hUnion : Finset.univ.biUnion B ⊆ U := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hBU i hxi
  have hPairSet : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact hPair i j hij
  have hCardUnion : (Finset.univ.biUnion B).card =
      ∑ i : Fin k, (B i).card := (Finset.card_biUnion hPairSet)
  have hPer (i : Fin k) :
      (B i).card + (if (B i).card = r then 1 else 0) = r + 1 := by
    rcases hSize i with hi | hi
    · simp [hi]
    · have hne : (B i).card ≠ r := by omega
      simp [hne, hi]
  have hSum :
      (∑ i : Fin k, (B i).card) +
        (∑ i : Fin k, if (B i).card = r then 1 else 0) =
          k * (r + 1) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hPer]
    simp
  have hShort :
      (∑ i : Fin k, if (B i).card = r then 1 else 0) =
        (Finset.univ.filter (fun i : Fin k => (B i).card = r)).card := by
    simp
  calc
    (U \ Finset.univ.biUnion B).card =
        U.card - (Finset.univ.biUnion B).card :=
      Finset.card_sdiff_of_subset hUnion
    _ = k * (r + 1) - (∑ i : Fin k, (B i).card) := by
      rw [hTotal, hCardUnion]
    _ = (Finset.univ.filter (fun i : Fin k => (B i).card = r)).card := by
      omega

/-- An unallocated item implies that some position is short. -/
theorem exists_short_of_unallocated {α : Type*} [DecidableEq α]
    (k r : ℕ) (U : Finset α) (B : Fin k → Finset α)
    (hBU : ∀ i, B i ⊆ U)
    (hPair : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))
    (hTotal : U.card = k * (r + 1))
    (hSize : ∀ i, (B i).card = r ∨ (B i).card = r + 1)
    (hUnallocated : (U \ Finset.univ.biUnion B).Nonempty) :
    ∃ i : Fin k, (B i).card = r := by
  classical
  have hCount := card_unallocated_eq_short_count
    k r U B hBU hPair hTotal hSize
  have hpos : 0 < (U \ Finset.univ.biUnion B).card :=
    Finset.card_pos.mpr hUnallocated
  rw [hCount] at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- A short position implies that an item remains unallocated. -/
theorem exists_unallocated_of_short {α : Type*} [DecidableEq α]
    (k r : ℕ) (U : Finset α) (B : Fin k → Finset α)
    (hBU : ∀ i, B i ⊆ U)
    (hPair : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j))
    (hTotal : U.card = k * (r + 1))
    (hSize : ∀ i, (B i).card = r ∨ (B i).card = r + 1)
    (i : Fin k) (hi : (B i).card = r) :
    (U \ Finset.univ.biUnion B).Nonempty := by
  classical
  have hCount := card_unallocated_eq_short_count
    k r U B hBU hPair hTotal hSize
  have hshort : i ∈ Finset.univ.filter
      (fun j : Fin k => (B j).card = r) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have hpos : 0 < (Finset.univ.filter
      (fun j : Fin k => (B j).card = r)).card :=
    Finset.card_pos.mpr ⟨i, hshort⟩
  rw [← hCount] at hpos
  exact Finset.card_pos.mp hpos

end FairDivision.Finite
