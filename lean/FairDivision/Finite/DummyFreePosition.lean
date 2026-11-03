import Mathlib

/-!
# Finding a position with no dummy item

Fewer dummy items than positions cannot meet pairwise disjoint bundles at
every position. This is the counting step used when the BF completion proof
needs a full dummy-free bundle for a replacement swap.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- If the dummy stock has size below the number of positions, one of any
pairwise disjoint position bundles has no dummy item. -/
theorem exists_dummy_free_position {α : Type*} [DecidableEq α]
    (k : ℕ) (D : Finset α) (B : Fin k → Finset α)
    (hD : D.card < k)
    (hPair : ∀ i j : Fin k, i ≠ j → Disjoint (B i) (B j)) :
    ∃ i : Fin k, B i ∩ D = ∅ := by
  classical
  have hPairD : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => B i ∩ D) := by
    intro i _ j _ hij
    exact (hPair i j hij).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hUnion : Finset.univ.biUnion (fun i : Fin k => B i ∩ D) ⊆ D := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxi).2
  have hSum : (∑ i : Fin k, (B i ∩ D).card) ≤ D.card := by
    calc
      (∑ i : Fin k, (B i ∩ D).card) =
          (Finset.univ.biUnion (fun i : Fin k => B i ∩ D)).card :=
        (Finset.card_biUnion hPairD).symm
      _ ≤ D.card := Finset.card_le_card hUnion
  have hLess : (∑ i : Fin k, (B i ∩ D).card) <
      ∑ i : Fin k, (1 : ℕ) := by
    simpa using lt_of_le_of_lt hSum hD
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hLess
  have hzero : (B i ∩ D).card = 0 := by omega
  exact ⟨i, Finset.card_eq_zero.mp hzero⟩

end FairDivision.Finite
