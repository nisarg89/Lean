import FairDivision.BF.HeterogeneousRealCount
import FairDivision.BF.HeterogeneousTransfer

/-!
# BF Section 5: one simultaneous donor and recipient update

The manuscript shortens a full real bundle and gives the removed item to a
deficient bundle. This module makes that operation on the whole allocation,
retaining disjointness, coverage, and the certificates needed for repetition.
-/

set_option autoImplicit false

namespace FairDivision.BF

/-- One manuscript rebalancing move eliminates one deficient bundle while
retaining the real-allocation invariant. -/
theorem HeteroRealState.rebalance_one
    {n m r d : ℕ} {Rstock : Finset (Fin m)}
    {v : Fin n → Finset (Fin m) → ℝ} {τ : Fin n → ℝ}
    {R : Fin n → Finset (Fin m)}
    (h : HeteroRealState r Rstock v τ R)
    (hr : 1 ≤ r)
    (hTotal : Rstock.card + d = n * (r + 1))
    (hDlt : d < n)
    (hSmall : (Finset.univ.filter
      (fun i : Fin n => (R i).card = r - 1)).Nonempty) :
    ∃ A : Fin n → Finset (Fin m),
      HeteroRealState r Rstock v τ A ∧
      (Finset.univ.filter
        (fun i : Fin n => (A i).card = r - 1)).card <
      (Finset.univ.filter
        (fun i : Fin n => (R i).card = r - 1)).card := by
  classical
  obtain ⟨j, hj⟩ := h.exists_full_of_small hr hTotal hDlt hSmall
  obtain ⟨i, hiFilter⟩ := hSmall
  have hi : (R i).card = r - 1 := (Finset.mem_filter.mp hiFilter).2
  have hij : i ≠ j := by
    intro hEq
    subst j
    omega
  obtain ⟨C, hCSub, hCCard, hCBrackets⟩ :=
    ((h.1 j).2).full_shorten hj
  obtain ⟨hLow, hHigh⟩ := ((h.1 i).2).small_values hr hi
  obtain ⟨z, hzF, hzS, hRemove, _, hRecCard, _, hRecBrackets⟩ :=
    hetero_rebalance_pair hr hj hCSub hCCard hCBrackets
      hi hLow hHigh (h.2.1 j i (Ne.symm hij))
  have hzC : z ∉ C := by
    rw [← hRemove]
    simp
  let R1 := Function.update R j C
  let A := Function.update R1 i (insert z (R i))
  have hAi : A i = insert z (R i) := by simp [A]
  have hAj : A j = C := by simp [A, R1, Ne.symm hij]
  have hAk (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
      A k = R k := by simp [A, R1, hki, hkj]
  have hDonorRecipient : Disjoint C (insert z (R i)) := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxIns
    rcases Finset.mem_insert.mp hxIns with rfl | hxRi
    · exact hzC hxC
    · exact (Finset.disjoint_left.mp (h.2.1 j i (Ne.symm hij)))
        (hCSub hxC) hxRi
  have hRecipientOther (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
      Disjoint (insert z (R i)) (R k) := by
    apply Finset.disjoint_left.mpr
    intro x hxIns hxk
    rcases Finset.mem_insert.mp hxIns with rfl | hxRi
    · exact (Finset.disjoint_left.mp (h.2.1 j k (Ne.symm hkj))) hzF hxk
    · exact (Finset.disjoint_left.mp (h.2.1 i k (Ne.symm hki))) hxRi hxk
  have hDonorOther (k : Fin n) (hkj : k ≠ j) :
      Disjoint C (R k) :=
    (h.2.1 j k (Ne.symm hkj)).mono hCSub (Finset.Subset.rfl)
  have hState : HeteroRealState r Rstock v τ A := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k
        rw [hAi]
        exact ⟨Finset.insert_subset ((h.1 j).1 hzF) (h.1 i).1,
          Or.inr (Or.inl ⟨hRecCard, hRecBrackets⟩)⟩
      · by_cases hkj : k = j
        · subst k
          rw [hAj]
          exact ⟨hCSub.trans (h.1 j).1,
            Or.inr (Or.inl ⟨hCCard, hCBrackets⟩)⟩
        · rw [hAk k hki hkj]
          exact h.1 k
    · intro k l hkl
      by_cases hki : k = i
      · subst k
        rw [hAi]
        by_cases hlj : l = j
        · subst l
          rw [hAj]
          exact hDonorRecipient.symm
        · rw [hAk l (Ne.symm hkl) hlj]
          exact hRecipientOther l (Ne.symm hkl) hlj
      · by_cases hkj : k = j
        · subst k
          rw [hAj]
          by_cases hli : l = i
          · subst l
            rw [hAi]
            exact hDonorRecipient
          · rw [hAk l hli (Ne.symm hkl)]
            exact hDonorOther l (Ne.symm hkl)
        · rw [hAk k hki hkj]
          by_cases hli : l = i
          · subst l
            rw [hAi]
            exact (hRecipientOther k hki hkj).symm
          · by_cases hlj : l = j
            · subst l
              rw [hAj]
              exact (hDonorOther k hkj).symm
            · rw [hAk l hli hlj]
              exact h.2.1 k l hkl
    · intro x hxStock
      obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp (h.2.2 hxStock)
      by_cases hki : k = i
      · subst k
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, by rw [hAi]; exact Finset.mem_insert_of_mem hxk⟩
      · by_cases hkj : k = j
        · subst k
          by_cases hxz : x = z
          · subst x
            exact Finset.mem_biUnion.mpr
              ⟨i, Finset.mem_univ _, by rw [hAi]; exact Finset.mem_insert_self _ _⟩
          · have hxC : x ∈ C := by
              rw [← hRemove]
              exact Finset.mem_sdiff.mpr ⟨hxk, by simpa using hxz⟩
            exact Finset.mem_biUnion.mpr
              ⟨j, Finset.mem_univ _, by rw [hAj]; exact hxC⟩
        · exact Finset.mem_biUnion.mpr
            ⟨k, Finset.mem_univ _, by rw [hAk k hki hkj]; exact hxk⟩
  have hSmallFilter :
      (Finset.univ.filter (fun k : Fin n => (A k).card = r - 1)) =
      (Finset.univ.filter (fun k : Fin n => (R k).card = r - 1)).erase i := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [hAi, hRecCard]
      omega
    · by_cases hkj : k = j
      · subst k
        simp [hAj, hCCard, hj, hki]
        omega
      · simp [hAk k hki hkj, hki]
  refine ⟨A, hState, ?_⟩
  rw [hSmallFilter]
  exact Finset.card_erase_lt_of_mem hiFilter

end FairDivision.BF
