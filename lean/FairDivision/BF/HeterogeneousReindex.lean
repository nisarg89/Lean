import FairDivision.BF.HeterogeneousFiniteConversion
import FairDivision.Finite.DummyRemovalReindex
import FairDivision.Finite.BundlePartitionAllocation

/-!
# BF Section 5: reindexing the real stock

The manuscript's finite conversion produces a partition of the nondummy
subset of the augmented item type. The existing reindexing equivalence
renames that subset as a standard `Fin` type. Optional-deletion witnesses
and their valuation comparisons transport through this equivalence.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Finite

/-- Pulling a heterogeneous bracket through the real-item equivalence
preserves both optional-deletion witnesses. -/
theorem HeteroBrackets.pullbackReal
    {n N : ℕ} (D : Finset (Fin N))
    {v : Fin n → Finset (Fin (N - D.card)) → ℝ}
    {τ : Fin n → ℝ} {owner : Fin n} {R : Finset (Fin N)}
    (h : HeteroBrackets
      (fun j S => v j (pullbackRealBundle D S)) τ owner R) :
    HeteroBrackets v τ owner (pullbackRealBundle D R) := by
  rcases h with ⟨hLower, hUpper⟩
  have hDelete (E : Finset (Fin N)) (hE : CanDeleteOne E R) :
      CanDeleteOne (pullbackRealBundle D E)
        (pullbackRealBundle D R) := by
    constructor
    · exact pullbackRealBundle_mono D hE.1
    · calc
        (pullbackRealBundle D E).card = (E \ D).card :=
          card_pullbackRealBundle D E
        _ ≤ E.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ 1 := hE.2
  constructor
  · intro j
    obtain ⟨E, hE, hValue⟩ := hLower j
    refine ⟨pullbackRealBundle D E, hDelete E hE, ?_⟩
    rw [← pullbackRealBundle_sdiff D R E]
    exact hValue
  · obtain ⟨E, hE, hValue⟩ := hUpper
    refine ⟨pullbackRealBundle D E, hDelete E hE, ?_⟩
    rw [← pullbackRealBundle_sdiff D R E]
    exact hValue

/-- A disjoint real family covering every nondummy item becomes a complete
allocation after the manuscript's harmless reindexing of item labels. -/
theorem exists_allocation_of_hetero_real_family
    {n N r : ℕ} (D : Finset (Fin N))
    (v : Fin n → Finset (Fin (N - D.card)) → ℝ)
    (τ : Fin n → ℝ)
    (R : Fin n → Finset (Fin N))
    (hSubset : ∀ i : Fin n,
      R i ⊆ (Finset.univ : Finset (Fin N)) \ D)
    (hPairReal : ∀ i j : Fin n, i ≠ j → Disjoint (R i) (R j))
    (hCoverReal : (Finset.univ : Finset (Fin N)) \ D ⊆
      Finset.univ.biUnion R)
    (hSizes : ∀ i : Fin n, (R i).card = r ∨ (R i).card = r + 1)
    (hBrackets : ∀ i : Fin n,
      HeteroBrackets
        (fun j S => v j (pullbackRealBundle D S)) τ i (R i)) :
    ∃ A : FairDivision.Allocation n (N - D.card),
      (∀ i : Fin n, FairDivision.bundle A i = pullbackRealBundle D (R i)) ∧
      (∀ i : Fin n, (FairDivision.bundle A i).card = (R i).card) ∧
      (∀ i : Fin n, (FairDivision.bundle A i).card = r ∨
        (FairDivision.bundle A i).card = r + 1) ∧
      FairDivision.IsEF11 v A := by
  classical
  let B' : Fin n → Finset (Fin (N - D.card)) :=
    fun i => pullbackRealBundle D (R i)
  have hPair : ∀ i j : Fin n, i ≠ j → Disjoint (B' i) (B' j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    have hi : (realItemEquiv D g).val ∈ R i := by
      simpa [B', pullbackRealBundle] using hgi
    have hj : (realItemEquiv D g).val ∈ R j := by
      simpa [B', pullbackRealBundle] using hgj
    exact (Finset.disjoint_left.mp (hPairReal i j hij)) hi hj
  have hCover : Finset.univ.biUnion B' =
      (Finset.univ : Finset (Fin (N - D.card))) := by
    ext g
    constructor
    · intro _
      exact Finset.mem_univ g
    · intro _
      have hgReal : (realItemEquiv D g).val ∈
          (Finset.univ : Finset (Fin N)) \ D :=
        (realItemEquiv D g).property
      obtain ⟨i, _, hRi⟩ := Finset.mem_biUnion.mp (hCoverReal hgReal)
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, by simp [B', pullbackRealBundle, hRi]⟩
  obtain ⟨A, hBundle⟩ :=
    exists_allocation_of_disjoint_cover B' hPair hCover
  have hCardEq (i : Fin n) :
      (FairDivision.bundle A i).card = (R i).card := by
    rw [hBundle i]
    change (pullbackRealBundle D (R i)).card = (R i).card
    rw [card_pullbackRealBundle D (R i)]
    have hReal : R i \ D = R i := by
      apply Finset.sdiff_eq_self_iff_disjoint.mpr
      apply Finset.disjoint_left.mpr
      intro x hxRi hxD
      have hxReal : x ∈ (Finset.univ : Finset (Fin N)) \ D :=
        (hSubset i) hxRi
      exact (Finset.mem_sdiff.mp hxReal).2 hxD
    rw [hReal]
  refine ⟨A, hBundle, hCardEq, ?_, ?_⟩
  · intro i
    rw [hCardEq i]
    exact hSizes i
  · intro i j
    have hOwn := HeteroBrackets.pullbackReal D (hBrackets i)
    have hOther := HeteroBrackets.pullbackReal D (hBrackets j)
    obtain ⟨C, hC, hHigh⟩ := hOwn.2
    obtain ⟨G, hG, hLow⟩ := hOther.1 i
    rw [hBundle i, hBundle j]
    exact ⟨C, G, hC, hG, hLow.trans hHigh⟩

end FairDivision.BF
