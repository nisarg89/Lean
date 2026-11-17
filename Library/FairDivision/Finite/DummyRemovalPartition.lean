import FairDivision.Finite.DummyRemovalBalance
import FairDivision.Finite.DummyRemovalThreshold

/-!
# Real-bundle partition after deleting BF dummy items

The augmented allocation partitions all items. Deleting the dummy set from
each bundle leaves a disjoint partition of the real stock, preserves the
common optional-deletion threshold, and gives bundle sizes `q` or `q-1`.
The final finite-type reindexing to `Allocation n m_real` is separate.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open FairDivision

/-- A completed augmented bundle projects to a balanced-size real bundle
with the same common threshold under optional one-item deletions. -/
theorem realBundle_after_dummyRemoval {n m q : ℕ}
    (A : Allocation n m) (D : Finset (Fin m))
    (v : Finset (Fin m) → ℝ) (t : ℝ)
    (h : ∀ i : Fin n,
      (bundle A i).card = q ∧
      BracketsOneDeletion (fun F => v (F \ D)) (bundle A i) t ∧
      (bundle A i ∩ D).card ≤ 1)
    (i : Fin n) :
    ((bundle A i \ D).card = q ∨
      (bundle A i \ D).card + 1 = q) ∧
    (∃ E : Finset (Fin m), E ⊆ bundle A i \ D ∧ E.card ≤ 1 ∧
      v ((bundle A i \ D) \ E) ≤ t) ∧
    (∃ E : Finset (Fin m), E ⊆ bundle A i \ D ∧ E.card ≤ 1 ∧
      t ≤ v ((bundle A i \ D) \ E)) := by
  obtain ⟨hFull, hBracket, hCap⟩ := h i
  exact ⟨card_removeDummies_full_or_short (bundle A i) D q hFull hCap,
    bracketsOneDeletion_removeDummies v (bundle A i) D t hBracket⟩

/-- The projected real bundles remain pairwise disjoint. -/
theorem realBundle_pairwise_disjoint {n m : ℕ}
    (A : Allocation n m) (D : Finset (Fin m))
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (bundle A i \ D) (bundle A j \ D) := by
  apply Finset.disjoint_left.mpr
  intro g hgi hgj
  have hi : A g = i :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hgi).1).2
  have hj : A g = j :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hgj).1).2
  exact hij (hi.symm.trans hj)

/-- Every nondummy item appears in exactly one projected bundle. -/
theorem realBundle_cover {n m : ℕ}
    (A : Allocation n m) (D : Finset (Fin m)) :
    Finset.univ.biUnion (fun i : Fin n => bundle A i \ D) =
      (Finset.univ : Finset (Fin m)) \ D := by
  ext g
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hgi, hgD⟩
    exact hgD
  · intro hgD
    refine ⟨A g, ?_, hgD⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

end FairDivision.Finite
