import FairDivision.Definitions

/-!
# Turning a bundle partition into an allocation

The BF completion recursion produces full, pairwise disjoint bundles whose
union is the augmented item set. This finite choice lemma converts that
family to the allocation function used by the final theorem statements.
-/

set_option autoImplicit false

namespace FairDivision.Finite

/-- A disjoint family of bundles covering every item is the bundle family of
some allocation. -/
theorem exists_allocation_of_disjoint_cover {n m : ℕ}
    (B : Fin n → Finset (Fin m))
    (hPair : ∀ i j : Fin n, i ≠ j → Disjoint (B i) (B j))
    (hCover : Finset.univ.biUnion B = (Finset.univ : Finset (Fin m))) :
    ∃ A : FairDivision.Allocation n m,
      ∀ i : Fin n, FairDivision.bundle A i = B i := by
  classical
  have hOwner (g : Fin m) : ∃ i : Fin n, g ∈ B i := by
    have hg : g ∈ Finset.univ.biUnion B := by
      rw [hCover]
      exact Finset.mem_univ g
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
    exact ⟨i, hgi⟩
  let A : FairDivision.Allocation n m :=
    fun g => Classical.choose (hOwner g)
  have hA (g : Fin m) : g ∈ B (A g) :=
    Classical.choose_spec (hOwner g)
  have hUnique (g : Fin m) (i : Fin n)
      (hgi : g ∈ B i) : A g = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hPair (A g) i hne))
      (hA g) hgi
  refine ⟨A, ?_⟩
  intro i
  ext g
  simp only [FairDivision.bundle, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro hgi
    simpa [hgi] using hA g
  · exact hUnique g i

end FairDivision.Finite
