import FairDivision.Topology.UnlabeledPositionAction

/-!
# Position permutations preserve auxiliary faces

The proof relabels one compatible family of labeled representatives and then
forgets the dummy labels. This directly exhibits the symmetric-group action
on the corrected auxiliary complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

private theorem pool_relabel {k m r c : ℕ} {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (T : Finset (PartialVertex k D r c))
    (i : Fin k) :
    pool (T.image (relabelPartialVertex σ)) (σ i) = pool T i := by
  classical
  ext g
  simp only [pool, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨Y, hY, hgY⟩
    obtain ⟨X, hXT, hXY⟩ := Finset.mem_image.mp hY
    rw [← hXY] at hgY
    have hgB : g ∈ partialBundle (relabelPartial σ X.1) (σ i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgY⟩
    rw [partialBundle_relabel] at hgB
    exact ⟨X, hXT, (Finset.mem_filter.mp hgB).2⟩
  · rintro ⟨X, hXT, hgX⟩
    have hgB : g ∈ partialBundle X.1 i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgX⟩
    rw [← partialBundle_relabel σ X.1 i] at hgB
    exact ⟨relabelPartialVertex σ X,
      Finset.mem_image.mpr ⟨X, hXT, rfl⟩,
      (Finset.mem_filter.mp hgB).2⟩

private theorem compatible_relabel {k m r c : ℕ} {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (T : Finset (PartialVertex k D r c))
    (hT : IsCompatibleFamily T) :
    IsCompatibleFamily (T.image (relabelPartialVertex σ)) := by
  classical
  have hPool (j : Fin k) :
      pool (T.image (relabelPartialVertex σ)) j =
        pool T (σ.symm j) := by
    simpa using pool_relabel σ T (σ.symm j)
  constructor
  · intro i j hij
    have hneq : σ.symm i ≠ σ.symm j := by
      intro h
      exact hij (σ.symm.injective h)
    rw [hPool i, hPool j]
    exact hT.1 (σ.symm i) (σ.symm j) hneq
  · intro i
    rw [hPool i]
    exact hT.2 (σ.symm i)

/-- A permutation of positions takes each auxiliary face to a face. -/
theorem unlabeledCompatible_relabel {k m r c : ℕ}
    {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k))
    (S : Finset (UnlabeledDummyVertex k m r c D))
    (hS : IsUnlabeledCompatibleFamily S) :
    IsUnlabeledCompatibleFamily
      (S.image (relabelUnlabeledVertex σ)) := by
  classical
  obtain ⟨T, hT, hImage⟩ := hS
  refine ⟨T.image (relabelPartialVertex σ),
    compatible_relabel σ T hT, ?_⟩
  calc
    (T.image (relabelPartialVertex σ)).image
        toUnlabeledDummyVertex =
        T.image (toUnlabeledDummyVertex ∘ relabelPartialVertex σ) :=
      Finset.image_image
    _ = T.image (relabelUnlabeledVertex σ ∘
        toUnlabeledDummyVertex) := by
      apply Finset.image_congr
      intro X _
      exact (relabelUnlabeledVertex_of_partial σ X).symm
    _ = (T.image toUnlabeledDummyVertex).image
        (relabelUnlabeledVertex σ) := (Finset.image_image).symm
    _ = S.image (relabelUnlabeledVertex σ) := by rw [hImage]

end FairDivision.Topology
