import FairDivision.Topology.UnlabeledDummyFaceCriterion

/-!
# Relabeling positions in the BF auxiliary complex

A position permutation changes owners in a partial allocation. It reindexes
the real-bundle and dummy-count profile but never labels dummy items.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Relabel the owner of every assigned item. -/
def relabelPartial {k m : ℕ} (σ : Equiv.Perm (Fin k))
    (X : PartialAllocation k m) : PartialAllocation k m :=
  fun g => (X g).map σ

/-- The bundle at the new position `σ i` is the old bundle at `i`. -/
theorem partialBundle_relabel {k m : ℕ} (σ : Equiv.Perm (Fin k))
    (X : PartialAllocation k m) (i : Fin k) :
    partialBundle (relabelPartial σ X) (σ i) = partialBundle X i := by
  classical
  ext g
  cases h : X g with
  | none => simp [partialBundle, relabelPartial, h]
  | some j =>
      simp [partialBundle, relabelPartial, h, σ.injective.eq_iff]

/-- A relabeled valid allocation is valid with the same size and dummy caps. -/
def relabelPartialVertex {k m r c : ℕ} {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (X : PartialVertex k D r c) :
    PartialVertex k D r c :=
  ⟨relabelPartial σ X.1, by
    intro j
    have hBundle : partialBundle (relabelPartial σ X.1) j =
        partialBundle X.1 (σ.symm j) := by
      simpa using partialBundle_relabel σ X.1 (σ.symm j)
    rw [hBundle]
    exact X.2 (σ.symm j)⟩

/-- Relabeling a vertex only reindexes its unlabeled profile. -/
def relabelUnlabeledVertex {k m r c : ℕ} {D : Finset (Fin m)}
    (σ : Equiv.Perm (Fin k)) (p : UnlabeledDummyVertex k m r c D) :
    UnlabeledDummyVertex k m r c D := by
  refine ⟨fun i => p.1 (σ.symm i), ?_⟩
  obtain ⟨X, hX⟩ := p.2
  refine ⟨relabelPartialVertex σ X, ?_⟩
  funext i
  have hBundle : partialBundle (relabelPartial σ X.1) i =
      partialBundle X.1 (σ.symm i) := by
    simpa using partialBundle_relabel σ X.1 (σ.symm i)
  change (partialBundle (relabelPartial σ X.1) i \ D,
    (partialBundle (relabelPartial σ X.1) i ∩ D).card) = p.1 (σ.symm i)
  rw [hBundle]
  exact congrFun hX (σ.symm i)

/-- Relabeling and forgetting dummy labels commute. -/
theorem relabelUnlabeledVertex_of_partial {k m r c : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (X : PartialVertex k D r c) :
    relabelUnlabeledVertex σ (toUnlabeledDummyVertex X) =
      toUnlabeledDummyVertex (relabelPartialVertex σ X) := by
  apply Subtype.ext
  funext i
  have hBundle : partialBundle (relabelPartial σ X.1) i =
      partialBundle X.1 (σ.symm i) := by
    simpa using partialBundle_relabel σ X.1 (σ.symm i)
  change (partialBundle X.1 (σ.symm i) \ D,
    (partialBundle X.1 (σ.symm i) ∩ D).card) =
    (partialBundle (relabelPartial σ X.1) i \ D,
    (partialBundle (relabelPartial σ X.1) i ∩ D).card)
  rw [hBundle]

end FairDivision.Topology
