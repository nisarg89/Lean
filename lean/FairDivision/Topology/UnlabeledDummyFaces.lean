import FairDivision.Topology.UnlabeledDummyComplex

/-!
# Necessary face conditions for the unlabeled-dummy complex

A compatible family has disjoint real pools. At each position the largest
number of dummy items used by a vertex fits in that position's labeled dummy
pool, and these pools are disjoint subsets of the available dummy set.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The union of the real bundles at one position over an auxiliary face. -/
def unlabeledRealPool {k m r c : ℕ} {D : Finset (Fin m)}
    (S : Finset (UnlabeledDummyVertex k m r c D))
    (i : Fin k) : Finset (Fin m) :=
  Finset.univ.filter (fun g =>
    ∃ p ∈ S, g ∈ (p.1 i).1)

/-- The largest dummy count at one position over an auxiliary face. -/
def unlabeledDummyMax {k m r c : ℕ} {D : Finset (Fin m)}
    (S : Finset (UnlabeledDummyVertex k m r c D))
    (i : Fin k) : ℕ :=
  S.sup (fun p => (p.1 i).2)

private theorem unlabeledRealPool_subset_pool {k m r c : ℕ}
    {D : Finset (Fin m)}
    (T : Finset (PartialVertex k D r c)) (i : Fin k) :
    unlabeledRealPool (T.image toUnlabeledDummyVertex) i ⊆ pool T i := by
  classical
  intro g hg
  obtain ⟨p, hp, hgp⟩ := (Finset.mem_filter.mp hg).2
  obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hp
  rw [← hXp] at hgp
  have hgBundle : g ∈ partialBundle X.1 i :=
    (Finset.mem_sdiff.mp hgp).1
  exact partialBundle_subset_pool hXT i hgBundle

private theorem unlabeledDummyMax_le_pool_card {k m r c : ℕ}
    {D : Finset (Fin m)}
    (T : Finset (PartialVertex k D r c)) (i : Fin k) :
    unlabeledDummyMax (T.image toUnlabeledDummyVertex) i ≤
      (pool T i ∩ D).card := by
  classical
  unfold unlabeledDummyMax
  apply Finset.sup_le
  intro p hp
  obtain ⟨X, hXT, hXp⟩ := Finset.mem_image.mp hp
  rw [← hXp]
  change (partialBundle X.1 i ∩ D).card ≤ (pool T i ∩ D).card
  apply Finset.card_le_card
  intro g hg
  exact Finset.mem_inter.mpr ⟨
    partialBundle_subset_pool hXT i (Finset.mem_inter.mp hg).1,
    (Finset.mem_inter.mp hg).2⟩

/-- The manuscript's two numerical face constraints are necessary for a
compatible choice of labeled representatives. -/
theorem unlabeledFace_necessary {k m r c : ℕ}
    {D : Finset (Fin m)}
    (S : Finset (UnlabeledDummyVertex k m r c D))
    (hS : IsUnlabeledCompatibleFamily S) :
    (∀ i j : Fin k, i ≠ j →
      Disjoint (unlabeledRealPool S i) (unlabeledRealPool S j)) ∧
      (∑ i : Fin k, unlabeledDummyMax S i) ≤ D.card := by
  classical
  obtain ⟨T, hT, hImage⟩ := hS
  constructor
  · intro i j hij
    rw [← hImage]
    exact (hT.1 i j hij).mono
      (unlabeledRealPool_subset_pool T i)
      (unlabeledRealPool_subset_pool T j)
  · rw [← hImage]
    have hMax : ∑ i : Fin k,
        unlabeledDummyMax (T.image toUnlabeledDummyVertex) i ≤
        ∑ i : Fin k, (pool T i ∩ D).card := by
      apply Finset.sum_le_sum
      intro i _
      exact unlabeledDummyMax_le_pool_card T i
    have hPair : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => pool T i ∩ D) := by
      intro i _ j _ hij
      exact (hT.1 i j hij).mono
        Finset.inter_subset_left Finset.inter_subset_left
    have hUnion :
        (Finset.univ.biUnion (fun i : Fin k => pool T i ∩ D)) ⊆ D := by
      intro g hg
      obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hg
      exact (Finset.mem_inter.mp hgi).2
    calc
      (∑ i : Fin k, unlabeledDummyMax
        (T.image toUnlabeledDummyVertex) i) ≤
          ∑ i : Fin k, (pool T i ∩ D).card := hMax
      _ = (Finset.univ.biUnion (fun i : Fin k => pool T i ∩ D)).card :=
        (Finset.card_biUnion hPair).symm
      _ ≤ D.card := Finset.card_le_card hUnion

end FairDivision.Topology
