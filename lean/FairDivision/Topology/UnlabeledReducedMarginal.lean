import FairDivision.Topology.UnlabeledMarginalFin
import FairDivision.Finite.DummyRemovalReindex

/-!
# Marginal lotteries indexed by real items and one dummy placeholder

The corrected auxiliary complex is indexed by all augmented item labels.
Virtual valuations, however, are defined on the actual real-item set and one
common dummy. This module reindexes the real part of each auxiliary vertex
before forming its marginal lottery. Position relabeling still permutes these
marginals, and every positively supported marginal bundle has a source vertex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open FairDivision.Finite

/-- Remove actual dummy labels from a profile's real bundle, reindex the
remaining items, and represent its possible dummy by zero. -/
noncomputable def reducedMarginalBundle {k N r : ℕ}
    {D : Finset (Fin N)}
    (p : UnlabeledDummyVertex k N r 1 D) (i : Fin k) :
    Finset (Fin (N - D.card + 1)) :=
  (pullbackRealBundle D (p.1 i).1).image Fin.succ ∪
    if (p.1 i).2 = 0 then ∅ else {0}

/-- The reduced bundle still has the manuscript's exact marginal size. -/
theorem reducedMarginalBundle_card {k N r : ℕ}
    {D : Finset (Fin N)}
    (p : UnlabeledDummyVertex k N r 1 D) (i : Fin k) :
    (reducedMarginalBundle p i).card = r := by
  classical
  have hReal : (pullbackRealBundle D (p.1 i).1).card =
      (p.1 i).1.card := by
    rw [card_pullbackRealBundle]
    exact congrArg Finset.card
      (unlabeledProfile_real_disjoint_dummy p i).sdiff_eq_left
  have hImage : ((pullbackRealBundle D (p.1 i).1).image Fin.succ).card =
      (p.1 i).1.card := by
    rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]
    exact hReal
  have hProfile := unlabeledProfile_card p i
  by_cases hzero : (p.1 i).2 = 0
  · simp only [hzero, add_zero] at hProfile
    simpa [reducedMarginalBundle, hzero, hImage] using hProfile
  · have hone : (p.1 i).2 = 1 := by
      have hcap := unlabeledProfile_dummy_le_cap p i
      omega
    simp only [hone] at hProfile
    simpa [reducedMarginalBundle, hzero, hImage] using hProfile

/-- The reduced finite-coordinate marginal vertex. -/
noncomputable def reducedMarginalVertex {k N r : ℕ}
    {D : Finset (Fin N)}
    (p : UnlabeledDummyVertex k N r 1 D) (i : Fin k) :
    FixedFinMarginalBundle (N - D.card) r :=
  ⟨reducedMarginalBundle p i, reducedMarginalBundle_card p i⟩

/-- The reduced real part is exactly the real part of the original profile,
in the final allocation's real-item coordinates. -/
theorem marginalRealPart_reducedVertex {k N r : ℕ}
    {D : Finset (Fin N)}
    (p : UnlabeledDummyVertex k N r 1 D) (i : Fin k) :
    marginalRealPart (reducedMarginalVertex p i).1 =
      pullbackRealBundle D (p.1 i).1 := by
  classical
  ext g
  by_cases hzero : (p.1 i).2 = 0
  · simp [marginalRealPart, reducedMarginalVertex,
      reducedMarginalBundle, hzero]
  · simp [marginalRealPart, reducedMarginalVertex,
      reducedMarginalBundle, hzero]

/-- The marginal lottery on actual real items plus one common placeholder. -/
noncomputable def unlabeledReducedMarginal {k N r : ℕ}
    {D : Finset (Fin N)} (i : Fin k) :
    unlabeledLotterySpace k N r 1 D →
      stdSimplex ℝ (FixedFinMarginalBundle (N - D.card) r) :=
  fun x => stdSimplex.map (fun p => reducedMarginalVertex p i) x.1

/-- Reduced marginals vary continuously. -/
theorem unlabeledReducedMarginal_continuous {k N r : ℕ}
    {D : Finset (Fin N)} (i : Fin k) :
    Continuous (unlabeledReducedMarginal (D := D) (r := r) i) := by
  exact (stdSimplex.continuous_map
    (fun p : UnlabeledDummyVertex k N r 1 D =>
      reducedMarginalVertex p i)).comp continuous_subtype_val

/-- Position relabeling carries the new marginal to the old position. -/
theorem reducedMarginalVertex_relabel {k N r : ℕ}
    {D : Finset (Fin N)} (σ : Equiv.Perm (Fin k))
    (p : UnlabeledDummyVertex k N r 1 D) (i : Fin k) :
    reducedMarginalVertex (relabelUnlabeledVertex σ p) (σ i) =
      reducedMarginalVertex p i := by
  apply Subtype.ext
  simp [reducedMarginalVertex, reducedMarginalBundle,
    relabelUnlabeledVertex, Equiv.symm_apply_apply]

/-- The new marginals are equivariant under position relabeling. -/
theorem unlabeledReducedMarginal_relabel {k N r : ℕ}
    {D : Finset (Fin N)} (σ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k N r 1 D) (i : Fin k) :
    unlabeledReducedMarginal (σ i) (auxiliaryRelabel σ x) =
      unlabeledReducedMarginal i x := by
  change stdSimplex.map
      (fun p : UnlabeledDummyVertex k N r 1 D =>
        reducedMarginalVertex p (σ i))
      (stdSimplex.map (relabelUnlabeledVertex σ) x.1) =
    stdSimplex.map
      (fun p : UnlabeledDummyVertex k N r 1 D =>
        reducedMarginalVertex p i) x.1
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext p
  exact reducedMarginalVertex_relabel σ p i

/-- Every supported reduced marginal bundle comes from a supported
unlabeled auxiliary vertex. -/
theorem exists_source_of_reducedMarginal_support {k N r : ℕ}
    {D : Finset (Fin N)}
    (x : unlabeledLotterySpace k N r 1 D) (i : Fin k)
    (B : FixedFinMarginalBundle (N - D.card) r)
    (hB : B ∈ finiteSimplexSupport (unlabeledReducedMarginal i x)) :
    ∃ p ∈ unlabeledLotterySupport x.1,
      reducedMarginalVertex p i = B := by
  have hmap := finiteSimplexSupport_map_subset
    (fun p : UnlabeledDummyVertex k N r 1 D =>
      reducedMarginalVertex p i) x.1 hB
  exact Finset.mem_image.mp hmap


end FairDivision.Topology
