import FairDivision.Topology.UnlabeledContinuousAction
import FairDivision.Topology.UnlabeledDummyProfiles
import FairDivision.Topology.FiniteSimplexSupportMap

/-!
# Canonical bundle marginals of the unlabeled BF auxiliary complex

At a position, an auxiliary vertex remembers a real bundle and the number
of dummy items, but not their labels. For the heterogeneous virtual
valuations we replace the possible dummy by one common placeholder. Pushing
the auxiliary probability simplex along this vertex map gives a continuous
marginal lottery at each position.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The real bundle with `none` added exactly when this position uses a
dummy. The dummy's original label is deliberately forgotten. -/
noncomputable def canonicalMarginalBundle {k m r : ℕ}
    {D : Finset (Fin m)}
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    Finset (Option (Fin m)) :=
  (p.1 i).1.image some ∪
    if (p.1 i).2 = 0 then ∅ else {none}

/-- The placeholder bundle always has the required number of items
when at most one dummy is allowed at each position. -/
theorem canonicalMarginalBundle_card {k m r : ℕ}
    {D : Finset (Fin m)}
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    (canonicalMarginalBundle p i).card = r := by
  classical
  have hRealCard : ((p.1 i).1.image some).card = (p.1 i).1.card :=
    Finset.card_image_of_injective _
      (fun a b h => Option.some.inj h)
  have hProfile := unlabeledProfile_card p i
  by_cases hzero : (p.1 i).2 = 0
  · simp only [hzero, add_zero] at hProfile
    simpa [canonicalMarginalBundle, hzero, hRealCard] using hProfile
  · have hone : (p.1 i).2 = 1 := by
      have hcap := unlabeledProfile_dummy_le_cap p i
      omega
    simp only [hone] at hProfile
    simpa [canonicalMarginalBundle, hzero, hRealCard]
      using hProfile

/-- Vertices of the manuscript's fixed-size marginal simplex. -/
abbrev FixedMarginalBundle (m r : ℕ) :=
  {F : Finset (Option (Fin m)) // F.card = r}

/-- A canonical fixed-size marginal vertex. -/
noncomputable def canonicalMarginalVertex {k m r : ℕ}
    {D : Finset (Fin m)}
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    FixedMarginalBundle m r :=
  ⟨canonicalMarginalBundle p i, canonicalMarginalBundle_card p i⟩

/-- The marginal lottery in the exact `(q-1)`-bundle simplex used for BF's
virtual valuations. -/
noncomputable def unlabeledSizedMarginal {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    unlabeledLotterySpace k m r 1 D →
      stdSimplex ℝ (FixedMarginalBundle m r) :=
  fun x => stdSimplex.map (fun p => canonicalMarginalVertex p i) x.1

/-- The fixed-size marginal lottery is continuous. -/
theorem unlabeledSizedMarginal_continuous {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    Continuous (unlabeledSizedMarginal (D := D) (r := r) i) := by
  exact (stdSimplex.continuous_map
    (fun p : UnlabeledDummyVertex k m r 1 D =>
      canonicalMarginalVertex p i)).comp continuous_subtype_val

/-- The canonical marginal lottery at one position. -/
noncomputable def unlabeledMarginal {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    unlabeledLotterySpace k m r 1 D →
      stdSimplex ℝ (Finset (Option (Fin m))) :=
  fun x => stdSimplex.map (fun p => canonicalMarginalBundle p i) x.1

/-- The marginal lottery varies continuously over the auxiliary complex. -/
theorem unlabeledMarginal_continuous {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    Continuous (unlabeledMarginal (D := D) (r := r) i) := by
  exact (stdSimplex.continuous_map
    (fun p : UnlabeledDummyVertex k m r 1 D =>
      canonicalMarginalBundle p i)).comp continuous_subtype_val

/-- Position relabeling carries a vertex's canonical bundle at the new
position to its former canonical bundle. -/
theorem canonicalMarginalBundle_relabel {k m r : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    canonicalMarginalBundle (relabelUnlabeledVertex σ p) (σ i) =
      canonicalMarginalBundle p i := by
  simp only [canonicalMarginalBundle, relabelUnlabeledVertex,
    Equiv.symm_apply_apply]

/-- Position relabeling also preserves the fixed-size subtype vertex. -/
theorem canonicalMarginalVertex_relabel {k m r : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    canonicalMarginalVertex (relabelUnlabeledVertex σ p) (σ i) =
      canonicalMarginalVertex p i := by
  apply Subtype.ext
  exact canonicalMarginalBundle_relabel σ p i

/-- The exact fixed-size marginal lotteries permute with the positions. -/
theorem unlabeledSizedMarginal_relabel {k m r : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k) :
    unlabeledSizedMarginal (σ i) (auxiliaryRelabel σ x) =
      unlabeledSizedMarginal i x := by
  change stdSimplex.map
      (fun p : UnlabeledDummyVertex k m r 1 D =>
        canonicalMarginalVertex p (σ i))
      (stdSimplex.map (relabelUnlabeledVertex σ) x.1) =
    stdSimplex.map
      (fun p : UnlabeledDummyVertex k m r 1 D =>
        canonicalMarginalVertex p i) x.1
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext p
  exact canonicalMarginalVertex_relabel σ p i

/-- Relabeling the auxiliary point permutes its marginal lotteries. -/
theorem unlabeledMarginal_relabel {k m r : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k) :
    unlabeledMarginal (σ i) (auxiliaryRelabel σ x) =
      unlabeledMarginal i x := by
  change stdSimplex.map
      (fun p : UnlabeledDummyVertex k m r 1 D =>
        canonicalMarginalBundle p (σ i))
      (stdSimplex.map (relabelUnlabeledVertex σ) x.1) =
    stdSimplex.map
      (fun p : UnlabeledDummyVertex k m r 1 D =>
        canonicalMarginalBundle p i) x.1
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext p
  exact canonicalMarginalBundle_relabel σ p i

/-- Every bundle with positive marginal probability comes from a
positive-weight auxiliary vertex at that position. -/
theorem unlabeledSizedMarginal_support_subset {k m r : ℕ}
    {D : Finset (Fin m)}
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k) :
    finiteSimplexSupport (unlabeledSizedMarginal i x) ⊆
      (unlabeledLotterySupport x.1).image
        (fun p => canonicalMarginalVertex p i) := by
  classical
  exact finiteSimplexSupport_map_subset
    (fun p : UnlabeledDummyVertex k m r 1 D =>
      canonicalMarginalVertex p i) x.1

/-- A supported marginal bundle has an explicit supported source vertex. -/
theorem exists_source_of_sizedMarginal_support {k m r : ℕ}
    {D : Finset (Fin m)}
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k)
    (B : FixedMarginalBundle m r)
    (hB : B ∈ finiteSimplexSupport (unlabeledSizedMarginal i x)) :
    ∃ p ∈ unlabeledLotterySupport x.1,
      canonicalMarginalVertex p i = B := by
  exact Finset.mem_image.mp (unlabeledSizedMarginal_support_subset x i hB)

end FairDivision.Topology
