import FairDivision.Topology.UnlabeledMarginal
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite augmented-item coordinates for unlabeled marginals

The auxiliary complex uses `Option (Fin m)` so that `none` is a common,
unlabeled dummy placeholder. Existing admissibility certificates use finite
index types. Mathlib's `finSuccEquiv` identifies the placeholder with
zero in `Fin (m+1)` and each real item with its successor.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The common placeholder is item zero; real item `g` is `g.succ`. -/
def marginalItemEquiv (m : ℕ) : Option (Fin m) ≃ Fin (m + 1) :=
  (finSuccEquiv m).symm

@[simp] theorem marginalItemEquiv_none (m : ℕ) :
    marginalItemEquiv m none = 0 :=
  finSuccEquiv_symm_none

@[simp] theorem marginalItemEquiv_some {m : ℕ} (g : Fin m) :
    marginalItemEquiv m (some g) = g.succ :=
  finSuccEquiv_symm_some g

/-- Remove the placeholder from a finite-coordinate augmented bundle. -/
noncomputable def marginalRealPart {m : ℕ}
    (F : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter (fun g => g.succ ∈ F)

/-- The fixed-size marginal vertices in the finite coordinate convention. -/
abbrev FixedFinMarginalBundle (m r : ℕ) :=
  {F : Finset (Fin (m + 1)) // F.card = r}

/-- Translate a marginal vertex to finite augmented-item coordinates. -/
noncomputable def finMarginalVertex {m r : ℕ}
    (B : FixedMarginalBundle m r) : FixedFinMarginalBundle m r := by
  classical
  refine ⟨B.1.image (marginalItemEquiv m), ?_⟩
  rw [Finset.card_image_of_injective _ (marginalItemEquiv m).injective]
  exact B.2

/-- The placeholder is present exactly when the Option bundle contains `none`. -/
theorem zero_mem_finMarginalVertex_iff {m r : ℕ}
    (B : FixedMarginalBundle m r) :
    (0 : Fin (m + 1)) ∈ (finMarginalVertex B).1 ↔ none ∈ B.1 := by
  classical
  simp only [finMarginalVertex, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, heq⟩
    have haNone : a = none :=
      (marginalItemEquiv m).injective
        (heq.trans (marginalItemEquiv_none m).symm)
    exact haNone ▸ ha
  · intro h
    exact ⟨none, h, marginalItemEquiv_none m⟩

/-- A real item is present exactly when its `some` counterpart is present. -/
theorem succ_mem_finMarginalVertex_iff {m r : ℕ}
    (B : FixedMarginalBundle m r) (g : Fin m) :
    g.succ ∈ (finMarginalVertex B).1 ↔ some g ∈ B.1 := by
  classical
  simp only [finMarginalVertex, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, heq⟩
    have haSome : a = some g :=
      (marginalItemEquiv m).injective
        (heq.trans (marginalItemEquiv_some g).symm)
    exact haSome ▸ ha
  · intro h
    exact ⟨some g, h, marginalItemEquiv_some g⟩

/-- Canonical finite-coordinate marginals remember exactly the real bundle
of the original unlabeled auxiliary vertex. -/
theorem marginalRealPart_canonical {k m r : ℕ}
    {D : Finset (Fin m)}
    (p : UnlabeledDummyVertex k m r 1 D) (i : Fin k) :
    marginalRealPart
      (finMarginalVertex (canonicalMarginalVertex p i)).1 = (p.1 i).1 := by
  classical
  ext g
  by_cases hzero : (p.1 i).2 = 0
  · simp [marginalRealPart, succ_mem_finMarginalVertex_iff,
      canonicalMarginalVertex, canonicalMarginalBundle, hzero]
  · simp [marginalRealPart, succ_mem_finMarginalVertex_iff,
      canonicalMarginalVertex, canonicalMarginalBundle, hzero]

/-- The auxiliary position marginal in finite augmented-item coordinates. -/
noncomputable def unlabeledFinMarginal {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    unlabeledLotterySpace k m r 1 D →
      stdSimplex ℝ (FixedFinMarginalBundle m r) :=
  fun x => stdSimplex.map (finMarginalVertex (m := m) (r := r))
    (unlabeledSizedMarginal i x)

/-- Finite-coordinate marginals vary continuously with the auxiliary point. -/
theorem unlabeledFinMarginal_continuous {k m r : ℕ}
    {D : Finset (Fin m)} (i : Fin k) :
    Continuous (unlabeledFinMarginal (D := D) (r := r) i) := by
  exact (stdSimplex.continuous_map
    (finMarginalVertex (m := m) (r := r))).comp
    (unlabeledSizedMarginal_continuous i)

/-- Relabeling positions permutes the finite-coordinate marginal lotteries. -/
theorem unlabeledFinMarginal_relabel {k m r : ℕ}
    {D : Finset (Fin m)} (σ : Equiv.Perm (Fin k))
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k) :
    unlabeledFinMarginal (σ i) (auxiliaryRelabel σ x) =
      unlabeledFinMarginal i x := by
  simp only [unlabeledFinMarginal, unlabeledSizedMarginal_relabel]

/-- A supported finite-coordinate bundle comes from a supported auxiliary
vertex at that position. -/
theorem exists_source_of_finMarginal_support {k m r : ℕ}
    {D : Finset (Fin m)}
    (x : unlabeledLotterySpace k m r 1 D) (i : Fin k)
    (B : FixedFinMarginalBundle m r)
    (hB : B ∈ finiteSimplexSupport (unlabeledFinMarginal i x)) :
    ∃ p ∈ unlabeledLotterySupport x.1,
      finMarginalVertex (canonicalMarginalVertex p i) = B := by
  have hmap := finiteSimplexSupport_map_subset
    (finMarginalVertex (m := m) (r := r))
    (unlabeledSizedMarginal i x) hB
  obtain ⟨C, hC, hCB⟩ := Finset.mem_image.mp hmap
  obtain ⟨p, hp, hpC⟩ := exists_source_of_sizedMarginal_support x i C hC
  refine ⟨p, hp, ?_⟩
  rw [hpC]
  exact hCB

end FairDivision.Topology
