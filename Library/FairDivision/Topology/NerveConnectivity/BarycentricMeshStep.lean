import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-!
# Quantitative barycentric mesh estimates

The centroid identity is the algebraic starting point for bounding the mesh
of a barycentric subdivision. Subsequent results will compare centroids of
nested finite faces in a normed vector space, then apply that estimate to
chains of faces in a subdivided simplicial complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- For a nonempty finite face in a real normed vector space, its centroid
is the arithmetic mean of its indexed vertices. -/
theorem finiteCentroid_eq_inv_card_smul_sum
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (p : ι → E) (hs : s.Nonempty) :
    s.centroid ℝ p = (s.card : ℝ)⁻¹ • ∑ i ∈ s, p i := by
  rw [s.centroid_eq_centerMass hs]
  rw [s.centerMass_eq_of_sum_1 _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, ← Finset.smul_sum]

/-- The centroid of a nonempty subset lies in the convex hull of the
larger face's vertices. -/
theorem finiteCentroid_mem_convexHull_of_subset
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E)
    (hs : s.Nonempty) (hst : s ⊆ t) :
    s.centroid ℝ p ∈ convexHull ℝ (p '' (t : Set ι)) := by
  rw [s.centroid_eq_centerMass hs]
  apply Finset.centerMass_mem_convexHull s
  · intro i hi
    simp
  · rw [s.sum_centroidWeights_eq_one_of_nonempty ℝ hs]
    norm_num
  · intro i hi
    exact ⟨i, hst hi, rfl⟩

/-- Every vertex of a containing face is within that face's diameter of
the centroid of a nonempty subface. -/
theorem dist_vertex_finiteCentroid_le_diam
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E)
    (hs : s.Nonempty) (hst : s ⊆ t)
    (i : ι) (hit : i ∈ t) :
    dist (p i) (s.centroid ℝ p) ≤
      Metric.diam (p '' (t : Set ι)) := by
  obtain ⟨y, hy, hdist⟩ :=
    convexHull_exists_dist_ge
      (finiteCentroid_mem_convexHull_of_subset s t p hs hst) (p i)
  have hbound : Bornology.IsBounded (p '' (t : Set ι)) :=
    (t.finite_toSet.image p).isBounded
  calc
    dist (p i) (s.centroid ℝ p) =
        dist (s.centroid ℝ p) (p i) := dist_comm _ _
    _ ≤ dist y (p i) := hdist
    _ = dist (p i) y := dist_comm _ _
    _ ≤ Metric.diam (p '' (t : Set ι)) :=
        Metric.dist_le_diam_of_mem hbound ⟨i, hit, rfl⟩ hy

/-- A pairwise bound on the original face controls the distance from
any of its vertices to a subface centroid. -/
theorem dist_vertex_finiteCentroid_le_of_pairwise
    {ι : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E) (δ : ℝ)
    (hs : s.Nonempty) (hst : s ⊆ t)
    (hpair : ∀ i ∈ t, ∀ j ∈ t, dist (p i) (p j) ≤ δ)
    (i : ι) (hit : i ∈ t) :
    dist (p i) (s.centroid ℝ p) ≤ δ := by
  obtain ⟨_, ⟨j, hj, rfl⟩, hdist⟩ :=
    convexHull_exists_dist_ge
      (finiteCentroid_mem_convexHull_of_subset s t p hs hst) (p i)
  calc
    dist (p i) (s.centroid ℝ p) =
        dist (s.centroid ℝ p) (p i) := dist_comm _ _
    _ ≤ dist (p j) (p i) := hdist
    _ ≤ δ := hpair j hj i hit

/-- The difference between the averages of nested faces is the average,
with the larger face's denominator, of the new vertices' displacements
from the smaller face's centroid. -/
theorem card_smul_centroid_sub_eq_sum_sdiff
    {ι : Type u} {E : Type v}
    [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E)
    (hs : s.Nonempty) (hst : s ⊆ t) :
    (t.card : ℝ) • (t.centroid ℝ p - s.centroid ℝ p) =
      ∑ i ∈ t \ s, (p i - s.centroid ℝ p) := by
  classical
  have ht : t.Nonempty := hs.mono hst
  have hs0 : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr hs)
  have ht0 : (t.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr ht)
  have hsmean : (s.card : ℝ) • s.centroid ℝ p = ∑ i ∈ s, p i := by
    rw [finiteCentroid_eq_inv_card_smul_sum s p hs, smul_smul]
    simp [hs0]
  have htmean : (t.card : ℝ) • t.centroid ℝ p = ∑ i ∈ t, p i := by
    rw [finiteCentroid_eq_inv_card_smul_sum t p ht, smul_smul]
    simp [ht0]
  have hcard : (t.card : ℝ) = (s.card : ℝ) + ((t \ s).card : ℝ) := by
    have hcardNat : t.card = s.card + (t \ s).card := by
      have hdiff := Finset.card_sdiff_add_card_eq_card hst
      omega
    exact_mod_cast hcardNat
  have hsum : (∑ i ∈ t, p i) = (∑ i ∈ s, p i) + ∑ i ∈ t \ s, p i := by
    rw [← Finset.sum_sdiff hst]
    abel
  calc
    (t.card : ℝ) • (t.centroid ℝ p - s.centroid ℝ p) =
        (∑ i ∈ t, p i) - (t.card : ℝ) • s.centroid ℝ p := by
          rw [smul_sub, htmean]
    _ = ∑ i ∈ t \ s, (p i - s.centroid ℝ p) := by
      rw [hsum, hcard, add_smul, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Nat.cast_smul_eq_nsmul]
      rw [← hsmean]
      module

/-- Quantitative nested-face estimate. Each newly added vertex contributes
at most the parent face's pairwise distance bound. -/
theorem card_mul_dist_centroid_le
    {ι : Type u} {E : Type v}
    [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s t : Finset ι) (p : ι → E) (δ : ℝ)
    (hs : s.Nonempty) (hst : s ⊆ t)
    (hpair : ∀ i ∈ t, ∀ j ∈ t, dist (p i) (p j) ≤ δ) :
    (t.card : ℝ) * dist (t.centroid ℝ p) (s.centroid ℝ p) ≤
      ((t \ s).card : ℝ) * δ := by
  have hsum := card_smul_centroid_sub_eq_sum_sdiff s t p hs hst
  have hnorm : (t.card : ℝ) * dist (t.centroid ℝ p) (s.centroid ℝ p) =
      ‖∑ i ∈ t \ s, (p i - s.centroid ℝ p)‖ := by
    rw [← hsum, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), dist_eq_norm]
  rw [hnorm]
  calc
    ‖∑ i ∈ t \ s, (p i - s.centroid ℝ p)‖ ≤
        ∑ i ∈ t \ s, ‖p i - s.centroid ℝ p‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ t \ s, δ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← dist_eq_norm]
      exact dist_vertex_finiteCentroid_le_of_pairwise s t p δ hs hst hpair i
        (Finset.mem_sdiff.mp hi).1
    _ = ((t \ s).card : ℝ) * δ := by simp

end FairDivision.Topology.NerveConnectivity
