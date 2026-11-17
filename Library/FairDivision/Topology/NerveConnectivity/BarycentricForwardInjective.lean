import FairDivision.Topology.NerveConnectivity.BarycentricInverseSimplex
import FairDivision.Topology.FiniteSimplexRestriction

/-!
# Injectivity of the barycentric forward map

The first step identifies the greatest positive subdivision face with
the positive support of its forward point. The full inverse-forward law
will follow by recovering and removing the greatest face weight
inductively along the supporting chain.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- A positive subdivision face contributes positive mass at each of
its original vertices. -/
theorem barycentricForward_pos_of_mem_face {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (F : Finset V) (hF : F ∈ FairDivision.Topology.finiteSimplexSupport z.1)
    {v : V} (hv : v ∈ F) :
    0 < (barycentricForwardSimplex z).1 v := by
  classical
  have hFpos : 0 < z.1.1 F :=
    (FairDivision.Topology.mem_finiteSimplexSupport_iff z.1 F).1 hF
  have hFn : F.Nonempty :=
    (K.isRelLowerSet_faces (z.2.2.1 F hF)).1
  have hcard : 0 < (F.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hFn
  have hbary : 0 < faceBaryWeight F v := by
    simp [faceBaryWeight, hv, inv_pos.mpr hcard]
  have hterm : 0 < z.1.1 F * faceBaryWeight F v :=
    mul_pos hFpos hbary
  change 0 < ∑ G : Finset V, z.1.1 G * faceBaryWeight G v
  exact Finset.sum_pos' (fun G _ =>
    mul_nonneg (z.1.2.1 G) (faceBaryWeight_nonneg G v))
    ⟨F, Finset.mem_univ F, hterm⟩

/-- The original positive support of a forward point is the greatest
face of the positive subdivision chain. -/
theorem barycentricForward_support_eq_greatest {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hM : M ∈ FairDivision.Topology.finiteSimplexSupport z.1)
    (htop : ∀ F ∈ FairDivision.Topology.finiteSimplexSupport z.1, F ⊆ M) :
    FairDivision.Topology.finiteSimplexSupport (barycentricForwardSimplex z) = M := by
  classical
  ext v
  constructor
  · intro hv
    by_contra hvM
    have hzero : ∀ F : Finset V, z.1.1 F * faceBaryWeight F v = 0 := by
      intro F
      by_cases hFpos : 0 < z.1.1 F
      · have hFC : F ∈ FairDivision.Topology.finiteSimplexSupport z.1 :=
          (FairDivision.Topology.mem_finiteSimplexSupport_iff z.1 F).2 hFpos
        have hvF : v ∉ F := fun hvF => hvM (htop F hFC hvF)
        simp [faceBaryWeight, hvF]
      · have hz : z.1.1 F = 0 :=
          le_antisymm (le_of_not_gt hFpos) (z.1.2.1 F)
        simp [hz]
    have hcoord : (barycentricForwardSimplex z).1 v = 0 := by
      simp [barycentricForwardSimplex, barycentricForwardWeight, hzero]
    have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff
      (barycentricForwardSimplex z) v).1 hv
    exact (ne_of_gt hpos) hcoord
  · intro hv
    exact (FairDivision.Topology.mem_finiteSimplexSupport_iff
      (barycentricForwardSimplex z) v).2
      (barycentricForward_pos_of_mem_face z M hM hv)

/-- A greatest face in a finite chain has a vertex belonging to no
other face of that chain. -/
theorem finiteChain_greatest_has_exclusive_vertex {V : Type v}
    (C : Finset (Finset V))
    (hchain : IsChain (· ⊆ ·) (C : Set (Finset V)))
    (M : Finset V) (hM : M ∈ C) (hMn : M.Nonempty)
    (htop : ∀ F ∈ C, F ⊆ M) :
    ∃ v ∈ M, ∀ F ∈ C, F ≠ M → v ∉ F := by
  classical
  let R := C.erase M
  by_cases hR : R.Nonempty
  · have hchainR : IsChain (· ⊆ ·) (R : Set (Finset V)) :=
      IsChain.mono (by
        intro F hF
        exact Finset.mem_of_mem_erase hF) hchain
    obtain ⟨N, hN, htopR⟩ := finiteChain_exists_greatest R hR hchainR
    have hNC : N ∈ C := Finset.mem_of_mem_erase hN
    have hNM : N ≠ M := (Finset.mem_erase.mp hN).1
    have hNsub : N ⊆ M := htop N hNC
    have hMnotSub : ¬ M ⊆ N := by
      intro hMsub
      exact hNM (Finset.Subset.antisymm hNsub hMsub)
    obtain ⟨v, hvM, hvN⟩ := Finset.not_subset.mp hMnotSub
    refine ⟨v, hvM, ?_⟩
    intro F hFC hFM hvF
    have hFR : F ∈ R := Finset.mem_erase.mpr ⟨hFM, hFC⟩
    exact hvN (htopR F hFR hvF)
  · have hR0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    obtain ⟨v, hvM⟩ := hMn
    refine ⟨v, hvM, ?_⟩
    intro F hFC hFM _
    have hFR : F ∈ R := Finset.mem_erase.mpr ⟨hFM, hFC⟩
    rw [hR0] at hFR
    simp at hFR

/-- At a vertex exclusive to the greatest positive face, only that
face contributes to the forward coordinate. -/
theorem barycentricForward_exclusive_coordinate {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V) (v : V) (hvM : v ∈ M)
    (hexcl : ∀ F ∈ FairDivision.Topology.finiteSimplexSupport z.1,
      F ≠ M → v ∉ F) :
    (barycentricForwardSimplex z).1 v =
      z.1.1 M * (M.card : ℝ)⁻¹ := by
  classical
  change (∑ F : Finset V, z.1.1 F * faceBaryWeight F v) = _
  have hsum : (∑ F : Finset V, z.1.1 F * faceBaryWeight F v) =
      z.1.1 M * faceBaryWeight M v := by
    apply Finset.sum_eq_single M
    · intro F _ hFM
      by_cases hFpos : 0 < z.1.1 F
      · have hFC : F ∈ FairDivision.Topology.finiteSimplexSupport z.1 :=
          (FairDivision.Topology.mem_finiteSimplexSupport_iff z.1 F).2 hFpos
        have hvF : v ∉ F := hexcl F hFC hFM
        simp [faceBaryWeight, hvF]
      · have hz : z.1.1 F = 0 :=
          le_antisymm (le_of_not_gt hFpos) (z.1.2.1 F)
        simp [hz]
    · simp
  simpa [faceBaryWeight, hvM] using hsum

/-- The smallest forward coordinate on the greatest positive face
recovers its barycentric coefficient divided by its cardinality. -/
theorem barycentricForward_min_greatest {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hM : M ∈ FairDivision.Topology.finiteSimplexSupport z.1)
    (htop : ∀ F ∈ FairDivision.Topology.finiteSimplexSupport z.1, F ⊆ M) :
    faceInsideMin M (barycentricForwardSimplex z) =
      z.1.1 M * (M.card : ℝ)⁻¹ := by
  classical
  have hMn : M.Nonempty :=
    (K.isRelLowerSet_faces (z.2.2.1 M hM)).1
  have hchain : IsChain (· ⊆ ·)
      ((FairDivision.Topology.finiteSimplexSupport z.1 : Finset (Finset V)) :
        Set (Finset V)) := z.2.2.2
  obtain ⟨v, hvM, hexcl⟩ := finiteChain_greatest_has_exclusive_vertex
    (FairDivision.Topology.finiteSimplexSupport z.1) hchain M hM hMn htop
  have hlower : ∀ w ∈ M,
      z.1.1 M * (M.card : ℝ)⁻¹ ≤ (barycentricForwardSimplex z).1 w := by
    intro w hwM
    have hbary : faceBaryWeight M w = (M.card : ℝ)⁻¹ := by
      simp [faceBaryWeight, hwM]
    have hbound : z.1.1 M * faceBaryWeight M w ≤
        barycentricForwardWeight z w := by
      unfold barycentricForwardWeight
      exact Finset.single_le_sum
        (fun F _ => mul_nonneg (z.1.2.1 F) (faceBaryWeight_nonneg F w))
        (Finset.mem_univ M)
    simpa only [hbary, barycentricForwardSimplex] using hbound
  have hlowerMin : z.1.1 M * (M.card : ℝ)⁻¹ ≤
      faceInsideMin M (barycentricForwardSimplex z) := by
    rw [faceInsideMin, dif_pos hMn]
    apply (Finset.le_inf'_iff hMn
      (fun w => (barycentricForwardSimplex z).1 w)).2
    exact hlower
  apply le_antisymm
  · calc
      faceInsideMin M (barycentricForwardSimplex z) ≤
          (barycentricForwardSimplex z).1 v :=
        faceInsideMin_le M (barycentricForwardSimplex z) hvM
      _ = z.1.1 M * (M.card : ℝ)⁻¹ :=
        barycentricForward_exclusive_coordinate z M v hvM hexcl
  · exact hlowerMin

/-- The inverse-coordinate formula recovers the weight of the
greatest positive subdivision face. -/
theorem barycentricInverseWeight_greatest {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hM : M ∈ FairDivision.Topology.finiteSimplexSupport z.1)
    (htop : ∀ F ∈ FairDivision.Topology.finiteSimplexSupport z.1, F ⊆ M) :
    faceInverseWeight M (barycentricForwardSimplex z) = z.1.1 M := by
  have hMn : M.Nonempty :=
    (K.isRelLowerSet_faces (z.2.2.1 M hM)).1
  have hcard : (M.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hMn
  have hOutside : faceOutsideMax M (barycentricForwardSimplex z) = 0 := by
    have hs := barycentricForward_support_eq_greatest z M hM htop
    rw [← hs]
    exact faceOutsideMax_support_eq_zero (barycentricForwardSimplex z)
  have hMin := barycentricForward_min_greatest z M hM htop
  have hnonneg : 0 ≤ z.1.1 M * (M.card : ℝ)⁻¹ :=
    mul_nonneg (z.1.2.1 M) (inv_nonneg.mpr (by positivity))
  unfold faceInverseWeight
  rw [hMin, hOutside, sub_zero, max_eq_right hnonneg]
  calc
    (M.card : ℝ) * (z.1.1 M * (M.card : ℝ)⁻¹) =
      z.1.1 M * ((M.card : ℝ) * (M.card : ℝ)⁻¹) := by ring
    _ = z.1.1 M := by rw [mul_inv_cancel₀ hcard, mul_one]

/-- The mass remaining after deleting one subdivision face is one
minus that face's weight. -/
theorem barycentricMass_erase_eq {V : Type v} [Fintype V]
    (z : stdSimplex ℝ (Finset V)) (M : Finset V) :
    FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z = 1 - z.1 M := by
  classical
  have hsum := Finset.sum_erase_add
    (Finset.univ : Finset (Finset V)) (fun F => z.1 F) (Finset.mem_univ M)
  change ((Finset.univ : Finset (Finset V)).erase M).sum (fun F => z.1 F) =
    1 - z.1 M
  have htotal : (Finset.univ : Finset (Finset V)).sum (fun F => z.1 F) = 1 :=
    z.2.2
  linarith

end FairDivision.Topology.NerveConnectivity
