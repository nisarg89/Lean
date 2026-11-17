import FairDivision.Topology.NerveConnectivity.BarycentricForwardInjective
import FairDivision.Topology.FiniteSimplexRestriction

/-!
# Removing a barycentric face from a subdivision point

The remaining positive face weights are normalized after the selected face is
removed. The resulting point stays in the same subdivided complex. This is
the reduction used in the injectivity proof for the canonical barycentric map.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- Normalize the remaining face weights after deleting `M`. -/
noncomputable def barycentricStrip {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1) :
    simplicialRealization (barycentricSubdivision K) := by
  classical
  let P : Finset (Finset V) := Finset.univ.erase M
  let w := FairDivision.Topology.finiteSimplexRestrict P ⟨z.1, hr⟩
  refine ⟨w, ?_⟩
  have hsub : FairDivision.Topology.finiteSimplexSupport w ⊆
      FairDivision.Topology.finiteSimplexSupport z.1 := by
    intro F hF
    exact (FairDivision.Topology.finiteSimplexRestrict_support_subset
      P ⟨z.1, hr⟩ F hF).1
  exact ((barycentricSubdivision K).isRelLowerSet_faces z.2).2 hsub
    (FairDivision.Topology.finiteSimplexSupport_nonempty w)

/-- Positive support after stripping is the old support without `M`. -/
theorem barycentricStrip_support {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1) :
    FairDivision.Topology.finiteSimplexSupport (barycentricStrip z M hr).1 =
      (FairDivision.Topology.finiteSimplexSupport z.1).erase M := by
  classical
  ext F
  rw [FairDivision.Topology.mem_finiteSimplexSupport_iff,
    Finset.mem_erase, FairDivision.Topology.mem_finiteSimplexSupport_iff]
  change 0 < (FairDivision.Topology.finiteSimplexRestrict
    ((Finset.univ : Finset (Finset V)).erase M) ⟨z.1, hr⟩).1 F ↔ _
  rw [FairDivision.Topology.finiteSimplexRestrict_pos_iff]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

/-- The weight of a face other than `M` is divided by the remaining mass. -/
theorem barycentricStrip_weight_of_ne {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M F : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1)
    (hFM : F ≠ M) :
    (barycentricStrip z M hr).1.1 F =
      z.1.1 F / FairDivision.Topology.finiteSimplexMass
        ((Finset.univ : Finset (Finset V)).erase M) z.1 := by
  classical
  simp [barycentricStrip, FairDivision.Topology.finiteSimplexRestrict,
    Finset.mem_erase, hFM]

/-- The erased face has zero weight. -/
theorem barycentricStrip_weight_self {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1) :
    (barycentricStrip z M hr).1.1 M = 0 := by
  classical
  simp [barycentricStrip, FairDivision.Topology.finiteSimplexRestrict]


/-- Removing one face subtracts its barycentric contribution, then
renormalizes the remaining forward coordinates. -/
theorem barycentricStrip_forward_identity {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1)
    (v : V) :
    FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1 *
        (barycentricForwardSimplex (barycentricStrip z M hr)).1 v =
      (barycentricForwardSimplex z).1 v -
        z.1.1 M * faceBaryWeight M v := by
  classical
  let P : Finset (Finset V) := Finset.univ.erase M
  let r : ℝ := FairDivision.Topology.finiteSimplexMass P z.1
  have hsum : (∑ F : Finset V, z.1.1 F * faceBaryWeight F v) =
      (∑ F ∈ P, z.1.1 F * faceBaryWeight F v) +
        z.1.1 M * faceBaryWeight M v := by
    simpa [P] using (Finset.sum_erase_add
      (Finset.univ : Finset (Finset V))
      (fun F => z.1.1 F * faceBaryWeight F v) (Finset.mem_univ M)).symm
  have hstrip : r * (∑ F : Finset V,
        (barycentricStrip z M hr).1.1 F * faceBaryWeight F v) =
      ∑ F ∈ P, z.1.1 F * faceBaryWeight F v := by
    rw [Finset.mul_sum]
    have hterm : ∀ F : Finset V,
        r * ((barycentricStrip z M hr).1.1 F * faceBaryWeight F v) =
          if F ∈ P then z.1.1 F * faceBaryWeight F v else 0 := by
      intro F
      by_cases hFM : F = M
      · subst F
        simp [P, barycentricStrip_weight_self z M hr]
      · have hFP : F ∈ P := by simp [P, hFM]
        rw [if_pos hFP, barycentricStrip_weight_of_ne z M F hr hFM]
        change r * ((z.1.1 F / r) * faceBaryWeight F v) = _
        have hrne : r ≠ 0 := ne_of_gt hr
        calc
          r * ((z.1.1 F / r) * faceBaryWeight F v) =
              (r * r⁻¹) * (z.1.1 F * faceBaryWeight F v) := by
                rw [div_eq_mul_inv]
                ring
          _ = z.1.1 F * faceBaryWeight F v := by
                rw [mul_inv_cancel₀ hrne, one_mul]
    simp_rw [hterm]
    exact Fintype.sum_ite_mem P (fun F => z.1.1 F * faceBaryWeight F v)
  change r * (∑ F : Finset V,
      (barycentricStrip z M hr).1.1 F * faceBaryWeight F v) =
    (∑ F : Finset V, z.1.1 F * faceBaryWeight F v) -
      z.1.1 M * faceBaryWeight M v
  rw [hstrip, hsum]
  ring


/-- If two points have the same forward image and the same selected face
weight, their normalized remainders have the same forward image. -/
theorem barycentricStrip_forward_eq {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z z' : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1)
    (hr' : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z'.1)
    (hforward : barycentricForwardSimplex z = barycentricForwardSimplex z')
    (hweight : z.1.1 M = z'.1.1 M) :
    barycentricForwardSimplex (barycentricStrip z M hr) =
      barycentricForwardSimplex (barycentricStrip z' M hr') := by
  have hmass : FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1 =
      FairDivision.Topology.finiteSimplexMass
        ((Finset.univ : Finset (Finset V)).erase M) z'.1 := by
    rw [barycentricMass_erase_eq, barycentricMass_erase_eq, hweight]
  apply Subtype.ext
  funext v
  have hleft := barycentricStrip_forward_identity z M hr v
  have hright := barycentricStrip_forward_identity z' M hr' v
  rw [← hmass, ← hforward, ← hweight] at hright
  exact (mul_left_cancel₀ (ne_of_gt hr)) (hleft.trans hright.symm)


/-- Zero remaining mass forces every other face weight to vanish. -/
theorem barycentric_zero_of_zero_remaining_mass {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M F : Finset V)
    (hzero : FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1 = 0)
    (hFM : F ≠ M) : z.1.1 F = 0 := by
  classical
  have hFP : F ∈ (Finset.univ : Finset (Finset V)).erase M := by
    simp [hFM]
  have hle : z.1.1 F ≤ FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1 := by
    unfold FairDivision.Topology.finiteSimplexMass
    exact Finset.single_le_sum (fun G _ => z.1.2.1 G) hFP
  exact le_antisymm (by simpa [hzero] using hle) (z.1.2.1 F)

/-- Stripping a positive face strictly reduces the number of positive
subdivision weights. -/
theorem barycentricStrip_support_card_lt {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K))
    (M : Finset V)
    (hM : M ∈ FairDivision.Topology.finiteSimplexSupport z.1)
    (hr : 0 < FairDivision.Topology.finiteSimplexMass
      ((Finset.univ : Finset (Finset V)).erase M) z.1) :
    (FairDivision.Topology.finiteSimplexSupport
      (barycentricStrip z M hr).1).card <
        (FairDivision.Topology.finiteSimplexSupport z.1).card := by
  rw [barycentricStrip_support]
  have hpos : 0 < (FairDivision.Topology.finiteSimplexSupport z.1).card :=
    Finset.card_pos.mpr ⟨M, hM⟩
  simpa [Finset.card_erase_of_mem hM] using
    Nat.pred_lt (Nat.ne_of_gt hpos)

end FairDivision.Topology.NerveConnectivity
