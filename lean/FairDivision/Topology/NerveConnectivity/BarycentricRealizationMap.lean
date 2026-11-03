import FairDivision.Topology.NerveConnectivity.BarycentricSubdivision
import Mathlib.Algebra.BigOperators.Field

/-!
# Forward realization map for barycentric subdivision

A barycentric vertex is a nonempty original face. Its image is the uniform
barycenter of that face. Averaging these barycenters with the subdivision
weights gives the canonical piecewise-linear map `|sd K| → |K|`.
The inverse and homeomorphism are separate obligations.
-/

set_option autoImplicit false

open scoped Topology Classical

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- The `v` coordinate of the uniform barycenter of a finite face `F`.
The empty face is assigned zero coordinatewise and receives no positive
weight in a valid subdivision point. -/
noncomputable def faceBaryWeight {V : Type v} (F : Finset V) (v : V) : ℝ :=
  if v ∈ F then (F.card : ℝ)⁻¹ else 0

@[simp] theorem faceBaryWeight_of_not_mem {V : Type v}
    (F : Finset V) (v : V) (hv : v ∉ F) :
    faceBaryWeight F v = 0 := by
  simp [faceBaryWeight, hv]

theorem faceBaryWeight_nonneg {V : Type v}
    (F : Finset V) (v : V) : 0 ≤ faceBaryWeight F v := by
  by_cases hv : v ∈ F
  · simp [faceBaryWeight, hv]
  · simp [faceBaryWeight, hv]

/-- The coordinates of a nonempty face barycenter sum to one. -/
theorem faceBaryWeight_sum {V : Type v} [Fintype V]
    (F : Finset V) (hF : F.Nonempty) :
    ∑ v : V, faceBaryWeight F v = 1 := by
  classical
  have hc : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hF
  simp [faceBaryWeight, Finset.sum_ite, hc]

/-- Affine barycentric coordinates in the original vertex set. -/
noncomputable def barycentricForwardWeight {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K)) (v : V) : ℝ :=
  ∑ F : Finset V, z.1.1 F * faceBaryWeight F v

/-- Every coordinate of the forward map is nonnegative. -/
theorem barycentricForwardWeight_nonneg {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K)) (v : V) :
    0 ≤ barycentricForwardWeight z v := by
  unfold barycentricForwardWeight
  apply Finset.sum_nonneg
  intro F _
  exact mul_nonneg (z.1.2.1 F) (faceBaryWeight_nonneg F v)

/-- The forward barycentric coordinates sum to one. -/
theorem barycentricForwardWeight_sum {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K)) :
    ∑ v : V, barycentricForwardWeight z v = 1 := by
  classical
  calc
    (∑ v : V, barycentricForwardWeight z v) =
        ∑ F : Finset V, z.1.1 F * (∑ v : V, faceBaryWeight F v) := by
      simp only [barycentricForwardWeight]
      rw [Finset.sum_comm]
      congr 1
      ext F
      rw [Finset.mul_sum]
    _ = ∑ F : Finset V, z.1.1 F := by
      apply Finset.sum_congr rfl
      intro F _
      by_cases hFpos : 0 < z.1.1 F
      · have hFface : F ∈ K :=
          z.2.2.1 F
            ((FairDivision.Topology.mem_finiteSimplexSupport_iff z.1 F).2 hFpos)
        rw [faceBaryWeight_sum F (K.isRelLowerSet_faces hFface).1, mul_one]
      · have hz : z.1.1 F = 0 :=
          le_antisymm (le_of_not_gt hFpos) (z.1.2.1 F)
        simp [hz]
    _ = 1 := z.1.2.2

/-- The canonical map from the subdivision realization to the ambient
probability simplex. -/
noncomputable def barycentricForwardSimplex {V : Type v} [Fintype V]
    {K : PreAbstractSimplicialComplex V}
    (z : simplicialRealization (barycentricSubdivision K)) :
    stdSimplex ℝ V :=
  ⟨barycentricForwardWeight z,
    barycentricForwardWeight_nonneg z,
    barycentricForwardWeight_sum z⟩

/-- The forward barycentric point lies in the original complex: its
support is contained in the greatest face of the supporting chain. -/
theorem barycentricForwardSimplex_mem {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (z : simplicialRealization (barycentricSubdivision K)) :
    barycentricForwardSimplex z ∈ simplicialRealization K := by
  let C := FairDivision.Topology.finiteSimplexSupport z.1
  have hC : C ∈ barycentricSubdivision K := z.2
  obtain ⟨M, hM, htop⟩ := finiteChain_exists_greatest C hC.1 hC.2.2
  have hMK : M ∈ K := hC.2.1 M hM
  change FairDivision.Topology.finiteSimplexSupport (barycentricForwardSimplex z) ∈ K
  have hsub : FairDivision.Topology.finiteSimplexSupport
      (barycentricForwardSimplex z) ⊆ M := by
    intro v hv
    by_contra hvM
    have hzero : ∀ F : Finset V, z.1.1 F * faceBaryWeight F v = 0 := by
      intro F
      by_cases hFpos : 0 < z.1.1 F
      · have hFC : F ∈ C :=
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
  exact (K.isRelLowerSet_faces hMK).2 hsub
    (FairDivision.Topology.finiteSimplexSupport_nonempty _)

/-- The affine barycentric map is continuous in all subdivision weights. -/
theorem barycentricForwardSimplex_continuous {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    Continuous (barycentricForwardSimplex (K := K)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun z : simplicialRealization (barycentricSubdivision K) =>
    ∑ F : Finset V, z.1.1 F * faceBaryWeight F v)
  apply continuous_finset_sum
  intro F _
  have hF : Continuous (fun z : simplicialRealization (barycentricSubdivision K) =>
      z.1.1 F) :=
    (continuous_apply F).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  exact hF.mul continuous_const

/-- Canonical continuous map from a subdivided finite complex to its original
probability-simplex realization. -/
noncomputable def barycentricForwardMap {V : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    C(simplicialRealization (barycentricSubdivision K),
      simplicialRealization K) :=
  ⟨fun z => ⟨barycentricForwardSimplex z,
      barycentricForwardSimplex_mem K z⟩,
    Continuous.subtype_mk (barycentricForwardSimplex_continuous K) _⟩

end FairDivision.Topology.NerveConnectivity
