import FairDivision.Topology.NerveConnectivity.BarycentricMeshIteration
import FairDivision.Topology.NerveConnectivity.BarycentricMeshStep
import Mathlib.Analysis.Convex.Topology

/-!
# Geometric sets underlying barycentric subdivisions

The geometric realization is the union of face convex hulls. Each
subdivided face is contained in an original face, so iterated subdivision
never leaves the original compact geometric set.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Geometric realization of an abstract complex with assigned vertex
points in a real normed vector space. -/
def geometricSimplicialRealization
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) : Set E :=
  {x | ∃ F : Finset V, F ∈ K ∧ x ∈ convexHull ℝ (p '' (F : Set V))}

/-- A finite-vertex geometric realization is compact. -/
theorem geometricSimplicialRealization_isCompact
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) :
    IsCompact (geometricSimplicialRealization K p) := by
  classical
  let faces : Finset (Finset V) := Finset.univ.filter (fun F => F ∈ K)
  have hcompact : IsCompact
      (⋃ F ∈ faces, convexHull ℝ (p '' (F : Set V))) := by
    apply faces.isCompact_biUnion
    intro F _
    exact (F.finite_toSet.image p).isCompact_convexHull ℝ
  convert hcompact using 1
  ext x
  simp [geometricSimplicialRealization, faces]

/-- A geometric barycentric simplex stays inside a single face of the
original complex. -/
theorem geometricBarycentricSubdivision_subset
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) :
    geometricSimplicialRealization (barycentricSubdivision K)
      (fun F : Finset V => F.centroid ℝ p) ⊆
      geometricSimplicialRealization K p := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := hx
  obtain ⟨M, hM, htop⟩ := finiteChain_exists_greatest C hC.1 hC.2.2
  have hMK : M ∈ K := hC.2.1 M hM
  refine ⟨M, hMK, ?_⟩
  apply (convexHull_min ?_ (convex_convexHull ℝ _)) hxC
  intro y hy
  obtain ⟨F, hFC, rfl⟩ := hy
  exact finiteCentroid_mem_convexHull_of_subset F M p
    (K.isRelLowerSet_faces (hC.2.1 F hFC)).1 (htop F hFC)

/-- Every iterated geometric subdivision stays inside the original
geometric realization. -/
theorem geometricIteratedBarycentric_subset
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E) :
    ∀ n : ℕ,
      geometricSimplicialRealization (iteratedBarycentricComplex K n)
        (iteratedBarycentricPoint p n) ⊆ geometricSimplicialRealization K p := by
  intro n
  induction n with
  | zero =>
      exact Set.Subset.rfl
  | succ n ih =>
      exact (geometricBarycentricSubdivision_subset
        (iteratedBarycentricComplex K n)
        (iteratedBarycentricPoint p n)).trans ih

end FairDivision.Topology.NerveConnectivity
