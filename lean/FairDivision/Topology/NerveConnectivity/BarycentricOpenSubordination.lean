import FairDivision.Topology.NerveConnectivity.BarycentricFiniteSourceMesh
import FairDivision.Topology.NerveConnectivity.BarycentricGeometricRealization
import FairDivision.Topology.NerveConnectivity.FiniteOpenCoverMesh

/-!
# Subordination of a finite geometric complex to an open cover

For a finite geometric simplicial complex and an open cover of its compact
geometric realization, sufficiently many barycentric subdivisions make
each geometric face lie in one cover member. The depth is common to all
faces; the selected cover member may vary by face.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v w

/-- A common iterated subdivision subordinate to an open cover of the
finite geometric realization. -/
theorem exists_barycentricSubdivision_subordinate_openCover
    {V : Type u} {E : Type v} {ι : Type w} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i))
    (hcover : geometricSimplicialRealization K p ⊆ ⋃ i, U i) :
    ∃ n : ℕ, ∀ (F : Finset (iteratedBarycentricVertex V n)),
      F ∈ iteratedBarycentricComplex K n →
      ∃ i, convexHull ℝ
        (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n)))
        ⊆ U i := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_smallSet_subordinate_to_openCover
    (geometricSimplicialRealization K p)
    (geometricSimplicialRealization_isCompact K p) U hU hcover
  obtain ⟨n, hmesh⟩ :=
    exists_iteratedBarycentric_finiteSourceMesh_lt K p δ hδ
  refine ⟨n, ?_⟩
  intro F hF
  let t : Set E := convexHull ℝ
    (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n)))
  have hFn : F.Nonempty :=
    ((iteratedBarycentricComplex K n).isRelLowerSet_faces hF).1
  obtain ⟨i, hi⟩ := hFn
  have htn : t.Nonempty := by
    refine ⟨iteratedBarycentricPoint p n i, ?_⟩
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  have hts : t ⊆ geometricSimplicialRealization K p := by
    intro x hx
    exact geometricIteratedBarycentric_subset K p n ⟨F, hF, hx⟩
  exact hsmall t htn hts (fun x hx y hy => hmesh F hF x y hx hy)

end FairDivision.Topology.NerveConnectivity
