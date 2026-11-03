import FairDivision.Topology.NerveConnectivity.FiniteSimplexOpenSubordination
import FairDivision.Topology.NerveConnectivity.BarycentricIteratedRealization

/-!
# Subordination to relatively open covers of a simplicial realization

An open set in the probability-simplex realization lifts through its two
subtype layers to an ambient open set of coordinate vectors. The geometric
subordination theorem then controls every realized point whose support
lies in a face of one common barycentric subdivision.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

private theorem exists_ambientOpen_lift
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (U : Set (simplicialRealization K)) (hU : IsOpen U) :
    ∃ O : Set (V → ℝ), IsOpen O ∧
      ∀ w : simplicialRealization K, w ∈ U ↔ w.1.1 ∈ O := by
  obtain ⟨W, hW, hUW⟩ := isOpen_induced_iff.mp hU
  obtain ⟨O, hO, hWO⟩ := isOpen_induced_iff.mp hW
  refine ⟨O, hO, ?_⟩
  intro w
  calc
    w ∈ U ↔ w.1 ∈ W := by
      exact Iff.of_eq (congrArg (fun A : Set (simplicialRealization K)=>w∈A) hUW.symm)
    _ ↔ w.1.1 ∈ O := by
      exact Iff.of_eq (congrArg (fun A : Set (stdSimplex ℝ V)=>w.1∈A) hWO.symm)

/-- One common subdivision subordinates every realized simplex to one
member of a relatively open cover of the original realization. -/
theorem exists_finiteSimplexSubdivision_subordinate_relativeOpenCover
    {V : Type u} {ι : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (U : ι → Set (simplicialRealization K))
    (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ w : simplicialRealization K, ∃ i, w ∈ U i) :
    ∃ n : ℕ, ∀ (F : Finset (iteratedBarycentricVertex V n)),
      (hF : F ∈ iteratedBarycentricComplex K n) →
      ∃ i, ∀ z : simplicialRealization (iteratedBarycentricComplex K n),
        FairDivision.Topology.finiteSimplexSupport z.1 ⊆ F →
        iteratedBarycentricRealizationHomeomorph K n z ∈ U i := by
  classical
  let lift (i : ι) := exists_ambientOpen_lift K (U i) (hU i)
  let O : ι → Set (V → ℝ) := fun i => Classical.choose (lift i)
  have hO : ∀ i, IsOpen (O i) := fun i => (Classical.choose_spec (lift i)).1
  have hmem : ∀ i (w : simplicialRealization K),
      w ∈ U i ↔ w.1.1 ∈ O i :=
    fun i w => (Classical.choose_spec (lift i)).2 w
  have hambientCover : ∀ w : simplicialRealization K,
      ∃ i, w.1.1 ∈ O i := by
    intro w
    obtain ⟨i, hi⟩ := hcover w
    exact ⟨i, (hmem i w).1 hi⟩
  obtain ⟨n, hfaces⟩ :=
    exists_finiteSimplexSubdivision_subordinate_ambientOpenCover
      K O hO hambientCover
  refine ⟨n, ?_⟩
  intro F hF
  obtain ⟨i, hface⟩ := hfaces F hF
  refine ⟨i, ?_⟩
  intro z hsupport
  have hFn : F.Nonempty :=
    ((iteratedBarycentricComplex K n).isRelLowerSet_faces hF).1
  have hgeom := finiteSimplexAffinePoint_mem_convexHull
    (iteratedBarycentricPoint finiteSimplexUnitVertex n) z.1
    F hFn hsupport
  have hcoord : (iteratedBarycentricRealizationHomeomorph K n z).1.1 ∈ O i := by
    have hsmall := hface hgeom
    have htransport := finiteSimplexAffinePoint_iteratedBarycentric
      K finiteSimplexUnitVertex n z
    rw [← htransport, finiteSimplexAffinePoint_unitVertices] at hsmall
    exact hsmall
  exact (hmem i (iteratedBarycentricRealizationHomeomorph K n z)).2 hcoord

end FairDivision.Topology.NerveConnectivity
