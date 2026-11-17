import FairDivision.Topology.NerveConnectivity.FiniteSimplexGeometricRealization
import FairDivision.Topology.NerveConnectivity.BarycentricOpenSubordination

/-!
# Open-cover subordination for the probability-simplex realization

An ambient open cover of the finite probability-simplex realization has
a common barycentric subdivision whose entire geometric faces lie in
individual cover members.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Subordinate every geometric face of one common subdivision to an
ambient open cover of the existing probability-simplex realization. -/
theorem exists_finiteSimplexSubdivision_subordinate_ambientOpenCover
    {V : Type u} {ι : Type v} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (U : ι → Set (V → ℝ)) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ w : simplicialRealization K, ∃ i, w.1.1 ∈ U i) :
    ∃ n : ℕ, ∀ (F : Finset (iteratedBarycentricVertex V n)),
      F ∈ iteratedBarycentricComplex K n →
      ∃ i, convexHull ℝ
        (iteratedBarycentricPoint finiteSimplexUnitVertex n ''
          (F : Set (iteratedBarycentricVertex V n))) ⊆ U i := by
  apply exists_barycentricSubdivision_subordinate_openCover
    K finiteSimplexUnitVertex U hU
  intro x hx
  obtain ⟨w, hw⟩ := geometricUnitRealization_exists_simplexPoint K x hx
  obtain ⟨i, hi⟩ := hcover w
  exact Set.mem_iUnion.mpr ⟨i, by simpa [hw] using hi⟩

end FairDivision.Topology.NerveConnectivity
