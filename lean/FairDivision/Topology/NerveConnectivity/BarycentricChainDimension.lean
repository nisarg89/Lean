import FairDivision.Topology.NerveConnectivity.BarycentricSubdivision
import Mathlib.Data.Finset.Card

/-!
# Dimension does not grow under barycentric subdivision

A chain of nonempty subsets of an `N`-element set has at most `N` members:
cardinality is an injective rank on a chain. This preserves a fixed mesh
contraction factor through arbitrarily many subdivisions.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe v

/-- An abstract nonempty subset chain has no more members than the largest
allowed subset cardinality. -/
theorem finiteChain_card_le_of_faceCard_le
    {V : Type v}
    (C : Finset (Finset V)) (N : ℕ)
    (hchain : IsChain (· ⊆ ·) (C : Set (Finset V)))
    (hfaces : ∀ F ∈ C, F.Nonempty ∧ F.card ≤ N) :
    C.card ≤ N := by
  classical
  let R : Finset ℕ := Finset.Icc 1 N
  have hmap : Set.MapsTo Finset.card (C : Set (Finset V)) R := by
    intro F hF
    have h := hfaces F hF
    exact Finset.mem_Icc.mpr ⟨Finset.one_le_card.mpr h.1, h.2⟩
  have hinj : Set.InjOn Finset.card (C : Set (Finset V)) := by
    intro F hF G hG hcard
    rcases hchain.total hF hG with hFG | hGF
    · exact Finset.eq_of_subset_of_card_le hFG (le_of_eq hcard.symm)
    · exact (Finset.eq_of_subset_of_card_le hGF (le_of_eq hcard)).symm
  have h := Finset.card_le_card_of_injOn Finset.card hmap hinj
  simpa [R] using h

/-- Every face in a barycentric subdivision has no more vertices than
any fixed cardinality bound for original faces. -/
theorem barycentricSubdivision_faceCard_le
    {V : Type v}
    (K : PreAbstractSimplicialComplex V) (N : ℕ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (C : Finset (Finset V)) (hC : C ∈ barycentricSubdivision K) :
    C.card ≤ N := by
  classical
  apply finiteChain_card_le_of_faceCard_le C N hC.2.2
  intro F hF
  have hFK : F ∈ K := hC.2.1 F hF
  exact ⟨(K.isRelLowerSet_faces hFK).1, hsize F hFK⟩

end FairDivision.Topology.NerveConnectivity
