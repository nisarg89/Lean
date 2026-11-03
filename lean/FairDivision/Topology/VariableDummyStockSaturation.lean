import FairDivision.Topology.VariableDummyStock
import FairDivision.Topology.VariableDummySaturation

/-!
# Dummy saturation inside a restricted real stock

The saturation map only removes real items from each position. Therefore its
contiguity with the identity holds in every restricted-stock subcomplex as
well as in the unrestricted auxiliary complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The original face and its dummy-saturated image form a face in the same
restricted-stock complex. -/
theorem variableFace_union_saturation_in_stock {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : S ∈ variableStockComplex D E r c) :
    S ∪ S.image (saturateVariableVertex u huR huC hBudget hBound) ∈
      variableStockComplex D E r c := by
  classical
  obtain ⟨p, hp⟩ := hS.1.1
  have hFace := variableFace_union_saturation
    u huR huC hBudget hBound S hS.1.2
  refine ⟨⟨⟨p, Finset.mem_union_left _ hp⟩, hFace⟩, ?_⟩
  intro q hq i
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hS.2 q hq i
  · obtain ⟨p', hp', hImage⟩ := Finset.mem_image.mp hq
    rw [← hImage]
    exact ((saturateVariableVertex_spec
      u huR huC hBudget hBound p' i).1).trans (hS.2 p' hp' i)

end FairDivision.Topology
