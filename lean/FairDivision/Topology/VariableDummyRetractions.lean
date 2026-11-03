import FairDivision.Topology.VariableDummySimplicialRetraction
import FairDivision.Topology.VariableDummySaturatedSubcomplex
import FairDivision.Topology.VariableDummyForcedSubcomplex

/-!
# The two BF deformation retractions

These are the realization-level versions of the two explicit vertex
operations in the manuscript's connectivity induction: dummy saturation
when all useful dummies fit, and forcing a selected real item in one member
of the item cover.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- Dummy saturation gives a homotopy equivalence from the stock-restricted
auxiliary complex to its saturated-dummy subcomplex. -/
noncomputable def variableSaturation_homotopyEquiv {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i) :
    ContinuousMap.HomotopyEquiv
      (simplicialRealization (variableStockComplex D E r c))
      (simplicialRealization (variableSaturatedComplex D E r c u)) := by
  apply variableRealizationRetraction_homotopyEquiv
    (variableStockComplex D E r c)
    (variableSaturatedComplex D E r c u)
    (variableSaturatedComplex_le_stock D E r c u)
    (saturateVariableVertex u huR huC hBudget hBound)
  · intro S hS
    exact variableFace_union_saturation_in_stock
      u huR huC hBudget hBound S hS
  · intro S hS
    exact saturateVariableVertex_image_mem_saturated
      u huR huC hBudget hBound S hS
  · intro S hS p hp
    exact saturateVariableVertex_fixed_on_saturated
      u huR huC hBudget hBound S hS p hp

/-- Forcing `e` into position `a` gives a homotopy equivalence from that
stock-restricted cover member to its fixed-item subcomplex. -/
noncomputable def variableForceItem_homotopyEquiv {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a) :
    ContinuousMap.HomotopyEquiv
      (simplicialRealization
        (variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a))
      (simplicialRealization
        (variableForcedItemComplex D E r c e a)) := by
  apply variableRealizationRetraction_homotopyEquiv
    (variableStockComplex D E r c ⊓
      variableItemCoverComplex D r c e a)
    (variableForcedItemComplex D E r c e a)
    (variableForcedItemComplex_le_cover D E r c e a)
    (variableForceVertex e heD a hra)
  · intro S hS
    exact variableForceVertex_contiguous_in_stockCover
      e heD heE a hra S hS.1 hS.2.2
  · intro S hS
    exact variableForceVertex_image_mem_forced
      e heD heE a hra S hS
  · intro S hS p hp
    exact variableForceVertex_fixed_on_forced
      e heD a hra S hS p hp

end FairDivision.Topology
