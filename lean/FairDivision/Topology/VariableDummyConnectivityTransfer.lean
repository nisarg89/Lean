import FairDivision.Topology.VariableDummySaturationHomeomorph
import FairDivision.Topology.VariableDummyForceHomeomorph
import FairDivision.Topology.NerveConnectivity.NullHomotopy

/-!
# Connectivity transfer across the BF manuscript reductions

The actual induction applies these lemmas after reducing the auxiliary
complex. They combine the manuscript's deformation retractions with the
homeomorphisms that identify their images as smaller auxiliary complexes.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- The saturation branch transfers operational connectivity from the
no-dummy reduced auxiliary complex to the original stock complex. -/
theorem variableStock_nullConnected_of_saturation {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (hED : Disjoint E D)
    (p0 : VariableUnlabeledVertex k m D r c)
    (j : ℕ)
    (hReduced : NullConnectedSet j
      (simplicialRealization
        (variableStockComplex (∅ : Finset (Fin m)) E
          (fun i => r i - u i) (fun _ => 0)))) :
    NullConnectedSet j (simplicialRealization
      (variableStockComplex D E r c)) := by
  have hSat : NullConnectedSet j
      (simplicialRealization (variableSaturatedComplex D E r c u)) :=
    NullConnectedSpace.ofHomotopyEquiv
      (variableSaturated_reduced_homeomorph u huR huC hBudget
        hBound hED p0).symm.toHomotopyEquiv hReduced
  exact NullConnectedSpace.ofHomotopyEquiv
    (variableSaturation_homotopyEquiv u huR huC hBudget hBound).symm
    hSat

/-- The forced-item branch transfers operational connectivity from the
item-deleted auxiliary complex to one cover member. -/
theorem variableStockCover_nullConnected_of_forcing {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (p0 : VariableUnlabeledVertex k m D r c)
    (q0 : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
    (j : ℕ)
    (hReduced : NullConnectedSet j
      (simplicialRealization
        (variableStockComplex D (E.erase e)
          (variableDecreasedRequirement r a) c))) :
    NullConnectedSet j
      (simplicialRealization
        (variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a)) := by
  have hForced : NullConnectedSet j
      (simplicialRealization
        (variableForcedItemComplex D E r c e a)) :=
    NullConnectedSpace.ofHomotopyEquiv
      (variableForced_reduced_homeomorph e heD heE a hra
        p0 q0).symm.toHomotopyEquiv hReduced
  exact NullConnectedSpace.ofHomotopyEquiv
    (variableForceItem_homotopyEquiv e heD heE a hra).symm
    hForced

/-- Nonemptiness transfers across the saturation reduction even when the
connectivity slack is zero. -/
theorem variableStock_nonempty_of_saturation {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (hED : Disjoint E D)
    (p0 : VariableUnlabeledVertex k m D r c)
    (hReduced : Nonempty
      (simplicialRealization
        (variableStockComplex (∅ : Finset (Fin m)) E
          (fun i => r i - u i) (fun _ => 0)))) :
    Nonempty (simplicialRealization (variableStockComplex D E r c)) := by
  let hHome := variableSaturated_reduced_homeomorph u huR huC
    hBudget hBound hED p0
  let hRet := variableSaturation_homotopyEquiv
    (D := D) (E := E) (r := r) (c := c) u huR huC hBudget hBound
  exact ⟨hRet.invFun (hHome.symm (Classical.choice hReduced))⟩

/-- Nonemptiness transfers from the item-deleted auxiliary complex to a
cover member even when the connectivity slack is zero. -/
theorem variableStockCover_nonempty_of_forcing {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (p0 : VariableUnlabeledVertex k m D r c)
    (q0 : VariableUnlabeledVertex k m D
      (variableDecreasedRequirement r a) c)
    (hReduced : Nonempty
      (simplicialRealization
        (variableStockComplex D (E.erase e)
          (variableDecreasedRequirement r a) c))) :
    Nonempty
      (simplicialRealization
        (variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a)) := by
  let hHome := variableForced_reduced_homeomorph e heD heE a hra p0 q0
  let hRet := variableForceItem_homotopyEquiv
    (D := D) (E := E) (r := r) (c := c) e heD heE a hra
  exact ⟨hRet.invFun (hHome.symm (Classical.choice hReduced))⟩

end FairDivision.Topology
