import FairDivision.Topology.VariableDummyStockSaturation

/-!
# The dummy-saturated subcomplex

When the dummy stock is large enough, the manuscript retracts the auxiliary
complex onto the subcomplex in which every position has its maximum useful
dummy count. This file packages that image as a genuine simplicial
subcomplex and proves the face-level retraction properties.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Faces with target dummy count `u i` at every position of every vertex. -/
def variableSaturatedComplex {k m : ℕ}
    (D E : Finset (Fin m)) (r c u : Fin k → ℕ) :
    PreAbstractSimplicialComplex (VariableUnlabeledVertex k m D r c) where
  faces := {S | S ∈ variableStockComplex D E r c ∧
    ∀ p ∈ S, ∀ i : Fin k, (p.1 i).2 = u i}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨(variableStockComplex D E r c).isRelLowerSet_faces hS.1 |>.1, ?_⟩
    intro T hTS hT
    refine ⟨((variableStockComplex D E r c).isRelLowerSet_faces hS.1).2
      hTS hT, ?_⟩
    intro p hp i
    exact hS.2 p (hTS hp) i

/-- The saturated subcomplex lies in its stock-restricted ambient complex. -/
theorem variableSaturatedComplex_le_stock {k m : ℕ}
    (D E : Finset (Fin m)) (r c u : Fin k → ℕ) :
    variableSaturatedComplex D E r c u ≤
      variableStockComplex D E r c :=
  fun _ hS => hS.1

/-- Saturating every vertex of a stock-restricted face gives a face of the
saturated subcomplex. -/
theorem saturateVariableVertex_image_mem_saturated {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hStock : S ∈ variableStockComplex D E r c) :
    S.image (saturateVariableVertex u huR huC hBudget hBound) ∈
      variableSaturatedComplex D E r c u := by
  classical
  have hUnion := variableFace_union_saturation_in_stock
    u huR huC hBudget hBound S hStock
  have hSub : S.image
      (saturateVariableVertex u huR huC hBudget hBound) ⊆
      S ∪ S.image
        (saturateVariableVertex u huR huC hBudget hBound) :=
    Finset.subset_union_right
  have hStockImage :=
    ((variableStockComplex D E r c).isRelLowerSet_faces hUnion).2
      hSub (Finset.image_nonempty.mpr hStock.1.1)
  refine ⟨hStockImage, ?_⟩
  intro p hp i
  obtain ⟨q, _, hqp⟩ := Finset.mem_image.mp hp
  rw [← hqp]
  exact (saturateVariableVertex_spec
    u huR huC hBudget hBound q i).2

/-- Saturation fixes every vertex already in the target subcomplex. -/
theorem saturateVariableVertex_fixed_on_saturated {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hSat : S ∈ variableSaturatedComplex D E r c u)
    (p : VariableUnlabeledVertex k m D r c) (hp : p ∈ S) :
    saturateVariableVertex u huR huC hBudget hBound p = p :=
  saturateVariableVertex_eq_of_saturated
    u huR huC hBudget hBound p (hSat.2 p hp)

end FairDivision.Topology
