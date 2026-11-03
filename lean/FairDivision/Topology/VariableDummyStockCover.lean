import FairDivision.Topology.VariableDummyStock
import FairDivision.Topology.NerveConnectivity.SimplicialCover

/-!
# The item-restricted cover for an arbitrary real stock

This is the cover used at every stage of the BF connectivity induction. Its
ambient complex permits only real labels from `E`; its pieces additionally
permit one chosen item to appear only at the indexed position.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A finite simplicial cover of the auxiliary complex restricted to real
stock `E`, indexed by the positions with positive requirements. -/
noncomputable def variableStockItemFiniteCover {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (hSome : ∃ a : Fin k, 0 < r a) :
    NerveConnectivity.FiniteSubcomplexCover
      {a : Fin k // 0 < r a} (VariableUnlabeledVertex k m D r c) := by
  classical
  refine {
    ambient := variableStockComplex D E r c
    pieces := fun a => variableStockComplex D E r c ⊓
      variableItemCoverComplex D r c e a.1
    piece_le := ?_
    covers := ?_ }
  · intro a S hS
    exact hS.1
  · intro S hS
    obtain ⟨a, hra, hOnly⟩ :=
      variableFace_mem_item_cover e hSome S hS.1.2
    exact ⟨⟨a, hra⟩, ⟨hS, ⟨hS.1, hOnly⟩⟩⟩

/-- A face belongs to two distinct cover members exactly when it belongs to
the complex whose real stock has the fixed item removed. -/
theorem variableStockItem_two_iff_erase {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (a b : Fin k) (hab : a ≠ b)
    (S : Finset (VariableUnlabeledVertex k m D r c)) :
    (S ∈ variableStockComplex D E r c ⊓
        variableItemCoverComplex D r c e a ∧
      S ∈ variableStockComplex D E r c ⊓
        variableItemCoverComplex D r c e b) ↔
      S ∈ variableStockComplex D (E.erase e) r c := by
  rw [variableStockComplex_erase_iff_absent D E r c e S]
  constructor
  · intro h
    have hA : VariableItemOnlyAt S e a := h.1.2.2
    have hB : VariableItemOnlyAt S e b := h.2.2.2
    exact ⟨h.1.1, (variableItemOnlyAt_two_iff_absent S e a b hab).1
      ⟨hA, hB⟩⟩
  · intro h
    have hOnlyA : VariableItemOnlyAt S e a :=
      fun i _ => h.2 i
    have hOnlyB : VariableItemOnlyAt S e b :=
      fun i _ => h.2 i
    exact ⟨⟨h.1, ⟨h.1.1, hOnlyA⟩⟩,
      ⟨h.1, ⟨h.1.1, hOnlyB⟩⟩⟩

end FairDivision.Topology
