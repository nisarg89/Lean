import FairDivision.Topology.VariableDummyStockCover
import FairDivision.Topology.VariableDummyStockRealization

/-!
# Intersections in the real-item cover

The manuscript observes that an intersection of at least two distinct cover
members forbids the selected real item at every position. This identifies
all such intersections with one smaller stock-restricted complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open NerveConnectivity

/-- A one-member intersection is its cover member. -/
theorem variableStockItem_coverIntersection_singleton {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) (e : Fin m)
    (a : {a : Fin k // 0 < r a}) :
    coverIntersection
      (fun b : {a : Fin k // 0 < r a} =>
        simplicialRealization
          (variableStockComplex D E r c ⊓
            variableItemCoverComplex D r c e b.1)) ({a} : Finset _) =
      simplicialRealization
        (variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a.1) := by
  ext lot
  simp [coverIntersection]

/-- An allocation that never uses `e` lies in every item-cover member. -/
theorem variableStockItem_erase_subset_piece {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) (e : Fin m)
    (a : Fin k) :
    simplicialRealization (variableStockComplex D (E.erase e) r c) ⊆
      simplicialRealization
        (variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a) := by
  intro lot hlot
  have hErase := (variableStockComplex_erase_iff_absent
    D E r c e (finiteSimplexSupport lot)).1 hlot
  exact ⟨hErase.1, ⟨hErase.1.1, fun j _ => hErase.2 j⟩⟩

/-- A point of the erased-stock realization is common to every cover member. -/
theorem variableStockItem_commonPoint_of_erase_nonempty {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) (e : Fin m)
    (h : Nonempty
      (simplicialRealization (variableStockComplex D (E.erase e) r c))) :
    HasCommonPoint
      (fun a : {a : Fin k // 0 < r a} =>
        simplicialRealization
          (variableStockComplex D E r c ⊓
            variableItemCoverComplex D r c e a.1)) := by
  obtain ⟨⟨lot, hlot⟩⟩ := h
  refine ⟨lot, ?_⟩
  intro a
  exact variableStockItem_erase_subset_piece D E r c e a.1 hlot

/-- Every intersection of two or more distinct cover members is precisely
the complex with `e` removed from the real stock. -/
theorem variableStockItem_coverIntersection_eq_erase {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) (e : Fin m)
    (J : Finset {a : Fin k // 0 < r a}) (hJ : 2 ≤ J.card) :
    coverIntersection
      (fun a : {a : Fin k // 0 < r a} =>
        simplicialRealization
          (variableStockComplex D E r c ⊓
            variableItemCoverComplex D r c e a.1)) J =
      simplicialRealization (variableStockComplex D (E.erase e) r c) := by
  classical
  ext lot
  constructor
  · intro hlot
    obtain ⟨a, b, ha, hb, hab⟩ :=
      Finset.one_lt_card_iff.mp (by omega : 1 < J.card)
    have hA : finiteSimplexSupport lot ∈
        variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e a.1 :=
      Set.mem_iInter.mp (Set.mem_iInter.mp hlot a) ha
    have hB : finiteSimplexSupport lot ∈
        variableStockComplex D E r c ⊓
          variableItemCoverComplex D r c e b.1 :=
      Set.mem_iInter.mp (Set.mem_iInter.mp hlot b) hb
    have hab' : a.1 ≠ b.1 := by
      intro h
      exact hab (Subtype.ext h)
    exact (variableStockItem_two_iff_erase D E r c e a.1 b.1
      hab' (finiteSimplexSupport lot)).1 ⟨hA, hB⟩
  · intro hlot
    have hErase := (variableStockComplex_erase_iff_absent
      D E r c e (finiteSimplexSupport lot)).1 hlot
    apply Set.mem_iInter.mpr
    intro a
    apply Set.mem_iInter.mpr
    intro _
    exact ⟨hErase.1, ⟨hErase.1.1,
      fun j _ => hErase.2 j⟩⟩

end FairDivision.Topology
