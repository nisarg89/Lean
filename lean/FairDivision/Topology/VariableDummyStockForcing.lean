import FairDivision.Topology.VariableDummyForcingMap
import FairDivision.Topology.VariableDummyStock

/-!
# Forced-item retraction inside a restricted real stock

The forced-item vertex map preserves a stock-restricted cover member when the
forced item belongs to that stock. The union of a face and its image remains
inside the same cover member, providing the simplicial contiguity needed for
the geometric deformation retraction.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The forced-item operation preserves a real-stock restriction. -/
theorem variableForceVertex_realWithin {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (hWithin : ∀ i : Fin k, (p.1 i).1 ⊆ E)
    (i : Fin k) :
    ((variableForceVertex e heD a hra p).1 i).1 ⊆ E := by
  intro g hg
  have hsub := (variableForceVertex_bounds e heD a hra p).1 i hg
  by_cases hi : i = a
  · rw [if_pos hi] at hsub
    rcases Finset.mem_insert.mp hsub with rfl | hOld
    · exact heE
    · exact hWithin i hOld
  · rw [if_neg hi] at hsub
    exact hWithin i hsub

/-- Real bundles outside the selected position remain free of the fixed
item whenever the source vertex has that property. -/
theorem variableForceVertex_onlyAt {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D)
    (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (hOnly : ∀ i : Fin k, i ≠ a → e ∉ (p.1 i).1)
    (i : Fin k) (hi : i ≠ a) :
    e ∉ ((variableForceVertex e heD a hra p).1 i).1 := by
  intro he
  have hsub := (variableForceVertex_bounds e heD a hra p).1 i he
  rw [if_neg hi] at hsub
  exact hOnly i hi hsub

/-- Both the original face and its forced-item image lie together in the
same stock-restricted cover member. -/
theorem variableForceVertex_contiguous_in_stockCover {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hStock : S ∈ variableStockComplex D E r c)
    (hOnly : VariableItemOnlyAt S e a) :
    S ∪ S.image (variableForceVertex e heD a hra) ∈
      variableStockComplex D E r c ⊓
        variableItemCoverComplex D r c e a := by
  classical
  have hFace := variableFace_union_forceVertex
    e heD a hra S hStock.1.2 hOnly
  have hWithin : VariableRealWithin E
      (S ∪ S.image (variableForceVertex e heD a hra)) := by
    intro p hp i
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hStock.2 p hp i
    · obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      rw [← hqp]
      exact variableForceVertex_realWithin e heD heE a hra q
        (fun j => hStock.2 q hq j) i
  have hOnlyUnion : VariableItemOnlyAt
      (S ∪ S.image (variableForceVertex e heD a hra)) e a := by
    intro j hj hePool
    obtain ⟨_, p, hp, hep⟩ := Finset.mem_filter.mp hePool
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hOnly j hj (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hep⟩)
    · obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
      rw [← hqp] at hep
      have hOnlyQ : ∀ i : Fin k, i ≠ a → e ∉ (q.1 i).1 := by
        intro i hi heQ
        exact hOnly i hi (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, q, hq, heQ⟩)
      exact variableForceVertex_onlyAt e heD a hra q hOnlyQ j hj hep
  obtain ⟨p, hp⟩ := hStock.1.1
  have hNonempty :
      (S ∪ S.image (variableForceVertex e heD a hra)).Nonempty :=
    ⟨p, Finset.mem_union_left _ hp⟩
  exact ⟨⟨⟨hNonempty, hFace⟩, hWithin⟩,
    ⟨⟨hNonempty, hFace⟩, hOnlyUnion⟩⟩

end FairDivision.Topology
