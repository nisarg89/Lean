import FairDivision.Topology.VariableDummyStockForcing

/-!
# The fixed-item subcomplex of a cover member

Within the cover member indexed by `a`, forcing the item `e` at every vertex
is a simplicial map to the subcomplex in which each vertex already assigns
`e` to `a`. This is the deformation retract used in the manuscript's
connectivity induction.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A face in the restricted stock has the real item `e` at position `a` in
every vertex. -/
def variableForcedItemComplex {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (a : Fin k) :
    PreAbstractSimplicialComplex (VariableUnlabeledVertex k m D r c) where
  faces := {S | S ∈ variableStockComplex D E r c ∧
    ∀ p ∈ S, e ∈ (p.1 a).1}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨(variableStockComplex D E r c).isRelLowerSet_faces hS.1 |>.1, ?_⟩
    intro T hTS hT
    refine ⟨((variableStockComplex D E r c).isRelLowerSet_faces hS.1).2
      hTS hT, ?_⟩
    intro p hp
    exact hS.2 p (hTS hp)

/-- The fixed-item subcomplex lies inside its cover member when `e` is not
a dummy label. -/
theorem variableForcedItemComplex_le_cover {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (a : Fin k) :
    variableForcedItemComplex D E r c e a ≤
      variableStockComplex D E r c ⊓
        variableItemCoverComplex D r c e a := by
  intro S hS
  refine ⟨hS.1, ⟨hS.1.1, ?_⟩⟩
  intro j hja hePool
  obtain ⟨_, p, hp, heP⟩ := Finset.mem_filter.mp hePool
  have heAt := hS.2 p hp
  have hDisj := ((variableFace_iff S).1 hS.1.1.2).1 a j (Ne.symm hja)
  exact (Finset.disjoint_left.mp hDisj)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, heAt⟩) hePool

/-- The forcing map sends every face of the stock-restricted cover member
to a face of the fixed-item subcomplex. -/
theorem variableForceVertex_image_mem_forced {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (heE : e ∈ E)
    (a : Fin k) (hra : 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hCover : S ∈ variableStockComplex D E r c ⊓
      variableItemCoverComplex D r c e a) :
    S.image (variableForceVertex e heD a hra) ∈
      variableForcedItemComplex D E r c e a := by
  classical
  have hUnion := variableForceVertex_contiguous_in_stockCover
    e heD heE a hra S hCover.1 hCover.2.2
  have hSub : S.image (variableForceVertex e heD a hra) ⊆
      S ∪ S.image (variableForceVertex e heD a hra) :=
    Finset.subset_union_right
  have hStock :=
    ((variableStockComplex D E r c).isRelLowerSet_faces hUnion.1).2
      hSub (Finset.image_nonempty.mpr hCover.1.1.1)
  refine ⟨hStock, ?_⟩
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
  rw [← hqp]
  exact variableForceVertex_mem_at_on_cover
    e heD a hra S hCover.2.2 q hq

/-- Forcing fixes every vertex of the fixed-item subcomplex. -/
theorem variableForceVertex_fixed_on_forced {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D)
    (a : Fin k) (hra : 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hForced : S ∈ variableForcedItemComplex D E r c e a)
    (p : VariableUnlabeledVertex k m D r c) (hp : p ∈ S) :
    variableForceVertex e heD a hra p = p :=
  variableForceVertex_fixed e heD a hra p (hForced.2 p hp)

end FairDivision.Topology
