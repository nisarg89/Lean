import FairDivision.Topology.VariableDummyCover

/-!
# Restricting the available real stock of the BF auxiliary complex

The connectivity induction removes a real item while keeping the ambient
finite item type fixed. A stock restriction records the allowed real labels;
this avoids a noncanonical relabeling of `Fin m` after each deletion.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Every real bundle of every vertex in a face uses only the stock `E`. -/
def VariableRealWithin {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (E : Finset (Fin m))
    (S : Finset (VariableUnlabeledVertex k m D r c)) : Prop :=
  ∀ p ∈ S, ∀ i : Fin k, (p.1 i).1 ⊆ E

/-- The auxiliary subcomplex with real items restricted to `E`. -/
def variableStockComplex {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) :
    PreAbstractSimplicialComplex (VariableUnlabeledVertex k m D r c) where
  faces := {S | S ∈ variableDummyComplex k m D r c ∧
    VariableRealWithin E S}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1.1, ?_⟩
    intro T hTS hT
    constructor
    · exact ⟨hT, variableUnlabeled_mono hTS hS.1.2⟩
    · intro p hp i
      exact hS.2 p (hTS hp) i

/-- Restricting the real stock only removes faces. -/
theorem variableStockComplex_le {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ) :
    variableStockComplex D E r c ≤
      (variableDummyComplex k m D r c).toPreAbstractSimplicialComplex := by
  intro S hS
  exact hS.1

/-- Enlarging the real stock enlarges the restricted complex. -/
theorem variableStockComplex_mono {k m : ℕ}
    (D : Finset (Fin m)) {E F : Finset (Fin m)} (hEF : E ⊆ F)
    (r c : Fin k → ℕ) :
    variableStockComplex D E r c ≤ variableStockComplex D F r c := by
  intro S hS
  refine ⟨hS.1, ?_⟩
  intro p hp i
  exact (hS.2 p hp i).trans hEF

/-- The unrestricted complex is the stock-restricted complex for all
nondummy labels. -/
theorem variableStockComplex_full {k m : ℕ}
    (D : Finset (Fin m)) (r c : Fin k → ℕ) :
    variableStockComplex D (Finset.univ \ D) r c =
      (variableDummyComplex k m D r c).toPreAbstractSimplicialComplex := by
  ext S
  constructor
  · exact And.left
  · intro hS
    refine ⟨hS, ?_⟩
    intro p hp i g hg
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _,
        fun hD => (Finset.disjoint_left.mp
          (variableProfile_real_disjoint_dummy p i)) hg hD⟩

/-- Deleting `e` from a stock is exactly imposing the condition that no real
bundle uses `e`, while retaining the old stock restriction. -/
theorem variableStockComplex_erase_iff_absent {k m : ℕ}
    (D E : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (S : Finset (VariableUnlabeledVertex k m D r c)) :
    S ∈ variableStockComplex D (E.erase e) r c ↔
      S ∈ variableStockComplex D E r c ∧ VariableItemAbsent S e := by
  constructor
  · intro hS
    constructor
    · refine ⟨hS.1, ?_⟩
      intro p hp i
      exact (hS.2 p hp i).trans (Finset.erase_subset e E)
    · intro i hePool
      obtain ⟨_, p, hp, heP⟩ := Finset.mem_filter.mp hePool
      have hErase := hS.2 p hp i heP
      exact (Finset.ne_of_mem_erase hErase) rfl
  · intro hS
    refine ⟨hS.1.1, ?_⟩
    intro p hp i g hg
    apply Finset.mem_erase.mpr
    constructor
    · intro hge
      subst g
      exact hS.2 i (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hg⟩)
    · exact hS.1.2 p hp i hg

end FairDivision.Topology
