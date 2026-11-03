import FairDivision.Topology.VariableDummyForcedFace
import FairDivision.Topology.VariableDummyProfiles

/-!
# The item-restricted cover of the variable-size auxiliary complex

Fix a real item `e`. A face belongs to the cover member at position `a` when
`e` occurs nowhere else. Every auxiliary face belongs to some member whose
bundle requirement is positive. Distinct members intersect exactly in the
subcomplex where `e` is absent from every real bundle.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- The fixed item is absent from all position pools of a face. -/
def VariableItemAbsent {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (e : Fin m) : Prop :=
  ∀ i : Fin k, e ∉ variableRealPool S i

/-- Every auxiliary face is in an item-restricted cover member with positive
required size, provided at least one position requires an item. -/
theorem variableFace_mem_item_cover {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m)
    (hSome : ∃ a : Fin k, 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S) :
    ∃ a : Fin k, 0 < r a ∧ VariableItemOnlyAt S e a := by
  classical
  by_cases hOccurs : ∃ a : Fin k, e ∈ variableRealPool S a
  · obtain ⟨a, hea⟩ := hOccurs
    have hra : 0 < r a := by
      obtain ⟨p, hp, hep⟩ := (Finset.mem_filter.mp hea).2
      have hcard : 0 < (p.1 a).1.card :=
        Finset.card_pos.mpr ⟨e, hep⟩
      have hprofile := variableProfile_card p a
      omega
    refine ⟨a, hra, ?_⟩
    intro j hja hej
    have hdisj := ((variableFace_iff S).1 hS).1 a j (Ne.symm hja)
    exact (Finset.disjoint_left.mp hdisj) hea hej
  · obtain ⟨a, hra⟩ := hSome
    refine ⟨a, hra, ?_⟩
    intro j _ hej
    exact hOccurs ⟨j, hej⟩

/-- A face lies in two different item-restricted cover members exactly when
the fixed item is absent everywhere. -/
theorem variableItemOnlyAt_two_iff_absent {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (e : Fin m) (a b : Fin k) (hab : a ≠ b) :
    (VariableItemOnlyAt S e a ∧ VariableItemOnlyAt S e b) ↔
      VariableItemAbsent S e := by
  constructor
  · intro h i
    by_cases hia : i = a
    · subst i
      exact h.2 a hab
    · exact h.1 i hia
  · intro h
    exact ⟨fun i _ => h i, fun i _ => h i⟩


/-- The manuscript's cover member as a genuine simplicial subcomplex. -/
def variableItemCoverComplex {k m : ℕ}
    (D : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (a : Fin k) :
    PreAbstractSimplicialComplex (VariableUnlabeledVertex k m D r c) where
  faces := {S | S ∈ variableDummyComplex k m D r c ∧
    VariableItemOnlyAt S e a}
  isRelLowerSet_faces := by
    intro S hS
    refine ⟨hS.1.1, ?_⟩
    intro T hTS hT
    constructor
    · exact ⟨hT, variableUnlabeled_mono hTS hS.1.2⟩
    · intro j hj heT
      have hPoolSub : variableRealPool T j ⊆ variableRealPool S j := by
        intro g hg
        obtain ⟨_, p, hp, hgp⟩ := Finset.mem_filter.mp hg
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, p, hTS hp, hgp⟩
      exact hS.2 j hj (hPoolSub heT)

/-- Each item-restricted cover member is a subcomplex of the auxiliary
complex. -/
theorem variableItemCoverComplex_le {k m : ℕ}
    (D : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (a : Fin k) :
    variableItemCoverComplex D r c e a ≤
      (variableDummyComplex k m D r c).toPreAbstractSimplicialComplex := by
  intro S hS
  exact hS.1

/-- The positive-requirement cover members cover every face of the full
variable-size complex. -/
theorem variableItemCoverComplex_covers {k m : ℕ}
    (D : Finset (Fin m)) (r c : Fin k → ℕ)
    (e : Fin m) (hSome : ∃ a : Fin k, 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : S ∈ variableDummyComplex k m D r c) :
    ∃ a : Fin k, 0 < r a ∧ S ∈ variableItemCoverComplex D r c e a := by
  obtain ⟨a, hra, hOnly⟩ := variableFace_mem_item_cover e hSome S hS.2
  exact ⟨a, hra, hS, hOnly⟩

end FairDivision.Topology
