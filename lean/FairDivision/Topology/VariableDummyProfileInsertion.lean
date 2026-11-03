import FairDivision.Topology.VariableDummyProfileShrinking
import FairDivision.Topology.VariableDummyForcedFace

/-!
# Face transport when one real item is inserted at one position

This is the cross-vertex-type form of the manuscript's forcing face check.
It is used after deleting a forced item: the inverse map inserts that item
at the selected position in every reduced vertex. The item is absent at
all other positions throughout the source face.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Inserting `e` only at position `a`, while not increasing dummy counts,
sends a face to a face when `e` is absent from every other source pool. -/
theorem variableFace_image_of_inserting_at {k m : ℕ}
    {D : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D r' c')]
    (e : Fin m) (a : Fin k)
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S)
    (hReal : ∀ p ∈ S, ∀ j : Fin k,
      ((f p).1 j).1 ⊆
        if j = a then insert e (p.1 j).1 else (p.1 j).1)
    (hDummy : ∀ p ∈ S, ∀ j : Fin k,
      ((f p).1 j).2 ≤ (p.1 j).2)
    (hOnly : VariableItemOnlyAt S e a) :
    IsVariableUnlabeledFamily (S.image f) := by
  classical
  have hPoolOther (j : Fin k) (hj : j ≠ a) :
      variableRealPool (S.image f) j ⊆ variableRealPool S j := by
    intro g hg
    obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    subst q
    have hsub := hReal p hp j
    rw [if_neg hj] at hsub
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, p, hp, hsub hgq⟩
  have hPoolAt :
      variableRealPool (S.image f) a ⊆
        insert e (variableRealPool S a) := by
    intro g hg
    obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    subst q
    have hsub := hReal p hp a
    rw [if_pos rfl] at hsub
    rcases Finset.mem_insert.mp (hsub hgq) with rfl | hgp
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hgp⟩)
  have hMax (j : Fin k) :
      variableDummyMax (S.image f) j ≤ variableDummyMax S j :=
    variableDummyMax_image_le_source f S hDummy j
  apply (variableFace_iff (S.image f)).2
  constructor
  · intro i j hij
    have hOld := ((variableFace_iff S).1 hS).1 i j hij
    by_cases hi : i = a
    · subst i
      have hj : j ≠ a := Ne.symm hij
      apply Finset.disjoint_left.mpr
      intro g hgi hgj
      have hgi' := hPoolAt hgi
      have hgj' := hPoolOther j hj hgj
      rcases Finset.mem_insert.mp hgi' with hge | hgi''
      · subst g
        exact hOnly j hj hgj'
      · exact (Finset.disjoint_left.mp hOld) hgi'' hgj'
    · by_cases hj : j = a
      · subst j
        apply Finset.disjoint_left.mpr
        intro g hgi hgj
        have hgi' := hPoolOther i hi hgi
        have hgj' := hPoolAt hgj
        rcases Finset.mem_insert.mp hgj' with hge | hgj''
        · subst g
          exact hOnly i hi hgi'
        · exact (Finset.disjoint_left.mp hOld) hgi' hgj''
      · exact hOld.mono (hPoolOther i hi) (hPoolOther j hj)
  · calc
      (∑ j : Fin k, variableDummyMax (S.image f) j) ≤
          ∑ j : Fin k, variableDummyMax S j :=
        Finset.sum_le_sum (fun j _ => hMax j)
      _ ≤ D.card := ((variableFace_iff S).1 hS).2

end FairDivision.Topology
