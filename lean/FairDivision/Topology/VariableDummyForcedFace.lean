import FairDivision.Topology.VariableDummyFaceCriterion

/-!
# Face contiguity for forcing one real item to a position

The corrected BF connectivity induction covers the variable-size auxiliary
complex by subcomplexes where a chosen real item may occur at only one
position. Its retraction inserts that item at the permitted position. This
lemma isolates the exact face check for any such vertex operation: real
bundles may only shrink except for the permitted insertion, and dummy counts
may not increase.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Within `S`, the fixed real item occurs nowhere outside position `a`. -/
def VariableItemOnlyAt {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (e : Fin m) (a : Fin k) : Prop :=
  ∀ j : Fin k, j ≠ a → e ∉ variableRealPool S j

/-- Generic face condition for a forced-item vertex map on a cover member.
The image face and original face can be linearly interpolated. -/
theorem variableFace_union_image_of_forcing {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (a : Fin k)
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hReal : ∀ p j,
      ((f p).1 j).1 ⊆
        if j = a then insert e (p.1 j).1 else (p.1 j).1)
    (hDummy : ∀ p j, ((f p).1 j).2 ≤ (p.1 j).2)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S)
    (hOnly : VariableItemOnlyAt S e a) :
    IsVariableUnlabeledFamily (S ∪ S.image f) := by
  classical
  have hPoolOther (j : Fin k) (hj : j ≠ a) :
      variableRealPool (S ∪ S.image f) j ⊆ variableRealPool S j := by
    intro g hg
    obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hgq⟩
    · obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hq
      rw [← hfp] at hgq
      have hsub := hReal p j
      rw [if_neg hj] at hsub
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hsub hgq⟩
  have hPoolAt :
      variableRealPool (S ∪ S.image f) a ⊆
        insert e (variableRealPool S a) := by
    intro g hg
    obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hgq⟩)
    · obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hq
      rw [← hfp] at hgq
      have hsub := hReal p a
      rw [if_pos rfl] at hsub
      rcases Finset.mem_insert.mp (hsub hgq) with rfl | hgp
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, hgp⟩)
  have hMax (j : Fin k) :
      variableDummyMax (S ∪ S.image f) j ≤ variableDummyMax S j := by
    unfold variableDummyMax
    apply Finset.sup_le
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.le_sup (f := fun p : VariableUnlabeledVertex k m D r c =>
        (p.1 j).2) hq
    · obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hq
      rw [← hfp]
      exact (hDummy p j).trans
        (Finset.le_sup (f := fun p : VariableUnlabeledVertex k m D r c =>
          (p.1 j).2) hp)
  apply (variableFace_iff (S ∪ S.image f)).2
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
      (∑ j : Fin k, variableDummyMax (S ∪ S.image f) j) ≤
          ∑ j : Fin k, variableDummyMax S j :=
        Finset.sum_le_sum (fun j _ => hMax j)
      _ ≤ D.card := ((variableFace_iff S).1 hS).2

end FairDivision.Topology
