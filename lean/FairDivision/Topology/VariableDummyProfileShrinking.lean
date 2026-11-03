import FairDivision.Topology.VariableDummyProfileTransport

/-!
# Face transport under shrinking real bundles and dummy counts

Deleting a forced real item shrinks one real bundle and preserves every
dummy count. This general lemma transfers a face across different auxiliary
vertex types whenever both kinds of resources only shrink.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Under pointwise real-bundle inclusion, each mapped real pool lies in the
old real pool. -/
theorem variableRealPool_image_subset {k m : ℕ}
    {D D' : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D' r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D' r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hReal : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).1 ⊆ (p.1 i).1)
    (i : Fin k) :
    variableRealPool (S.image f) i ⊆ variableRealPool S i := by
  classical
  intro g hg
  obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  subst q
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, p, hp, hReal p hp i hgq⟩

/-- Under pointwise dummy-count reduction, the mapped maximum cannot exceed
the source maximum. -/
theorem variableDummyMax_image_le_source {k m : ℕ}
    {D D' : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D' r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D' r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hDummy : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).2 ≤ (p.1 i).2)
    (i : Fin k) :
    variableDummyMax (S.image f) i ≤ variableDummyMax S i := by
  classical
  unfold variableDummyMax
  apply Finset.sup_le
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  subst q
  exact (hDummy p hp i).trans
    (Finset.le_sup (f := fun v : VariableUnlabeledVertex k m D r c =>
      (v.1 i).2) hp)

/-- If a profile map only shrinks real bundles and dummy counts, it sends
faces to faces with the same dummy stock. -/
theorem variableFace_image_of_shrinking {k m : ℕ}
    {D : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hFace : IsVariableUnlabeledFamily S)
    (hReal : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).1 ⊆ (p.1 i).1)
    (hDummy : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).2 ≤ (p.1 i).2) :
    IsVariableUnlabeledFamily (S.image f) := by
  apply (variableFace_iff (S.image f)).2
  constructor
  · intro i j hij
    exact (((variableFace_iff S).1 hFace).1 i j hij).mono
      (variableRealPool_image_subset f S hReal i)
      (variableRealPool_image_subset f S hReal j)
  · calc
      (∑ i : Fin k, variableDummyMax (S.image f) i) ≤
          ∑ i : Fin k, variableDummyMax S i := by
        apply Finset.sum_le_sum
        intro i _
        exact variableDummyMax_image_le_source f S hDummy i
      _ ≤ D.card := ((variableFace_iff S).1 hFace).2

end FairDivision.Topology
