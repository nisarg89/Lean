import FairDivision.Topology.VariableDummyFaceCriterion

/-!
# Transporting BF faces by their real bundles

The face criterion depends only on real-bundle intersections and the maximum
dummy counts. These lemmas isolate the reusable part of both induction
identifications: a profile map preserving real bundles sends a face to a face
whenever its target dummy counts fit the target dummy stock.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Mapping every vertex without changing its real bundles leaves each real
pool unchanged. -/
theorem variableRealPool_image_eq {k m : ℕ}
    {D D' : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D' r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D' r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hReal : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).1 = (p.1 i).1)
    (i : Fin k) :
    variableRealPool (S.image f) i = variableRealPool S i := by
  classical
  ext g
  simp only [variableRealPool, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, hg⟩
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
    subst q
    exact ⟨p, hp, (hReal p hp i) ▸ hg⟩
  · rintro ⟨p, hp, hg⟩
    refine ⟨f p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    rw [hReal p hp i]
    exact hg

/-- If each mapped vertex has at most `u i` dummy items at position `i`,
the maximum over the mapped face has the same bound. -/
theorem variableDummyMax_image_le {k m : ℕ}
    {D D' : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D' r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D' r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (u : Fin k → ℕ)
    (hDummy : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).2 ≤ u i)
    (i : Fin k) :
    variableDummyMax (S.image f) i ≤ u i := by
  classical
  unfold variableDummyMax
  apply Finset.sup_le
  intro q hq
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  subst q
  exact hDummy p hp i

/-- A real-bundle-preserving profile map sends a face to a face if the target
dummy counts fit the target dummy stock. -/
theorem variableFace_image_of_real_preserving {k m : ℕ}
    {D D' : Finset (Fin m)} {r c r' c' : Fin k → ℕ}
    [DecidableEq (VariableUnlabeledVertex k m D' r' c')]
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D' r' c')
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hFace : IsVariableUnlabeledFamily S)
    (hReal : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).1 = (p.1 i).1)
    (u : Fin k → ℕ)
    (hDummy : ∀ p ∈ S, ∀ i : Fin k, ((f p).1 i).2 ≤ u i)
    (hBudget : (∑ i : Fin k, u i) ≤ D'.card) :
    IsVariableUnlabeledFamily (S.image f) := by
  apply (variableFace_iff (S.image f)).2
  constructor
  · intro i j hij
    rw [variableRealPool_image_eq f S hReal i,
      variableRealPool_image_eq f S hReal j]
    exact ((variableFace_iff S).1 hFace).1 i j hij
  · calc
      (∑ i : Fin k, variableDummyMax (S.image f) i) ≤
          ∑ i : Fin k, u i := by
        apply Finset.sum_le_sum
        intro i _
        exact variableDummyMax_image_le f S u hDummy i
      _ ≤ D'.card := hBudget

end FairDivision.Topology
