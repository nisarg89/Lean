import FairDivision.Topology.VariableDummyVertexBuild
import FairDivision.Topology.VariableDummyRealization

/-!
# Zero-requirement base case of the connectivity induction

When every position requires zero items, every auxiliary profile is the same
empty profile. Thus the complex and its geometric realization have one point.
This is the base case in the corrected BF connectivity induction.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- With zero required sizes, every auxiliary vertex is the empty profile. -/
theorem variableVertex_subsingleton_zero {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0) :
    Subsingleton (VariableUnlabeledVertex k m D r c) := by
  classical
  constructor
  intro p q
  apply Subtype.ext
  funext i
  apply Prod.ext
  · have hp : (p.1 i).1 = ∅ := by
      apply Finset.card_eq_zero.mp
      have hc := variableProfile_card p i
      rw [hr i] at hc
      omega
    have hq : (q.1 i).1 = ∅ := by
      apply Finset.card_eq_zero.mp
      have hc := variableProfile_card q i
      rw [hr i] at hc
      omega
    rw [hp, hq]
  · have hp := variableProfile_card p i
    have hq := variableProfile_card q i
    rw [hr i] at hp hq
    omega

/-- The empty profile is an auxiliary vertex when all requirements vanish. -/
theorem variableVertex_nonempty_zero {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0) :
    Nonempty (VariableUnlabeledVertex k m D r c) := by
  classical
  obtain ⟨p, _⟩ := exists_variable_vertex_of_profile
    (D := D) (r := r) (c := c)
    (fun _ : Fin k => (∅ : Finset (Fin m))) (fun _ => 0)
    (by simp) (by simp)
    (by intro i; simp [hr i])
    (by simp) (by simp)
  exact ⟨p⟩

/-- The zero-requirement auxiliary realization is subsingleton. -/
theorem variableLotterySpace_subsingleton_zero {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0) :
    Subsingleton (variableLotterySpace k m D r c) := by
  letI := variableVertex_subsingleton_zero (D := D) (c := c) hr
  infer_instance


/-- In the zero-requirement case every simplex lottery belongs to the
auxiliary realization. -/
theorem variableLotterySpace_all_zero {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c)) :
    lot ∈ variableLotterySpace k m D r c := by
  classical
  letI := variableVertex_subsingleton_zero (D := D) (c := c) hr
  obtain ⟨p, hp⟩ := variableLotterySupport_nonempty lot
  have hSupport : variableLotterySupport lot = {p} := by
    apply Finset.Subset.antisymm
    · intro q _
      exact Finset.mem_singleton.mpr (Subsingleton.elim q p)
    · intro q hq
      rw [Finset.mem_singleton.mp hq]
      exact hp
  change IsVariableUnlabeledFamily (variableLotterySupport lot)
  rw [hSupport]
  exact variableUnlabeled_singleton p

/-- The zero-requirement auxiliary realization is inhabited. -/
theorem variableLotterySpace_nonempty_zero {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (hr : ∀ i : Fin k, r i = 0) :
    Nonempty (variableLotterySpace k m D r c) := by
  classical
  let p := Classical.choice (variableVertex_nonempty_zero (D := D) (c := c) hr)
  let lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c) :=
    stdSimplex.vertex p
  exact ⟨⟨lot, variableLotterySpace_all_zero hr lot⟩⟩

end FairDivision.Topology
