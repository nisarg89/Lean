import FairDivision.Topology.VariableDummyRetractions
import FairDivision.Topology.VariableDummyProfileTransport
import FairDivision.Topology.VariableDummyVertexBuild

/-!
# Removing saturated dummy coordinates

At a saturated BF auxiliary vertex, dummy counts are fixed and the real
bundle at position `i` has size `r i - u i`. This file begins the exact
identification of the saturation retract with the no-dummy auxiliary
complex used in the manuscript's first induction branch.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A vertex never uses more dummies at a position than either its
requirement or its dummy cap. -/
theorem variableProfile_dummy_le_min {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    (p.1 i).2 ≤ min (r i) (c i) := by
  have hCard := variableProfile_card p i
  have hCap := variableProfile_dummy_le_cap p i
  omega

/-- Every original vertex has a canonical saturated image, whose real
bundles form a vertex of the reduced no-dummy complex. -/
theorem exists_variableSaturationReducedVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) :
    ∃ q : VariableUnlabeledVertex k m (∅ : Finset (Fin m))
        (fun i => r i - u i) (fun _ => 0),
      ∀ i : Fin k,
        q.1 i =
          (((saturateVariableVertex u huR huC hBudget hBound p).1 i).1, 0) := by
  let sat := saturateVariableVertex u huR huC hBudget hBound p
  have hCard (i : Fin k) : ((sat.1 i).1).card = r i - u i := by
    have h := variableProfile_card sat i
    have hs := (saturateVariableVertex_spec
      u huR huC hBudget hBound p i).2
    dsimp [sat] at h ⊢
    omega
  have hExists : ∃ q : VariableUnlabeledVertex k m
      (∅ : Finset (Fin m)) (fun i => r i - u i) (fun _ => 0),
      ∀ i : Fin k, q.1 i = ((sat.1 i).1, 0) := by
    apply exists_variable_vertex_of_profile
      (fun i => (sat.1 i).1) (fun _ => 0)
    · intro i
      simp
    · intro i j hij
      exact variableProfile_real_pairwise sat i j hij
    · intro i
      simpa using hCard i
    · intro i
      exact le_rfl
    · simp
  simpa [sat] using hExists

/-- Choose the reduced no-dummy vertex associated with the saturated image. -/
noncomputable def variableSaturationReducedVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) :
    VariableUnlabeledVertex k m (∅ : Finset (Fin m))
      (fun i => r i - u i) (fun _ => 0) :=
  Classical.choose (exists_variableSaturationReducedVertex
    u huR huC hBudget hBound p)

/-- The chosen reduced vertex keeps exactly the real bundles of the
saturated original vertex. -/
theorem variableSaturationReducedVertex_spec {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    (variableSaturationReducedVertex u huR huC hBudget hBound p).1 i =
      (((saturateVariableVertex u huR huC hBudget hBound p).1 i).1, 0) :=
  Classical.choose_spec (exists_variableSaturationReducedVertex
    u huR huC hBudget hBound p) i


/-- A reduced no-dummy vertex using only real stock `E` lifts to a vertex
with the prescribed saturated dummy counts. -/
theorem exists_variableSaturationLiftVertex {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hED : Disjoint E D)
    (q : VariableUnlabeledVertex k m (∅ : Finset (Fin m))
      (fun i => r i - u i) (fun _ => 0))
    (hStock : ∀ i : Fin k, (q.1 i).1 ⊆ E) :
    ∃ p : VariableUnlabeledVertex k m D r c,
      ∀ i : Fin k, p.1 i = ((q.1 i).1, u i) := by
  have hCard (i : Fin k) : (q.1 i).1.card + u i = r i := by
    have h := variableProfile_card q i
    have hz := variableProfile_dummy_le_cap q i
    have hu := huR i
    omega
  apply exists_variable_vertex_of_profile
    (fun i => (q.1 i).1) u
  · intro i
    exact hED.mono_left (hStock i)
  · intro i j hij
    exact variableProfile_real_pairwise q i j hij
  · exact hCard
  · exact huC
  · exact hBudget

/-- Choose the lift of a stock-restricted reduced vertex to the saturated
original complex. -/
noncomputable def variableSaturationLiftVertex {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hED : Disjoint E D)
    (q : VariableUnlabeledVertex k m (∅ : Finset (Fin m))
      (fun i => r i - u i) (fun _ => 0))
    (hStock : ∀ i : Fin k, (q.1 i).1 ⊆ E) :
    VariableUnlabeledVertex k m D r c :=
  Classical.choose (exists_variableSaturationLiftVertex
    u huR huC hBudget hED q hStock)

/-- The chosen lift keeps real bundles and fixes the dummy count at `u`. -/
theorem variableSaturationLiftVertex_spec {k m : ℕ}
    {D E : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hED : Disjoint E D)
    (q : VariableUnlabeledVertex k m (∅ : Finset (Fin m))
      (fun i => r i - u i) (fun _ => 0))
    (hStock : ∀ i : Fin k, (q.1 i).1 ⊆ E)
    (i : Fin k) :
    (variableSaturationLiftVertex u huR huC hBudget hED q hStock).1 i =
      ((q.1 i).1, u i) :=
  Classical.choose_spec (exists_variableSaturationLiftVertex
    u huR huC hBudget hED q hStock) i

end FairDivision.Topology
