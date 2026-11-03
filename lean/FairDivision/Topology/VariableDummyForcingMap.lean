import FairDivision.Topology.VariableDummyForcedVertex
import FairDivision.Topology.VariableDummyForcedFace
import FairDivision.Topology.VariableDummyCover

/-!
# The forced-item map on the variable-size auxiliary complex

The map acts on every vertex, but changes a vertex only when the chosen real
item occurs at no other position. On each item-restricted cover member, it
places the item at the permitted position and is contiguous to the identity.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Insert a fixed real item at a positive-requirement position whenever the
vertex belongs to the corresponding item-restricted cover member. -/
noncomputable def variableForceVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c) :
    VariableUnlabeledVertex k m D r c := by
  classical
  if hA : e ∈ (p.1 a).1 then
    exact p
  else if hOnly : ∀ j : Fin k, j ≠ a → e ∉ (p.1 j).1 then
    exact Classical.choose
      (exists_variable_vertex_forcing p e heD a hra hOnly hA)
  else
    exact p

/-- Forcing only shrinks the old real bundles apart from inserting the fixed
item at the selected position, and never raises a dummy count. -/
theorem variableForceVertex_bounds {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c) :
    (∀ j : Fin k,
      ((variableForceVertex e heD a hra p).1 j).1 ⊆
        if j = a then insert e (p.1 j).1 else (p.1 j).1) ∧
    (∀ j : Fin k,
      ((variableForceVertex e heD a hra p).1 j).2 ≤ (p.1 j).2) := by
  classical
  by_cases hA : e ∈ (p.1 a).1
  · simp only [variableForceVertex, dif_pos hA]
    constructor
    · intro j
      by_cases hj : j = a
      · subst j
        simp
      · simp [hj]
    · intro j
      exact le_rfl
  · by_cases hOnly : ∀ j : Fin k, j ≠ a → e ∉ (p.1 j).1
    · have hSpec := Classical.choose_spec
        (exists_variable_vertex_forcing p e heD a hra hOnly hA)
      simpa only [variableForceVertex, dif_neg hA, dif_pos hOnly]
        using And.intro hSpec.2.1 hSpec.2.2
    · simp only [variableForceVertex, dif_neg hA, dif_neg hOnly]
      constructor
      · intro j
        by_cases hj : j = a
        · subst j
          simp
        · simp [hj]
      · intro j
        exact le_rfl

/-- The forcing map is the identity when the fixed item is already at the
selected position. -/
theorem variableForceVertex_fixed {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (hA : e ∈ (p.1 a).1) :
    variableForceVertex e heD a hra p = p := by
  classical
  simp [variableForceVertex, hA]

/-- A vertex in the cover member has the fixed item at the selected position
after forcing. -/
theorem variableForceVertex_mem_at_of_only {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (p : VariableUnlabeledVertex k m D r c)
    (hOnly : ∀ j : Fin k, j ≠ a → e ∉ (p.1 j).1) :
    e ∈ ((variableForceVertex e heD a hra p).1 a).1 := by
  classical
  by_cases hA : e ∈ (p.1 a).1
  · simpa [variableForceVertex, hA] using hA
  · have hSpec := Classical.choose_spec
      (exists_variable_vertex_forcing p e heD a hra hOnly hA)
    simpa only [variableForceVertex, dif_neg hA, dif_pos hOnly]
      using hSpec.1

/-- The forcing map is contiguous to the identity on an item-restricted
cover member. -/
theorem variableFace_union_forceVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S)
    (hOnly : VariableItemOnlyAt S e a) :
    IsVariableUnlabeledFamily
      (S ∪ S.image (variableForceVertex e heD a hra)) := by
  exact variableFace_union_image_of_forcing e a
    (variableForceVertex e heD a hra)
    (fun p j => (variableForceVertex_bounds e heD a hra p).1 j)
    (fun p j => (variableForceVertex_bounds e heD a hra p).2 j)
    S hS hOnly

/-- Every vertex of a face in the restricted cover is mapped to a vertex
whose selected real bundle contains the fixed item. -/
theorem variableForceVertex_mem_at_on_cover {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (e : Fin m) (heD : e ∉ D) (a : Fin k) (hra : 0 < r a)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hOnly : VariableItemOnlyAt S e a)
    (p : VariableUnlabeledVertex k m D r c) (hp : p ∈ S) :
    e ∈ ((variableForceVertex e heD a hra p).1 a).1 := by
  apply variableForceVertex_mem_at_of_only e heD a hra p
  intro j hj he
  apply hOnly j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp, he⟩

end FairDivision.Topology
