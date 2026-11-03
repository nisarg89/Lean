import FairDivision.Topology.VariableDummyVertexBuild
import FairDivision.Finite.OrderedPrefix

/-!
# Dummy saturation of the variable-size auxiliary complex

For each position choose a target dummy count `u i` that dominates all vertex
counts and fits in the dummy stock. Shrinking each real bundle by the added
dummy count gives a saturated vertex. The original face and all of its
saturated images form a common face, the combinatorial contiguity needed for
the deformation step of the connectivity induction.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- Real bundles of a single variable-size profile are pairwise disjoint. -/
theorem variableProfile_real_pairwise {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (p : VariableUnlabeledVertex k m D r c)
    (i j : Fin k) (hij : i ≠ j) :
    Disjoint (p.1 i).1 (p.1 j).1 := by
  obtain ⟨X, hX⟩ := p.2
  rw [← congrArg Prod.fst (congrFun hX i),
    ← congrArg Prod.fst (congrFun hX j)]
  apply Finset.disjoint_left.mpr
  intro g hgi hgj
  have hi : X.1 g = some i :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hgi).1).2
  have hj : X.1 g = some j :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hgj).1).2
  exact hij (Option.some.inj (hi.symm.trans hj))

/-- If a vertex map only shrinks real bundles and its old and new dummy
counts fit under a common budget, each face is contiguous to its image. -/
theorem variableFace_union_image_of_shrinking {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hShrink : ∀ p i, ((f p).1 i).1 ⊆ (p.1 i).1)
    (hOld : ∀ (p : VariableUnlabeledVertex k m D r c) i, (p.1 i).2 ≤ u i)
    (hNew : ∀ p i, ((f p).1 i).2 ≤ u i)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S) :
    IsVariableUnlabeledFamily (S ∪ S.image f) := by
  classical
  have hPool (i : Fin k) :
      variableRealPool (S ∪ S.image f) i ⊆ variableRealPool S i := by
    intro g hg
    obtain ⟨_, q, hq, hgq⟩ := Finset.mem_filter.mp hg
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hgq⟩
    · obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp hq
      rw [← hfp] at hgq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, p, hp, hShrink p i hgq⟩
  have hMax (i : Fin k) : variableDummyMax (S ∪ S.image f) i ≤ u i := by
    unfold variableDummyMax
    apply Finset.sup_le
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hOld q i
    · obtain ⟨p, _, hfp⟩ := Finset.mem_image.mp hq
      rw [← hfp]
      exact hNew p i
  apply (variableFace_iff (S ∪ S.image f)).2
  constructor
  · intro i j hij
    exact ((variableFace_iff S).1 hS).1 i j hij |>.mono
      (hPool i) (hPool j)
  · calc
      (∑ i : Fin k, variableDummyMax (S ∪ S.image f) i) ≤
          ∑ i : Fin k, u i := Finset.sum_le_sum (fun i _ => hMax i)
      _ ≤ D.card := hBudget

/-- Choose a real subset of the size required after saturation. -/
private noncomputable def saturationReal {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (hu : ∀ i, u i ≤ r i)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c)
    (i : Fin k) : Finset (Fin m) :=
  FairDivision.Finite.orderedPrefix (p.1 i).1 (r i - u i) (by
    have hp := variableProfile_card p i
    have hpi := hBound p i
    have hui := hu i
    omega : r i - u i ≤ (p.1 i).1.card)

private theorem saturationReal_spec {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ) (hu : ∀ i, u i ≤ r i)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    saturationReal u hu hBound p i ⊆ (p.1 i).1 ∧
      (saturationReal u hu hBound p i).card = r i - u i :=
  FairDivision.Finite.orderedPrefix_spec (p.1 i).1 (r i - u i) (by
    have hp := variableProfile_card p i
    have hpi := hBound p i
    have hui := hu i
    omega : r i - u i ≤ (p.1 i).1.card)

/-- Saturate each vertex up to `u`, retaining the first real items in the fixed order. -/
noncomputable def saturateVariableVertex {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) :
    VariableUnlabeledVertex k m D r c := by
  classical
  let F := saturationReal u huR hBound p
  have hSpec (i : Fin k) :
      F i ⊆ (p.1 i).1 ∧ (F i).card = r i - u i :=
    saturationReal_spec u huR hBound p i
  exact Classical.choose (exists_variable_vertex_of_profile F u
    (fun i => (variableProfile_real_disjoint_dummy p i).mono_left (hSpec i).1)
    (fun i j hij => (variableProfile_real_pairwise p i j hij).mono
      (hSpec i).1 (hSpec j).1)
    (fun i => by have hs := (hSpec i).2; have hu := huR i; omega)
    huC hBudget)

/-- Saturation retains only original real items and reaches the target dummy
count at every position. -/
theorem saturateVariableVertex_spec {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) (i : Fin k) :
    ((saturateVariableVertex u huR huC hBudget hBound p).1 i).1 ⊆
      (p.1 i).1 ∧
    ((saturateVariableVertex u huR huC hBudget hBound p).1 i).2 = u i := by
  classical
  dsimp [saturateVariableVertex]
  have hs := Classical.choose_spec
    (exists_variable_vertex_of_profile (D := D) (r := r) (c := c)
      (saturationReal u huR hBound p) u
      (fun i => (variableProfile_real_disjoint_dummy p i).mono_left
        (saturationReal_spec u huR hBound p i).1)
      (fun i j hij => (variableProfile_real_pairwise p i j hij).mono
        (saturationReal_spec u huR hBound p i).1
        (saturationReal_spec u huR hBound p j).1)
      (fun i => by
        have h := (saturationReal_spec u huR hBound p i).2
        have hu := huR i
        omega)
      huC hBudget)
  rw [hs i]
  exact ⟨(saturationReal_spec u huR hBound p i).1, rfl⟩

/-- The original face and its saturation image form a face. -/
theorem variableFace_union_saturation {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (S : Finset (VariableUnlabeledVertex k m D r c))
    (hS : IsVariableUnlabeledFamily S) :
    IsVariableUnlabeledFamily
      (S ∪ S.image (saturateVariableVertex u huR huC hBudget hBound)) := by
  apply variableFace_union_image_of_shrinking u hBudget
    (saturateVariableVertex u huR huC hBudget hBound)
  · intro p i
    exact (saturateVariableVertex_spec u huR huC hBudget hBound p i).1
  · exact hBound
  · intro p i
    exact le_of_eq
      (saturateVariableVertex_spec u huR huC hBudget hBound p i).2
  · exact hS


/-- Saturation fixes every vertex already at the target dummy counts. -/
theorem saturateVariableVertex_eq_of_saturated {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c)
    (hSat : ∀ i, (p.1 i).2 = u i) :
    saturateVariableVertex u huR huC hBudget hBound p = p := by
  apply Subtype.ext
  funext i
  apply Prod.ext
  · have hs := saturateVariableVertex_spec
      u huR huC hBudget hBound p i
    apply Finset.eq_of_subset_of_card_le hs.1
    have hCardOld := variableProfile_card p i
    have hCardNew := variableProfile_card
      (saturateVariableVertex u huR huC hBudget hBound p) i
    rw [hSat i] at hCardOld
    rw [hs.2] at hCardNew
    omega
  · exact (saturateVariableVertex_spec
      u huR huC hBudget hBound p i).2.trans (hSat i).symm

/-- Dummy saturation is idempotent. -/
theorem saturateVariableVertex_idempotent {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (p : VariableUnlabeledVertex k m D r c) :
    saturateVariableVertex u huR huC hBudget hBound
      (saturateVariableVertex u huR huC hBudget hBound p) =
      saturateVariableVertex u huR huC hBudget hBound p := by
  apply saturateVariableVertex_eq_of_saturated
    u huR huC hBudget hBound
  intro i
  exact (saturateVariableVertex_spec
    u huR huC hBudget hBound p i).2

end FairDivision.Topology
