import FairDivision.Topology.VariableDummyRealization

/-!
# Geometric interpolation from contiguous auxiliary-complex maps

If a vertex map is contiguous to the identity, straight-line interpolation
between a lottery and its pushed-forward lottery stays in the variable-size
complex's geometric realization. This is the common topological mechanism for
the dummy-saturation and forced-item retractions in the BF induction.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped Classical

/-- The straight segment between two points of a finite probability simplex. -/
noncomputable def variableLotterySegment {α : Type*} [Fintype α]
    (x y : stdSimplex ℝ α) (t : Set.Icc (0 : ℝ) 1) :
    stdSimplex ℝ α :=
  ⟨(1 - t.1) • x.1 + t.1 • y.1,
    (convex_stdSimplex ℝ α) x.2 y.2
      (sub_nonneg.mpr t.2.2) t.2.1 (by ring)⟩

/-- The SAME support calculation for any finite probability simplex.
This generality lets the recording graph reuse the existing interpolation
without encoding its vertices as variable-dummy profiles. -/
theorem finiteSimplexSupport_variableLotterySegment_subset
    {V:Type*} [Fintype V] (x y:stdSimplex ℝ V) (t:Set.Icc (0:ℝ) 1):
    finiteSimplexSupport (variableLotterySegment x y t)⊆
      finiteSimplexSupport x∪finiteSimplexSupport y:=by
  classical
  intro v hv
  by_contra hnot
  have hxNot:v∉finiteSimplexSupport x:=fun h=>hnot (Finset.mem_union_left _ h)
  have hyNot:v∉finiteSimplexSupport y:=fun h=>hnot (Finset.mem_union_right _ h)
  have hx0:x.1 v=0:=by
    exact le_antisymm (le_of_not_gt (fun h=>hxNot ((mem_finiteSimplexSupport_iff x v).mpr h))) (x.2.1 v)
  have hy0:y.1 v=0:=by
    exact le_antisymm (le_of_not_gt (fun h=>hyNot ((mem_finiteSimplexSupport_iff y v).mpr h))) (y.2.1 v)
  have hPos:0<(variableLotterySegment x y t).1 v:=
    (mem_finiteSimplexSupport_iff _ v).mp hv
  simp only [variableLotterySegment,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hx0,hy0,
    mul_zero,add_zero] at hPos
  exact lt_irrefl _ hPos

/-- Positive support of an interpolated lottery lies in the union of endpoint
supports. -/
theorem variableLotterySegment_support_subset {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (x y : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (t : Set.Icc (0 : ℝ) 1) :
    variableLotterySupport (variableLotterySegment x y t) ⊆
      variableLotterySupport x ∪ variableLotterySupport y := by
  simpa only [variableLotterySupport,Finset.subset_iff,Finset.mem_union] using
    finiteSimplexSupport_variableLotterySegment_subset x y t

/-- Interpolation stays in the realization whenever the endpoint supports
form a common face. -/
theorem variableLotterySegment_mem_of_union_face {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (x y : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (hFace : IsVariableUnlabeledFamily
      (variableLotterySupport x ∪ variableLotterySupport y))
    (t : Set.Icc (0 : ℝ) 1) :
    variableLotterySegment x y t ∈ variableLotterySpace k m D r c := by
  exact variableUnlabeled_mono
    (variableLotterySegment_support_subset x y t) hFace

/-- A vertex map contiguous to the identity can be interpolated on every
point of the geometric realization. -/
theorem variableLotterySegment_mem_of_contiguous_map {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (f : VariableUnlabeledVertex k m D r c →
      VariableUnlabeledVertex k m D r c)
    (hContig : ∀ S : Finset (VariableUnlabeledVertex k m D r c),
      IsVariableUnlabeledFamily S →
        IsVariableUnlabeledFamily (S ∪ S.image f))
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (hlot : lot ∈ variableLotterySpace k m D r c)
    (t : Set.Icc (0 : ℝ) 1) :
    variableLotterySegment lot (stdSimplex.map f lot) t ∈
      variableLotterySpace k m D r c := by
  have hFace := hContig (variableLotterySupport lot) hlot
  have hSub :
      variableLotterySupport lot ∪
        variableLotterySupport (stdSimplex.map f lot) ⊆
      variableLotterySupport lot ∪ (variableLotterySupport lot).image f := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _
        (variableLotterySupport_map_subset f lot hp)
  exact variableLotterySegment_mem_of_union_face
    lot (stdSimplex.map f lot)
    (variableUnlabeled_mono hSub hFace) t

/-- The BF dummy-saturation map has a geometric interpolation inside the
variable-size auxiliary complex. -/
theorem variableLotterySegment_mem_saturation {k m : ℕ}
    {D : Finset (Fin m)} {r c : Fin k → ℕ}
    (u : Fin k → ℕ)
    (huR : ∀ i, u i ≤ r i)
    (huC : ∀ i, u i ≤ c i)
    (hBudget : (∑ i : Fin k, u i) ≤ D.card)
    (hBound : ∀ p : VariableUnlabeledVertex k m D r c,
      ∀ i, (p.1 i).2 ≤ u i)
    (lot : stdSimplex ℝ (VariableUnlabeledVertex k m D r c))
    (hlot : lot ∈ variableLotterySpace k m D r c)
    (t : Set.Icc (0 : ℝ) 1) :
    variableLotterySegment lot
      (stdSimplex.map
        (saturateVariableVertex u huR huC hBudget hBound) lot) t ∈
      variableLotterySpace k m D r c := by
  exact variableLotterySegment_mem_of_contiguous_map
    (saturateVariableVertex u huR huC hBudget hBound)
    (fun S hS => variableFace_union_saturation
      u huR huC hBudget hBound S hS)
    lot hlot t

end FairDivision.Topology
