import FairDivision.Topology.FiniteSimplexSupport
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Straight segments in a finite probability simplex

Shared by the BF auxiliary-complex homotopies and the generic barycentric
neighborhood deformation retraction. The support of an interpolated point
stays inside the union of the endpoint supports.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology

/-- The segment between two finite probability vectors. -/
noncomputable def finiteSimplexSegment {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (t : I) : stdSimplex ℝ V :=
  ⟨(1 - t.1) • x.1 + t.1 • y.1,
    (convex_stdSimplex ℝ V) x.2 y.2
      (sub_nonneg.mpr t.2.2) t.2.1 (by ring)⟩

/-- Positive support along a segment lies in the union of endpoint supports. -/
theorem finiteSimplexSegment_support_subset {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (t : I) :
    finiteSimplexSupport (finiteSimplexSegment x y t) ⊆
      finiteSimplexSupport x ∪ finiteSimplexSupport y := by
  classical
  intro v hv
  by_contra hnot
  have hxnot : v ∉ finiteSimplexSupport x :=
    fun h => hnot (Finset.mem_union_left _ h)
  have hynot : v ∉ finiteSimplexSupport y :=
    fun h => hnot (Finset.mem_union_right _ h)
  have hx0 : x.1 v = 0 := by
    have hle : ¬ 0 < x.1 v := by
      intro hpos
      exact hxnot ((mem_finiteSimplexSupport_iff x v).2 hpos)
    exact le_antisymm (le_of_not_gt hle) (x.2.1 v)
  have hy0 : y.1 v = 0 := by
    have hle : ¬ 0 < y.1 v := by
      intro hpos
      exact hynot ((mem_finiteSimplexSupport_iff y v).2 hpos)
    exact le_antisymm (le_of_not_gt hle) (y.2.1 v)
  have hpos : 0 < (finiteSimplexSegment x y t).1 v :=
    (mem_finiteSimplexSupport_iff _ v).1 hv
  simp [finiteSimplexSegment, hx0, hy0] at hpos

/-- If the second endpoint uses no new vertices, neither does the segment. -/
theorem finiteSimplexSegment_support_subset_left {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (t : I)
    (hyx : finiteSimplexSupport y ⊆ finiteSimplexSupport x) :
    finiteSimplexSupport (finiteSimplexSegment x y t) ⊆
      finiteSimplexSupport x := by
  intro v hv
  rcases Finset.mem_union.mp (finiteSimplexSegment_support_subset x y t hv) with hv | hv
  · exact hv
  · exact hyx hv

/-- A coordinate positive at both endpoints remains positive throughout
the segment. -/
theorem finiteSimplexSegment_pos_of_pos {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) (t : I) (v : V)
    (hx : 0 < x.1 v) (hy : 0 < y.1 v) :
    0 < (finiteSimplexSegment x y t).1 v := by
  change 0 < (1 - (t : ℝ)) * x.1 v + (t : ℝ) * y.1 v
  by_cases ht : (t : ℝ) = 0
  · simp [ht, hx]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have hleft : 0 ≤ (1 - (t : ℝ)) * x.1 v :=
      mul_nonneg (sub_nonneg.mpr t.2.2) hx.le
    exact add_pos_of_nonneg_of_pos hleft (mul_pos htpos hy)

/-- The segment is jointly continuous in time and both endpoints. -/
theorem finiteSimplexSegment_continuous {V : Type*} [Fintype V] :
    Continuous (fun z : I × (stdSimplex ℝ V × stdSimplex ℝ V) =>
      finiteSimplexSegment z.2.1 z.2.2 z.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun z : I × (stdSimplex ℝ V × stdSimplex ℝ V) =>
    (1 - (z.1 : ℝ)) * z.2.1.1 v + (z.1 : ℝ) * z.2.2.1 v)
  have ht : Continuous (fun z : I × (stdSimplex ℝ V × stdSimplex ℝ V) =>
      (z.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun z : I × (stdSimplex ℝ V × stdSimplex ℝ V) =>
      z.2.1.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hy : Continuous (fun z : I × (stdSimplex ℝ V × stdSimplex ℝ V) =>
      z.2.2.1 v) :=
    (continuous_apply v).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact ((continuous_const.sub ht).mul hx).add (ht.mul hy)

@[simp] theorem finiteSimplexSegment_self {V : Type*} [Fintype V]
    (x : stdSimplex ℝ V) (t : I) :
    finiteSimplexSegment x x t = x := by
  apply Subtype.ext
  funext v
  simp [finiteSimplexSegment]
  ring

@[simp] theorem finiteSimplexSegment_zero {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) :
    finiteSimplexSegment x y (0 : I) = x := by
  apply Subtype.ext
  funext v
  simp [finiteSimplexSegment]

@[simp] theorem finiteSimplexSegment_one {V : Type*} [Fintype V]
    (x y : stdSimplex ℝ V) :
    finiteSimplexSegment x y (1 : I) = y := by
  apply Subtype.ext
  funext v
  simp [finiteSimplexSegment]

end FairDivision.Topology
