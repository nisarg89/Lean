import FairDivision.Topology.NerveConnectivity.SimplicialCover
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Affine points in a finite simplicial realization

A probability vector supported on a face evaluates to a point of that
face's geometric convex hull. This is the geometric bridge used when
turning an abstract barycentric mesh estimate into a source-side estimate.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Evaluate probability barycentric coordinates at assigned vertex points. -/
noncomputable def finiteSimplexAffinePoint
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (w : stdSimplex ℝ V) : E :=
  ∑ i : V, w.1 i • p i

/-- Evaluation at fixed vertex points varies continuously with the
barycentric coordinates. -/
theorem finiteSimplexAffinePoint_continuous
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) : Continuous (finiteSimplexAffinePoint p) := by
  unfold finiteSimplexAffinePoint
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

/-- A point supported on a nonempty face lies in its geometric simplex. -/
theorem finiteSimplexAffinePoint_mem_convexHull
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (w : stdSimplex ℝ V)
    (F : Finset V) (hF : F.Nonempty)
    (hsupport : FairDivision.Topology.finiteSimplexSupport w ⊆ F) :
    finiteSimplexAffinePoint p w ∈ convexHull ℝ (p '' (F : Set V)) := by
  classical
  let i₀ : V := hF.choose
  let q : V → E := fun i => if i ∈ F then p i else p i₀
  have hq : ∀ i : V, q i ∈ p '' (F : Set V) := by
    intro i
    by_cases hi : i ∈ F
    · exact ⟨i, hi, by simp [q, hi]⟩
    · exact ⟨i₀, hF.choose_spec, by simp [q, hi]⟩
  have hzero : ∀ i : V, i ∉ F → w.1 i = 0 := by
    intro i hi
    have hnot : i ∉ FairDivision.Topology.finiteSimplexSupport w :=
      fun his => hi (hsupport his)
    have hnotpos : ¬ 0 < w.1 i :=
      fun hpos => hnot ((FairDivision.Topology.mem_finiteSimplexSupport_iff w i).2 hpos)
    exact le_antisymm (le_of_not_gt hnotpos) (w.2.1 i)
  have heq : ∑ i : V, w.1 i • q i = finiteSimplexAffinePoint p w := by
    unfold finiteSimplexAffinePoint
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ F
    · simp [q, hi]
    · simp [q, hi, hzero i hi]
  exact mem_convexHull_of_exists_fintype (fun i : V => w.1 i) q
    (fun i => w.2.1 i) w.2.2 hq heq

/-- Every realized point evaluates in the convex hull of its support face. -/
theorem finiteSimplexAffinePoint_mem_supportFace
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : V → E) (w : stdSimplex ℝ V) :
    finiteSimplexAffinePoint p w ∈ convexHull ℝ
      (p '' (FairDivision.Topology.finiteSimplexSupport w : Set V)) :=
  finiteSimplexAffinePoint_mem_convexHull p w
    (FairDivision.Topology.finiteSimplexSupport w)
    (FairDivision.Topology.finiteSimplexSupport_nonempty w) Finset.Subset.rfl

/-- A standard-simplex vertex as a unit coordinate vector. -/
noncomputable def finiteSimplexUnitVertex
    {V : Type u} [Fintype V] (i : V) : V → ℝ := by
  classical
  exact Pi.single i 1

/-- Affine evaluation at the unit vertices recovers the original
probability coordinates. -/
theorem finiteSimplexAffinePoint_unitVertices
    {V : Type u} [Fintype V] (w : stdSimplex ℝ V) :
    finiteSimplexAffinePoint finiteSimplexUnitVertex w = w.1 := by
  classical
  funext i
  simp [finiteSimplexAffinePoint, finiteSimplexUnitVertex,
    Pi.single_apply, smul_eq_mul]

end FairDivision.Topology.NerveConnectivity
