import FairDivision.Topology.NerveConnectivity.FiniteSimplexAffinePoint
import FairDivision.Topology.NerveConnectivity.BarycentricGeometricRealization
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Unit-coordinate geometric realization

When each vertex is the corresponding unit coordinate vector, the union
of geometric face hulls agrees exactly with the probability-simplex
realization of an abstract simplicial complex.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u

private theorem unitCoordinateFace_convex
    {V : Type u} [Fintype V] (F : Finset V) :
    Convex ℝ {x : V → ℝ | x ∈ stdSimplex ℝ V ∧
      ∀ i : V, i ∉ F → x i = 0} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_stdSimplex ℝ V) hx.1 hy.1 ha hb hab, ?_⟩
  intro i hi
  simp [Pi.add_apply, Pi.smul_apply, hx.2 i hi, hy.2 i hi]

private theorem unitFaceHull_subset_coordinateFace
    {V : Type u} [Fintype V] (F : Finset V) :
    convexHull ℝ (finiteSimplexUnitVertex '' (F : Set V)) ⊆
      {x : V → ℝ | x ∈ stdSimplex ℝ V ∧
        ∀ i : V, i ∉ F → x i = 0} := by
  classical
  apply convexHull_min _ (unitCoordinateFace_convex F)
  intro x hx
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨single_mem_stdSimplex ℝ i, ?_⟩
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hj (h ▸ hi)
  simp [finiteSimplexUnitVertex, Pi.single_apply, hji, hji.symm]

/-- A point of the unit-coordinate geometric realization is the coordinate
vector of a point of the probability-simplex realization. -/
theorem geometricUnitRealization_exists_simplexPoint
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (x : V → ℝ)
    (hx : x ∈ geometricSimplicialRealization K finiteSimplexUnitVertex) :
    ∃ w : simplicialRealization K, w.1.1 = x := by
  obtain ⟨F, hF, hxF⟩ := hx
  have hface := unitFaceHull_subset_coordinateFace F hxF
  let w : stdSimplex ℝ V := ⟨x, hface.1⟩
  have hsupport : FairDivision.Topology.finiteSimplexSupport w ⊆ F := by
    intro i hi
    by_contra hnot
    have hzero : w.1 i = 0 := hface.2 i hnot
    have hpos := (FairDivision.Topology.mem_finiteSimplexSupport_iff w i).1 hi
    exact (ne_of_gt hpos) hzero
  have hwK : FairDivision.Topology.finiteSimplexSupport w ∈ K :=
    (K.isRelLowerSet_faces hF).2 hsupport
      (FairDivision.Topology.finiteSimplexSupport_nonempty w)
  exact ⟨⟨w, hwK⟩, rfl⟩

/-- Conversely, each realized probability point belongs to its support
face's geometric hull. -/
theorem simplexPoint_mem_geometricUnitRealization
    {V : Type u} [Fintype V]
    (K : PreAbstractSimplicialComplex V)
    (w : simplicialRealization K) :
    w.1.1 ∈ geometricSimplicialRealization K finiteSimplexUnitVertex := by
  have h := finiteSimplexAffinePoint_mem_supportFace
    finiteSimplexUnitVertex w.1
  rw [finiteSimplexAffinePoint_unitVertices] at h
  exact ⟨FairDivision.Topology.finiteSimplexSupport w.1, w.2, h⟩

end FairDivision.Topology.NerveConnectivity
