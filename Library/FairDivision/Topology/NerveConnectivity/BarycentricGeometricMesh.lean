import FairDivision.Topology.NerveConnectivity.BarycentricMeshIteration
import Mathlib.Analysis.Normed.Module.Convex

/-!
# From a vertex mesh to a geometric simplex mesh

The diameter of a convex hull is controlled by its vertices. Thus the
iterated barycentric vertex estimate also bounds every pair of points in
each geometric simplex, the form needed for uniform-continuity arguments.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- A pairwise vertex bound controls all points in every geometric face. -/
theorem VertexMeshBound.convexHull
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : PreAbstractSimplicialComplex V}
    {p : V → E} {δ : ℝ}
    (hmesh : VertexMeshBound K p δ)
    (F : Finset V) (hF : F ∈ K)
    (x y : E)
    (hx : x ∈ convexHull ℝ (p '' (F : Set V)))
    (hy : y ∈ convexHull ℝ (p '' (F : Set V))) :
    dist x y ≤ δ := by
  obtain ⟨x', hx', y', hy', hxy⟩ := convexHull_exists_dist_ge2 hx hy
  obtain ⟨i, hi, rfl⟩ := hx'
  obtain ⟨j, hj, rfl⟩ := hy'
  exact hxy.trans (hmesh F hF i hi j hj)

/-- Every geometric simplex in the `n`-th barycentric subdivision has
mesh at most the explicit geometric-rate bound. -/
theorem iteratedBarycentric_geometricMeshBound
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V)
    (p : V → E) (δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (hmesh : VertexMeshBound K p δ)
    (n : ℕ)
    (F : Finset (iteratedBarycentricVertex V n))
    (hF : F ∈ iteratedBarycentricComplex K n)
    (x y : E)
    (hx : x ∈ convexHull ℝ
      (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n))))
    (hy : y ∈ convexHull ℝ
      (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n)))) :
    dist x y ≤ (barycentricMeshFactor N) ^ n * δ :=
  (iteratedBarycentric_vertexMeshBound K p δ N hN hδ hsize hmesh n).convexHull
    F hF x y hx hy

/-- Given any positive tolerance, sufficiently many barycentric subdivisions
make each geometric simplex smaller than that tolerance. -/
theorem exists_iteratedBarycentric_geometricMesh_lt
    {V : Type u} {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V)
    (p : V → E) (δ : ℝ) (N : ℕ)
    (hN : 0 < N) (hδ : 0 ≤ δ)
    (hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N)
    (hmesh : VertexMeshBound K p δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (F : Finset (iteratedBarycentricVertex V n))
      (hF : F ∈ iteratedBarycentricComplex K n)
      (x y : E)
      (hx : x ∈ convexHull ℝ
        (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n))))
      (hy : y ∈ convexHull ℝ
        (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n)))),
      dist x y < ε := by
  have hc := barycentricMeshFactor_lt_one N hN
  by_cases hδzero : δ = 0
  · refine ⟨0, ?_⟩
    intro F hF x y hx hy
    have h := iteratedBarycentric_geometricMeshBound
      K p δ N hN hδ hsize hmesh 0 F hF x y hx hy
    simp only [pow_zero, one_mul, hδzero] at h
    exact h.trans_lt hε
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδzero)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hδpos) hc
    refine ⟨n, ?_⟩
    intro F hF x y hx hy
    have h := iteratedBarycentric_geometricMeshBound
      K p δ N hN hδ hsize hmesh n F hF x y hx hy
    exact h.trans_lt ((lt_div_iff₀ hδpos).mp hn)

end FairDivision.Topology.NerveConnectivity
