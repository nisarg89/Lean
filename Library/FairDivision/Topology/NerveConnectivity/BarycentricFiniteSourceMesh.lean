import FairDivision.Topology.NerveConnectivity.BarycentricGeometricMesh

/-!
# Arbitrarily fine subdivision of a finite geometric complex

For a finite vertex type, the initial vertex diameter and face-cardinality
bounds are automatic. This version exposes only the geometric source and a
positive tolerance, as needed for subordinate source triangulations.
-/

set_option autoImplicit false

namespace FairDivision.Topology.NerveConnectivity

universe u v

/-- Every finite geometric simplicial complex admits a common barycentric
subdivision whose geometric simplices have diameter below any positive
threshold. -/
theorem exists_iteratedBarycentric_finiteSourceMesh_lt
    {V : Type u} {E : Type v} [Fintype V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : PreAbstractSimplicialComplex V) (p : V → E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (F : Finset (iteratedBarycentricVertex V n))
      (hF : F ∈ iteratedBarycentricComplex K n)
      (x y : E)
      (hx : x ∈ convexHull ℝ
        (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n))))
      (hy : y ∈ convexHull ℝ
        (iteratedBarycentricPoint p n '' (F : Set (iteratedBarycentricVertex V n)))),
      dist x y < ε := by
  classical
  let δ : ℝ := Metric.diam (Set.range p)
  let N : ℕ := Fintype.card V + 1
  have hN : 0 < N := by omega
  have hsize : ∀ F : Finset V, F ∈ K → F.card ≤ N := by
    intro F _
    exact (Finset.card_le_card (Finset.subset_univ F)).trans (Nat.le_succ _)
  have hmesh : VertexMeshBound K p δ := by
    intro F _ i _ j _
    exact Metric.dist_le_diam_of_mem (Set.finite_range p).isBounded
      ⟨i, rfl⟩ ⟨j, rfl⟩
  exact exists_iteratedBarycentric_geometricMesh_lt K p δ N hN
    (Metric.diam_nonneg) hsize hmesh ε hε

end FairDivision.Topology.NerveConnectivity
