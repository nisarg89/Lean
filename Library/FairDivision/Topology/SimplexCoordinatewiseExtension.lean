import FairDivision.Topology.SimplexEuclideanBall
import FairDivision.Topology.SphericalCapMaximumExtension

/-!
# The manuscript's common-region extension on a simplex face

For a face of dimension at least two, identify the entire face with one
Euclidean closed unit ball. Transport the already prescribed boundary map
to the unit sphere and use, for EVERY coordinate, the SAME closed region
`dist x y ≤ 2 * (1 - ‖x‖)`. The resulting coordinate maxima are continuous,
preserve the boundary, and admit one attaining boundary point per coordinate.

This is the higher-dimensional-face construction in BF Section 5. The
finite-face pasting argument uses only the exact boundary agreement and the
attaining witnesses below; the region and the ball identification remain
fixed across coordinates throughout the construction.
-/

set_option autoImplicit false

namespace FairDivision.Topology.SimplexCoordinatewiseExtension

/-- The union of the proper faces, expressed by a zero barycentric coordinate. -/
abbrev SimplexCoordinateBoundary (V : Type*) [Fintype V] := SimplexBoundary V

/-- Extend the boundary scores by the manuscript's coordinate maxima over
one common moving spherical cap. The last two clauses record precisely the
attainment and domination properties needed to retain each owner's bundle
and shortening witnesses. -/
theorem exists_extension (V : Type*) [Fintype V] {n : ℕ}
    (hCard : 3≤Fintype.card V)
    (f : C(SimplexCoordinateBoundary V,Fin n→ℝ)) :
    ∃ F : C(stdSimplex ℝ V,Fin n→ℝ),
      (∀x : SimplexCoordinateBoundary V,F x.1=f x) ∧
      ∀x,∃witness : Fin n→SimplexCoordinateBoundary V,
        (∀i,F x i=f (witness i) i) ∧
        (∀i j,f (witness j) i≤F x i) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let E := euclideanSimplexZeroSum V
  let ball := simplexEuclideanBallHomeomorph V
  let boundary := simplexBoundaryEuclideanSphereHomeomorph V
  let sphereScores : C(UnitSphere E,Fin n→ℝ) :=
    f.comp (boundary.symm : C(UnitSphere E,SimplexCoordinateBoundary V))
  have hRank : 1<Module.rank ℝ E := euclideanSimplexZeroSum_one_lt_rank V hCard
  have hUnit : Nonempty (UnitSphere E) :=
    euclideanSimplexZeroSum_unitSphere_nonempty V (by omega)
  let F : C(stdSimplex ℝ V,Fin n→ℝ) :=
    ⟨fun x=>sphericalCapMaximum sphereScores (ball x),
      (continuous_sphericalCapMaximum hRank hUnit sphereScores sphereScores.continuous).comp
        ball.continuous⟩
  refine ⟨F,?_,?_⟩
  · intro x
    have hx : ‖(ball x.1:E)‖=1 :=
      (simplexEuclideanBallHomeomorph_boundary_iff V x.1).mpr x.2
    change sphericalCapMaximum sphereScores (ball x.1)=f x
    rw [sphericalCapMaximum_boundary sphereScores (ball x.1) hx]
    change f (boundary.symm (boundary x))=f x
    rw [boundary.symm_apply_apply]
  · intro x
    obtain ⟨w,_hw,hAttain,hDom⟩:=
      sphericalCapMaximum_finite_witness hUnit sphereScores sphereScores.continuous (ball x)
    refine ⟨fun i=>boundary.symm (w i),?_,?_⟩
    · intro i
      exact hAttain i
    · intro i j
      exact hDom i j

end FairDivision.Topology.SimplexCoordinatewiseExtension
