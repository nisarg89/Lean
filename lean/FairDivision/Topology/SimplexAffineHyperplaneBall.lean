import FairDivision.Topology.SimplexAffineHyperplaneBounded

/-!
# A ball model for each finite simplex face

Mathlib's gauge-rescaling homeomorphism applies after translating a simplex
into its sum-zero affine hyperplane. It sends the translated simplex and its
frontier to the closed unit ball and unit sphere respectively. A later module
will identify the frontier with the union of proper faces.
-/

set_option autoImplicit false

namespace FairDivision.Topology

/-- A finite simplex has a ball model in its affine hyperplane, with its
frontier corresponding to the unit sphere. -/
theorem exists_centeredSimplex_ball_homeomorph
    (V : Type*) [Fintype V] [Nonempty V] :
    ∃ h : simplexZeroSum V ≃ₜ simplexZeroSum V,
      h '' centeredSimplex V = Metric.closedBall 0 1 ∧
      h '' frontier (centeredSimplex V) = Metric.sphere 0 1 := by
  obtain ⟨h, _, hClosure, hFrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (centeredSimplex_convex V)
      (centeredSimplex_interior_nonempty V)
      (centeredSimplex_isBounded V)
  have hClosed : closure (centeredSimplex V) = centeredSimplex V :=
    (centeredSimplex_isClosed V).closure_eq
  rw [hClosed] at hClosure
  exact ⟨h, hClosure, hFrontier⟩

end FairDivision.Topology
