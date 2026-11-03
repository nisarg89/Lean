import FairDivision.Topology.SphericalCapStrict
import FairDivision.Topology.SphericalCapBasic

/-!
# Angular bounds on ordinary spherical-cap boundary points

A boundary point of a proper, positive-radius cap is neither its radial
center nor its antipode. This is the nondegenerate case in which the
normalized blend produces strict cap points.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem capBoundary_inner_bounds
    (u y : UnitSphere E) {ρ : ℝ}
    (hρpos : 0 < ρ) (hρlarge : 1 < 3 * ρ) (hρsmall : ρ < 1)
    (hBoundary : dist (ρ • (u : E)) (y : E) = 2 * (1 - ρ)) :
    -1 < ⟪(u : E), (y : E)⟫_ℝ ∧
      ⟪(u : E), (y : E)⟫_ℝ < 1 := by
  have hLo := neg_one_le_real_inner_of_norm_eq_one u.property y.property
  have hHi := real_inner_le_one_of_norm_eq_one u.property y.property
  constructor
  · by_contra h
    have hc : ⟪(u : E), (y : E)⟫_ℝ = -1 := by linarith
    have hneg : (u : E) = -(y : E) :=
      (inner_eq_neg_one_iff_of_norm_eq_one u.property y.property).mp hc
    have hyneg : (y : E) = -(u : E) := by
      simpa using (congrArg Neg.neg hneg).symm
    have hmax := (dist_radial_unit_eq_max_iff (u : E) (y : E)
      u.property y.property hρpos).2 hyneg
    rw [hBoundary] at hmax
    linarith
  · by_contra h
    have hc : ⟪(u : E), (y : E)⟫_ℝ = 1 := by linarith
    have heq : (u : E) = (y : E) :=
      (inner_eq_one_iff_of_norm_eq_one u.property y.property).mp hc
    have hρnorm : ‖ρ • (u : E)‖ = ρ := by
      simp [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt hρpos), u.property]
    have hsq : (dist (ρ • (u : E)) (y : E)) ^ 2 =
        ρ ^ 2 - 2 * ρ * ⟪(u : E), (y : E)⟫_ℝ + 1 := by
      rw [dist_eq_norm, norm_sub_sq_real, hρnorm, y.property,
        real_inner_smul_left]
      ring
    rw [hBoundary, hc] at hsq
    nlinarith [sq_pos_of_pos (sub_pos.mpr hρsmall)]

end FairDivision.Topology
