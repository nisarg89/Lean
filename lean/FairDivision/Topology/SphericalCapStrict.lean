import FairDivision.Topology.SphericalCapScalar

/-!
# Moving inward within a spherical cap

For a nonzero radial center, an increase in the angular inner product
strictly decreases chordal distance to the center. Together with
`unitBlend_inner_gt`, this gives strict feasible points near an ordinary
spherical-cap boundary point.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dist_radial_unit_strict
    (u y z : E) (hu : ‖u‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hinner : ⟪u, y⟫_ℝ < ⟪u, z⟫_ℝ) :
    dist (ρ • u) z < dist (ρ • u) y := by
  have hρnorm : ‖ρ • u‖ = ρ := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hρ), hu]
  have hsqz : (dist (ρ • u) z) ^ 2 = ρ ^ 2 - 2 * ρ * ⟪u, z⟫_ℝ + 1 := by
    rw [dist_eq_norm, norm_sub_sq_real, hρnorm, hz,
      real_inner_smul_left]
    ring
  have hsqy : (dist (ρ • u) y) ^ 2 = ρ ^ 2 - 2 * ρ * ⟪u, y⟫_ℝ + 1 := by
    rw [dist_eq_norm, norm_sub_sq_real, hρnorm, hy,
      real_inner_smul_left]
    ring
  have hsq : (dist (ρ • u) z) ^ 2 < (dist (ρ • u) y) ^ 2 := by
    rw [hsqz, hsqy]
    nlinarith [mul_pos hρ (sub_pos.mpr hinner)]
  have hzNonneg : 0 ≤ dist (ρ • u) z := dist_nonneg
  have hyNonneg : 0 ≤ dist (ρ • u) y := dist_nonneg
  nlinarith

/-- The farthest unit vector from a nonzero radial point is its antipode. -/
theorem dist_radial_unit_eq_max_iff
    (u y : E) (hu : ‖u‖ = 1) (hy : ‖y‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ) :
    dist (ρ • u) y = 1 + ρ ↔ y = -u := by
  constructor
  · intro hd
    have hρnorm : ‖ρ • u‖ = ρ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hρ), hu]
    have hsq : (dist (ρ • u) y) ^ 2 =
        ρ ^ 2 - 2 * ρ * ⟪u, y⟫_ℝ + 1 := by
      rw [dist_eq_norm, norm_sub_sq_real, hρnorm, hy,
        real_inner_smul_left]
      ring
    have hinner : ⟪u, y⟫_ℝ = -1 := by
      rw [hd] at hsq
      have hProduct : ρ * (⟪u, y⟫_ℝ + 1) = 0 := by nlinarith [hsq]
      have hFactor : ⟪u, y⟫_ℝ + 1 = 0 :=
        (mul_eq_zero.mp hProduct).resolve_left hρ.ne'
      linarith
    have hneg : u = -y :=
      (inner_eq_neg_one_iff_of_norm_eq_one hu hy).mp hinner
    simpa using (congrArg Neg.neg hneg).symm
  · intro hyNeg
    subst y
    rw [dist_eq_norm]
    have hsmul : ρ • u - -u = (ρ + 1) • u := by
      simp [add_smul, sub_eq_add_neg]
    rw [hsmul, norm_smul, hu]
    simp [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ ρ + 1), add_comm]

end FairDivision.Topology
