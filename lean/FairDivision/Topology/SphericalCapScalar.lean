import Mathlib

/-!
# Scalar inequality for strict spherical-cap perturbations

For unit vectors `u` and `y`, normalize a small convex blend toward `u`.
The bounds on its norm imply that the inner product with `u` increases
strictly whenever the original angle lies strictly between zero and pi.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped InnerProductSpace

private theorem blend_scalar_strict
    {t c b : ℝ} (ht0 : 0 < t) (htHalf : t < 1 / 2)
    (hcLo : -1 < c) (hcHi : c < 1)
    (hbLo : 1 - 2 * t ≤ b) (hbHi : b ≤ 1) :
    b * c < (1 - t) * c + t := by
  by_cases hc : 0 ≤ c
  · have hbc : b * c ≤ c := by nlinarith
    have hpositive : 0 < t * (1 - c) := mul_pos ht0 (by linarith)
    nlinarith
  · have hcLt : c < 0 := lt_of_not_ge hc
    have hbc : b * c ≤ (1 - 2 * t) * c := by
      exact mul_le_mul_of_nonpos_right hbLo (le_of_lt hcLt)
    have hpositive : 0 < t * (1 + c) := mul_pos ht0 (by linarith)
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalize a short linear blend of two unit vectors. -/
noncomputable def unitBlend (u y : E) (t : ℝ) : E :=
  (‖(1 - t) • y + t • u‖)⁻¹ • ((1 - t) • y + t • u)

/-- The normalization leaves the original unit vector unchanged at the
initial endpoint. This equality is used explicitly when changing the target
of the one-sided convergence statement. -/
@[simp] theorem unitBlend_zero (u y : E) (hy : ‖y‖ = 1) :
    unitBlend u y 0 = y := by
  simp [unitBlend, hy]

private theorem unitBlend_bounds (u y : E) (hu : ‖u‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht0 : 0 < t) (htHalf : t < 1 / 2) :
    1 - 2 * t ≤ ‖(1 - t) • y + t • u‖ ∧
      ‖(1 - t) • y + t • u‖ ≤ 1 := by
  have ht1 : 0 ≤ 1 - t := by linarith
  have ht : 0 ≤ t := le_of_lt ht0
  have hnormY : ‖(1 - t) • y‖ = 1 - t := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht1, hy]
  have hnormU : ‖t • u‖ = t := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hu]
  constructor
  · have htri := norm_add_le ((1 - t) • y + t • u) (-(t • u))
    have hcancel : ((1 - t) • y + t • u) + -(t • u) = (1 - t) • y := by abel
    rw [hcancel, hnormY, norm_neg, hnormU] at htri
    linarith
  · have htri := norm_add_le ((1 - t) • y) (t • u)
    rw [hnormY, hnormU] at htri
    linarith

theorem unitBlend_norm (u y : E) (hu : ‖u‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht0 : 0 < t) (htHalf : t < 1 / 2) :
    ‖unitBlend u y t‖ = 1 := by
  obtain ⟨hlo, _⟩ := unitBlend_bounds u y hu hy ht0 htHalf
  have hb : 0 < ‖(1 - t) • y + t • u‖ := by linarith
  unfold unitBlend
  rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg ((1 - t) • y + t • u))]
  exact inv_mul_cancel₀ hb.ne' 

theorem unitBlend_inner_gt (u y : E) (hu : ‖u‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht0 : 0 < t) (htHalf : t < 1 / 2)
    (hcLo : -1 < ⟪u, y⟫_ℝ) (hcHi : ⟪u, y⟫_ℝ < 1) :
    ⟪u, unitBlend u y t⟫_ℝ > ⟪u, y⟫_ℝ := by
  obtain ⟨hbLo, hbHi⟩ := unitBlend_bounds u y hu hy ht0 htHalf
  let b : ℝ := ‖(1 - t) • y + t • u‖
  let c : ℝ := ⟪u, y⟫_ℝ
  have hbPos : 0 < b := by dsimp [b]; linarith
  have hstrict : b * c < (1 - t) * c + t :=
    blend_scalar_strict ht0 htHalf hcLo hcHi hbLo hbHi
  have hinner : ⟪u, (1 - t) • y + t • u⟫_ℝ = (1 - t) * c + t := by
    simp [c, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
  change c < ⟪u, b⁻¹ • ((1 - t) • y + t • u)⟫_ℝ
  rw [real_inner_smul_right, hinner]
  have hdiv : c < ((1 - t) * c + t) / b :=
    (lt_div_iff₀ hbPos).2 (by simpa [mul_comm] using hstrict)
  simpa [div_eq_mul_inv, mul_comm] using hdiv

theorem continuousAt_unitBlend_zero (u y : E) (hy : ‖y‖ = 1) :
    ContinuousAt (unitBlend u y) 0 := by
  let v : ℝ → E := fun t => (1 - t) • y + t • u
  have hv : Continuous v := by fun_prop
  have hv0 : v 0 = y := by simp [v]
  have hnz : ‖v 0‖ ≠ 0 := by simp [hv0, hy]
  have hcont : ContinuousAt (fun t => (‖v t‖)⁻¹ • v t) 0 :=
    (hv.norm.continuousAt.inv₀ hnz).smul hv.continuousAt
  change ContinuousAt (fun t =>
    (‖(1 - t) • y + t • u‖)⁻¹ • ((1 - t) • y + t • u)) 0
  simpa only [v] using hcont

end FairDivision.Topology
