import FairDivision.Topology.SphericalCapBasic

/-!
# Radial selection from a spherical cap

The normalized radial point belongs to every noncentral cap.  We use a
fixed unit point at the center; this selection is continuous at all
nonzero ball points, in particular at the boundary where caps are singletons.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open Filter _root_.Topology
open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A total radial point; its value at the center is irrelevant to the
boundary-continuity argument. -/
noncomputable def radialCapPoint (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) : UnitSphere E :=
  if hx : (x : E) = 0 then Classical.choice hUnit
  else ⟨(‖(x : E)‖)⁻¹ • (x : E), by
    have hn : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hx
    simp [norm_smul, Real.norm_eq_abs, hn.ne']⟩

theorem radialCapPoint_scale (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) (hx : (x : E) ≠ 0) :
    (x : E) = ‖(x : E)‖ • (radialCapPoint hUnit x : E) := by
  simp [radialCapPoint, hx, smul_smul, (norm_ne_zero_iff.mpr hx)]

theorem radialCapPoint_mem (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) : radialCapPoint hUnit x ∈ sphericalCap x := by
  by_cases hx : (x : E) = 0
  · have hsmall : 3 * ‖(x : E)‖ ≤ 1 := by simp [hx]
    rw [sphericalCap_eq_univ_of_norm_le_third x hsmall]
    trivial
  · let ρ : ℝ := ‖(x : E)‖
    have hρpos : 0 < ρ := norm_pos_iff.mpr hx
    have hρle : ρ ≤ 1 := x.property
    let yv : E := ρ⁻¹ • (x : E)
    have hxy : (x : E) = ρ • yv := by simp [yv, smul_smul, hρpos.ne']
    have hy : ‖yv‖ = 1 := by
      simp [yv, ρ, norm_smul, Real.norm_eq_abs, hρpos.ne']
    have hdist : dist (x : E) yv = 1 - ρ := by
      calc
        dist (x : E) yv = ‖(ρ - 1) • yv‖ := by
          rw [hxy, dist_eq_norm]
          congr 1
          simp [sub_smul]
        _ = 1 - ρ := by
          rw [norm_smul, hy, mul_one, Real.norm_eq_abs]
          rw [abs_of_nonpos (sub_nonpos.mpr hρle)]
          ring
    change dist (x : E) (radialCapPoint hUnit x : E) ≤
      2 * (1 - ‖(x : E)‖)
    have hval : (radialCapPoint hUnit x : E) = yv := by
      simp [radialCapPoint, hx, yv, ρ]
    rw [hval, hdist]
    dsimp [ρ]
    linarith

theorem continuousAt_radialCapPoint (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) (hx : (x : E) ≠ 0) :
    ContinuousAt (radialCapPoint hUnit) x := by
  apply (tendsto_subtype_rng).2
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hraw : ContinuousAt
      (fun z : ClosedUnitBall E => ‖(z : E)‖⁻¹ • (z : E)) x :=
    (continuous_subtype_val.norm.continuousAt.inv₀ hn).smul
      continuous_subtype_val.continuousAt
  have hEv : ∀ᶠ (z : ClosedUnitBall E) in 𝓝 x, (z : E) ≠ 0 :=
    (isOpen_compl_singleton.preimage continuous_subtype_val).mem_nhds
      (by simpa using hx)
  have hEq : (fun z : ClosedUnitBall E =>
      (radialCapPoint hUnit z : E)) =ᶠ[𝓝 x]
      (fun z => ‖(z : E)‖⁻¹ • (z : E)) := by
    filter_upwards [hEv] with z hz
    simp [radialCapPoint, hz]
  exact hraw.congr_of_eventuallyEq hEq

theorem radialCapPoint_boundary (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) (hx : ‖(x : E)‖ = 1) :
    radialCapPoint hUnit x = (⟨(x : E), hx⟩ : UnitSphere E) := by
  have hne : (x : E) ≠ 0 := by
    intro h
    simp [h] at hx
  apply Subtype.ext
  simp [radialCapPoint, hne, hx]

end FairDivision.Topology
