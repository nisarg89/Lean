import FairDivision.Topology.SphericalCapBasic
import FairDivision.Topology.SphericalCapScalar
import FairDivision.Topology.SphericalCapStrict

/-!
# Short sphere path toward a radial center

This constructs the actual nearby unit vectors used to perturb an ordinary
cap-boundary point into the strict cap. The path is needed only for positive
small parameters; its arbitrary value elsewhere makes it a total Lean map.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open Filter _root_.Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shortUnitBlend (u y : UnitSphere E) (t : ℝ) : UnitSphere E :=
  if ht : 0 < t ∧ t < 1 / 2 then
    ⟨unitBlend (u : E) (y : E) t,
      unitBlend_norm (u : E) (y : E) u.property y.property ht.1 ht.2⟩
  else y

theorem shortUnitBlend_tendsto (u y : UnitSphere E) :
    Tendsto (shortUnitBlend u y) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
  have hSmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  have hPos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hEv : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 / 2 := hPos.and hSmall
  have hRaw : Tendsto (unitBlend (u : E) (y : E))
      (𝓝[>] (0 : ℝ)) (𝓝 (y : E)) := by
    have hAt : Tendsto (unitBlend (u : E) (y : E))
        (𝓝[>] (0 : ℝ)) (𝓝 (unitBlend (u : E) (y : E) 0)) :=
      (continuousAt_unitBlend_zero (u : E) (y : E) y.property).mono_left
        nhdsWithin_le_nhds
    simpa only [unitBlend_zero (u : E) (y : E) y.property] using hAt
  have hEq : (fun t => (shortUnitBlend u y t : E)) =ᶠ[𝓝[>] (0 : ℝ)]
      unitBlend (u : E) (y : E) := by
    filter_upwards [hEv] with t ht
    simp only [shortUnitBlend, dif_pos ht]
  apply (tendsto_subtype_rng).2
  exact Filter.Tendsto.congr' hEq.symm hRaw

theorem unitSphere_mem_closure_dist_lt_of_nondegenerate
    (u y : UnitSphere E) {ρ : ℝ} (hρ : 0 < ρ)
    (hcLo : -1 < ⟪(u : E), (y : E)⟫_ℝ)
    (hcHi : ⟪(u : E), (y : E)⟫_ℝ < 1) :
    y ∈ closure {z : UnitSphere E |
      dist (ρ • (u : E)) (z : E) < dist (ρ • (u : E)) (y : E)} := by
  have hSmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
      nhdsWithin_le_nhds
  have hPos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hEv : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < 1 / 2 := hPos.and hSmall
  apply mem_closure_of_tendsto (shortUnitBlend_tendsto u y)
  filter_upwards [hEv] with t ht
  have hInner := unitBlend_inner_gt (u : E) (y : E)
    u.property y.property ht.1 ht.2 hcLo hcHi
  have hNorm := unitBlend_norm (u : E) (y : E)
    u.property y.property ht.1 ht.2
  have hDist := dist_radial_unit_strict (u : E) (y : E)
    (unitBlend (u : E) (y : E) t) u.property y.property hNorm hρ hInner
  simpa only [shortUnitBlend, dif_pos ht] using hDist

end FairDivision.Topology
