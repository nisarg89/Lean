import FairDivision.Topology.SphericalCapInterior
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Lower hemicontinuity of moving spherical caps

Interior caps have dense strict points. At a boundary point the cap is a
singleton and the normalized radial point of nearby ball points gives a
continuous feasible selection.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open Filter _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sphericalCap_lowerHemicontinuous
    (hRank : 1 < Module.rank ℝ E) :
    LowerHemicontinuous (sphericalCap (E := E)) := by
  rw [lowerHemicontinuous_iff]
  intro x
  rw [lowerHemicontinuousAt_iff]
  intro U hU hMeet
  obtain ⟨y, hyCap, hyU⟩ := hMeet
  by_cases hxInterior : ‖(x : E)‖ < 1
  · have hClosure := sphericalCap_mem_closure_strict_of_interior
      hRank x hxInterior y hyCap
    obtain ⟨z, hzU, hzStrict⟩ :=
      (mem_closure_iff.mp hClosure) U hU hyU
    have hOpen : IsOpen {x' : ClosedUnitBall E |
        dist (x' : E) (z : E) < 2 * (1 - ‖(x' : E)‖)} :=
      isOpen_lt (by fun_prop) (by fun_prop)
    have hEv : ∀ᶠ (x' : ClosedUnitBall E) in 𝓝 x,
        dist (x' : E) (z : E) < 2 * (1 - ‖(x' : E)‖) :=
      hOpen.mem_nhds hzStrict
    filter_upwards [hEv] with x' hx'
    exact ⟨z, le_of_lt hx', hzU⟩
  · have hxBoundary : ‖(x : E)‖ = 1 :=
      le_antisymm x.property (le_of_not_gt hxInterior)
    have hxNe : (x : E) ≠ 0 := by
      intro h
      simp [h] at hxBoundary
    let hUnit : Nonempty (UnitSphere E) := ⟨y⟩
    have hyEq : y = (⟨(x : E), hxBoundary⟩ : UnitSphere E) := by
      rw [sphericalCap_eq_singleton_of_boundary x hxBoundary] at hyCap
      simpa using hyCap
    have hRadEq : radialCapPoint hUnit x = y := by
      rw [radialCapPoint_boundary hUnit x hxBoundary]
      exact hyEq.symm
    have hEv : ∀ᶠ x' in 𝓝 x, radialCapPoint hUnit x' ∈ U :=
      (continuousAt_radialCapPoint hUnit x hxNe).eventually
        (hU.mem_nhds (by rw [hRadEq]; exact hyU))
    filter_upwards [hEv] with x' hx'
    exact ⟨radialCapPoint hUnit x', radialCapPoint_mem hUnit x', hx'⟩

end FairDivision.Topology
