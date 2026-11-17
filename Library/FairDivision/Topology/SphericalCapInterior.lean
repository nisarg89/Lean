import FairDivision.Topology.SphericalCapBasic
import FairDivision.Topology.SphericalCapRadial
import FairDivision.Topology.SphericalCapBoundaryGeometry
import FairDivision.Topology.SphericalCapBlendPath
import FairDivision.Topology.UnitSpherePerfect

/-!
# Density of strict spherical-cap points in an interior cap

For every point strictly inside the unit ball, each member of its closed
chordal cap is a limit of strict cap members. The ordinary boundary case
uses a normalized short blend toward the radial direction. At the unique
full-cap transition, all sphere points except the antipode are already
strict, and the sphere has no isolated points in dimension at least two.
-/

set_option autoImplicit false

namespace FairDivision.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The open version of a chordal cap. -/
def strictSphericalCap (x : ClosedUnitBall E) : Set (UnitSphere E) :=
  {y | dist (x : E) (y : E) < 2 * (1 - ‖(x : E)‖)}

theorem sphericalCap_mem_closure_strict_of_interior
    (hRank : 1 < Module.rank ℝ E)
    (x : ClosedUnitBall E) (hxInterior : ‖(x : E)‖ < 1)
    (y : UnitSphere E) (hy : y ∈ sphericalCap x) :
    y ∈ closure (strictSphericalCap x) := by
  let ρ : ℝ := ‖(x : E)‖
  have hρle : ρ ≤ 1 := x.property
  have hρnonneg : 0 ≤ ρ := norm_nonneg _
  by_cases hStrict : dist (x : E) (y : E) < 2 * (1 - ρ)
  · exact subset_closure hStrict
  have hBoundary : dist (x : E) (y : E) = 2 * (1 - ρ) :=
    le_antisymm hy (le_of_not_gt hStrict)
  have hρthird : 1 ≤ 3 * ρ := by
    by_contra h
    have hdist : dist (x : E) (y : E) ≤ ρ + 1 := by
      calc
        dist (x : E) (y : E) ≤ dist (x : E) 0 + dist 0 (y : E) :=
          dist_triangle _ _ _
        _ = ρ + 1 := by simp [ρ, y.property]
    rw [hBoundary] at hdist
    linarith
  have hρpos : 0 < ρ := by linarith
  have hxne : (x : E) ≠ 0 := by
    intro h
    simp [ρ, h] at hρpos
  let hUnit : Nonempty (UnitSphere E) := ⟨y⟩
  let u : UnitSphere E := radialCapPoint hUnit x
  have hScale : (x : E) = ρ • (u : E) :=
    radialCapPoint_scale hUnit x hxne
  by_cases hLarge : 1 < 3 * ρ
  · have hAngle := capBoundary_inner_bounds u y hρpos hLarge hxInterior
      (by simpa only [← hScale] using hBoundary)
    have hClosure := unitSphere_mem_closure_dist_lt_of_nondegenerate
      u y hρpos hAngle.1 hAngle.2
    have hSets : {z : UnitSphere E |
        dist (ρ • (u : E)) (z : E) < dist (ρ • (u : E)) (y : E)} =
        strictSphericalCap x := by
      ext z
      change (dist (ρ • (u : E)) (z : E) <
        dist (ρ • (u : E)) (y : E)) ↔
        dist (x : E) (z : E) < 2 * (1 - ‖(x : E)‖)
      have hzDist : dist (ρ • (u : E)) (z : E) =
          dist (x : E) (z : E) := congrArg (fun c : E => dist c (z : E)) hScale.symm
      have hyDist : dist (ρ • (u : E)) (y : E) =
          2 * (1 - ‖(x : E)‖) := by
        calc
          dist (ρ • (u : E)) (y : E) = dist (x : E) (y : E) :=
            congrArg (fun c : E => dist c (y : E)) hScale.symm
          _ = 2 * (1 - ‖(x : E)‖) := hBoundary
      rw [hzDist, hyDist]
    rwa [hSets] at hClosure
  · have hTransition : 3 * ρ = 1 := by linarith
    have hRmax : 2 * (1 - ρ) = 1 + ρ := by linarith
    have hMax : dist (ρ • (u : E)) (y : E) = 1 + ρ := by
      rw [← hScale, hBoundary, hRmax]
    have hyNeg : (y : E) = -(u : E) :=
      (dist_radial_unit_eq_max_iff (u : E) (y : E)
        u.property y.property hρpos).mp hMax
    have hSub : ({y}ᶜ : Set (UnitSphere E)) ⊆ strictSphericalCap x := by
      intro z hz
      have hzNe : z ≠ y := by simpa using hz
      have hdLe : dist (x : E) (z : E) ≤ 1 + ρ := by
        calc
          dist (x : E) (z : E) ≤ dist (x : E) 0 + dist 0 (z : E) :=
            dist_triangle _ _ _
          _ = ρ + 1 := by simp [ρ, z.property]
          _ = 1 + ρ := by ring
      change dist (x : E) (z : E) < 2 * (1 - ρ)
      by_contra hnot
      have hdEq : dist (ρ • (u : E)) (z : E) = 1 + ρ := by
        rw [← hScale]
        linarith
      have hzNeg : (z : E) = -(u : E) :=
        (dist_radial_unit_eq_max_iff (u : E) (z : E)
          u.property z.property hρpos).mp hdEq
      exact hzNe (Subtype.ext (hzNeg.trans hyNeg.symm))
    have hDense := unitSphere_dense_compl_singleton hRank y
    exact closure_mono hSub (by simpa [hDense.closure_eq] :
      y ∈ closure ({y}ᶜ : Set (UnitSphere E)))

end FairDivision.Topology
