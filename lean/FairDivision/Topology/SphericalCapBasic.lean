import Mathlib

/-!
# Spherical caps for the coordinatewise-maximum ball extension

The cap at an interior ball point `x` is measured in ambient chordal distance.
It is the whole sphere on a neighborhood of the center and becomes a
singleton on the boundary.  This is the radius schedule stated in the current BF manuscript
(Section 5, higher-dimensional faces).
-/

set_option autoImplicit false

namespace FairDivision.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball, regarded as a topological space. -/
abbrev ClosedUnitBall (E : Type*) [NormedAddCommGroup E] :=
  {x : E // ‖x‖ ≤ 1}

/-- The unit sphere, regarded as a topological space. -/
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] :=
  {y : E // ‖y‖ = 1}

/-- A chordal cap centered at the ball point itself. -/
def sphericalCap (x : ClosedUnitBall E) : Set (UnitSphere E) :=
  {y | dist (x : E) (y : E) ≤ 2 * (1 - ‖(x : E)‖)}

theorem sphericalCap_mem_iff (x : ClosedUnitBall E) (y : UnitSphere E) :
    y ∈ sphericalCap x ↔ dist (x : E) (y : E) ≤ 2 * (1 - ‖(x : E)‖) :=
  Iff.rfl

theorem sphericalCap_eq_univ_of_norm_le_third (x : ClosedUnitBall E)
    (hx : 3 * ‖(x : E)‖ ≤ 1) : sphericalCap x = Set.univ := by
  ext y
  simp only [sphericalCap, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have hy : ‖(y : E)‖ = 1 := y.property
  have hdist : dist (x : E) (y : E) ≤ ‖(x : E)‖ + 1 := by
    calc
      dist (x : E) (y : E) ≤ dist (x : E) 0 + dist 0 (y : E) := dist_triangle _ _ _
      _ = ‖(x : E)‖ + 1 := by simp [hy]
  linarith

theorem sphericalCap_eq_singleton_of_boundary (x : ClosedUnitBall E)
    (hx : ‖(x : E)‖ = 1) :
    sphericalCap x = {(⟨(x : E), hx⟩ : UnitSphere E)} := by
  ext y
  simp only [sphericalCap, Set.mem_setOf_eq, Set.mem_singleton_iff]
  have hr : 2 * (1 - ‖(x : E)‖) = 0 := by rw [hx]; ring
  rw [hr]
  constructor
  · intro hy
    have hd : dist (x : E) (y : E) = 0 := le_antisymm hy dist_nonneg
    apply Subtype.ext
    exact (dist_eq_zero.mp hd).symm
  · intro hy
    subst y
    simp

theorem sphericalCap_isClosed (x : ClosedUnitBall E) : IsClosed (sphericalCap x) := by
  unfold sphericalCap
  exact isClosed_le (continuous_const.dist continuous_subtype_val) continuous_const

instance unitSphere_compactSpace [ProperSpace E] : CompactSpace (UnitSphere E) := by
  apply isCompact_iff_compactSpace.mp
  have h : IsCompact {y : E | ‖y‖ = 1} := by
    simpa [Metric.sphere, dist_eq_norm] using isCompact_sphere (0 : E) 1
  exact h

theorem sphericalCap_isCompact [ProperSpace E] (x : ClosedUnitBall E) :
    IsCompact (sphericalCap x) :=
  (sphericalCap_isClosed x).isCompact

theorem sphericalCap_nonempty (hUnit : Nonempty (UnitSphere E))
    (x : ClosedUnitBall E) : (sphericalCap x).Nonempty := by
  let ρ : ℝ := ‖(x : E)‖
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρ1 : ρ ≤ 1 := x.property
  by_cases hsmall : 3 * ρ ≤ 1
  · rcases hUnit with ⟨y⟩
    exact ⟨y, by rw [sphericalCap_eq_univ_of_norm_le_third x hsmall]; trivial⟩
  · have hρpos : 0 < ρ := by linarith
    let yv : E := ρ⁻¹ • (x : E)
    have hy : ‖yv‖ = 1 := by
      simp [yv, ρ, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg (x : E)), hρpos.ne']
    have hxy : (x : E) = ρ • yv := by
      simp [yv, smul_smul, hρpos.ne']
    have hdist : dist (x : E) yv = 1 - ρ := by
      calc
        dist (x : E) yv = ‖(ρ - 1) • yv‖ := by
          rw [hxy, dist_eq_norm]
          congr 1
          simp [sub_smul]
        _ = 1 - ρ := by
          rw [norm_smul, hy, mul_one, Real.norm_eq_abs]
          rw [abs_of_nonpos (sub_nonpos.mpr hρ1)]
          ring
    refine ⟨⟨yv, hy⟩, ?_⟩
    change dist (x : E) yv ≤ 2 * (1 - ‖(x : E)‖)
    rw [hdist]
    dsimp [ρ]
    linarith

end FairDivision.Topology
