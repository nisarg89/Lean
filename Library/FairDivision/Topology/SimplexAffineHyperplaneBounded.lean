import FairDivision.Topology.SimplexAffineHyperplane

/-!
# Boundedness of the centered simplex

The shifted coordinates are nonnegative and sum to one. Each shifted
coordinate is therefore at most one, giving a uniform norm bound on the
sum-zero affine model of the simplex.
-/

set_option autoImplicit false

namespace FairDivision.Topology

open scoped BigOperators

/-- The centered simplex is bounded in its sum-zero normed space. -/
theorem centeredSimplex_isBounded
    (V : Type*) [Fintype V] [Nonempty V] :
    Bornology.IsBounded (centeredSimplex V) := by
  let b : ℝ := simplexBarycentricCoordinate V
  have hb : 0 < b := simplexBarycentricCoordinate_pos V
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hbSum : ∑ _v : V, b = 1 := by
    simp [b, simplexBarycentricCoordinate, hcard]
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1 + b, ?_⟩
  intro z hz
  have hzSum : ∑ v : V, z.1 v = 0 := z.property
  have hwSum : ∑ v : V, (z.1 v + b) = 1 := by
    rw [Finset.sum_add_distrib, hzSum, hbSum]
    simp
  have hUpper (i : V) : z.1 i + b ≤ 1 := by
    calc
      z.1 i + b ≤ ∑ v : V, (z.1 v + b) := by
        apply Finset.single_le_sum
          (f := fun j : V => z.1 j + b)
        · intro j _
          have hzj : -b ≤ z.1 j := hz j
          linarith
        · exact Finset.mem_univ i
      _ = 1 := hwSum
  have hCoord : ∀ i : V, ‖z.1 i‖ ≤ 1 + b := by
    intro i
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hz i]
    · linarith [hUpper i]
  have hPi : ‖(z.1 : V → ℝ)‖ ≤ 1 + b :=
    (pi_norm_le_iff_of_nonneg (by linarith [hb])).mpr hCoord
  simpa using hPi

end FairDivision.Topology
