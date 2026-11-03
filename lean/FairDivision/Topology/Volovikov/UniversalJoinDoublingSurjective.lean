import FairDivision.Topology.Volovikov.UniversalJoinDoublingInjective
import FairDivision.Topology.Volovikov.UniversalJoinDoublingRestriction
import FairDivision.Topology.Volovikov.UniversalJoinDoublingZeroMass

/-!
# Surjectivity of the doubled universal-join map

Split a doubled probability vector by its two color-block masses. Positive
blocks are normalized into the corresponding smaller join; a zero-mass block
uses an arbitrary source point because its factor is collapsed at the join
endpoint.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- Every point of the doubled finite universal join is a weighted join of
two points from the smaller universal join. -/
theorem doubledJoinCylinderPoint_surjective
    (m : ℕ) (G : Type*) [Fintype G]
    (w : simplicialRealization (universalJoinComplex (m + m) G)) :
    ∃ z : I ×
      (simplicialRealization (universalJoinComplex m G) ×
        simplicialRealization (universalJoinComplex m G)),
      doubledJoinCylinderPoint m G z = w := by
  let L := leftDoubledJoinMass w.1
  let R := rightDoubledJoinMass w.1
  let t := rightDoubledJoinTime w.1
  let base := doubledJoinBasepoint w
  let x : simplicialRealization (universalJoinComplex m G) :=
    if hL : 0 < L then leftDoubledJoinRealization w hL else base
  let y : simplicialRealization (universalJoinComplex m G) :=
    if hR : 0 < R then rightDoubledJoinRealization w hR else base
  have hLcoeff : 1 - (t : ℝ) = L := by
    change 1 - rightDoubledJoinMass w.1 = leftDoubledJoinMass w.1
    linarith [leftDoubledJoinMass_add_right w.1]
  have hRcoeff : (t : ℝ) = R := rfl
  have hleft (v : Fin m × G) :
      (doubledJoinCylinderSimplex m G (t, (x, y))).1
          (leftDoubledJoinVertex v) =
        w.1.1 (leftDoubledJoinVertex v) := by
    rw [doubledJoinCylinderSimplex_apply_left, hLcoeff]
    by_cases hL : 0 < L
    · have hx : x.1.1 v = w.1.1 (leftDoubledJoinVertex v) / L := by
        simp [x, hL, leftDoubledJoinRealization,
          leftDoubledJoinRestrict, L]
      rw [hx]
      exact mul_div_cancel₀ _ (ne_of_gt hL)
    · have hLzero : L = 0 :=
        le_antisymm (le_of_not_gt hL) (leftDoubledJoinMass_nonneg w.1)
      rw [hLzero, zero_mul]
      exact (leftDoubledJoinCoord_zero_of_mass_zero w.1 hLzero v).symm
  have hright (v : Fin m × G) :
      (doubledJoinCylinderSimplex m G (t, (x, y))).1
          (rightDoubledJoinVertex v) =
        w.1.1 (rightDoubledJoinVertex v) := by
    rw [doubledJoinCylinderSimplex_apply_right, hRcoeff]
    by_cases hR : 0 < R
    · have hy : y.1.1 v = w.1.1 (rightDoubledJoinVertex v) / R := by
        simp [y, hR, rightDoubledJoinRealization,
          rightDoubledJoinRestrict, R]
      rw [hy]
      exact mul_div_cancel₀ _ (ne_of_gt hR)
    · have hRzero : R = 0 :=
        le_antisymm (le_of_not_gt hR) (rightDoubledJoinMass_nonneg w.1)
      rw [hRzero, zero_mul]
      exact (rightDoubledJoinCoord_zero_of_mass_zero w.1 hRzero v).symm
  refine ⟨(t, (x, y)), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (doubledJoinCylinderSimplex m G (t, (x, y))).1 = w.1.1
  funext v
  rcases v with ⟨i, g⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [leftDoubledJoinVertex] using hleft (j, g)
  · simpa [rightDoubledJoinVertex] using hright (j, g)

/-- The map from the topological join onto the doubled finite universal join
is surjective. -/
theorem doubledJoinMap_surjective
    (m : ℕ) (G : Type*) [Fintype G] :
    Function.Surjective (doubledJoinMap m G) := by
  intro w
  obtain ⟨z, hz⟩ := doubledJoinCylinderPoint_surjective m G w
  exact ⟨topologicalJoinProjection _ _ z, hz⟩

end FairDivision.Topology.Volovikov
