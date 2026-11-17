import FairDivision.Topology.Volovikov.UniversalJoinDoublingWeights

/-!
# Injectivity of the doubled universal-join map

The two block masses recover the join parameter. Away from the collapsed
endpoint, the exact coordinate formulas recover the corresponding factor.
-/

set_option autoImplicit false

open scoped unitInterval Topology Classical

namespace FairDivision.Topology.Volovikov

open FairDivision.Topology.NerveConnectivity

/-- The continuous map from the topological join of two finite universal joins
to their doubled finite join is injective. -/
theorem doubledJoinMap_injective
    (m : ℕ) (G : Type*) [Fintype G] :
    Function.Injective (doubledJoinMap m G) := by
  intro z w h
  induction z using Quotient.inductionOn with
  | _ z =>
    induction w using Quotient.inductionOn with
    | _ w =>
      rcases z with ⟨t, x, y⟩
      rcases w with ⟨s, x', y'⟩
      change doubledJoinCylinderPoint m G (t, (x, y)) =
        doubledJoinCylinderPoint m G (s, (x', y')) at h
      have hsimplex :
          doubledJoinCylinderSimplex m G (t, (x, y)) =
            doubledJoinCylinderSimplex m G (s, (x', y')) :=
        congrArg Subtype.val h
      have htimeVal : (t : ℝ) = (s : ℝ) := by
        have hm := congrArg rightDoubledJoinMass hsimplex
        simpa only [rightDoubledJoinMass_cylinder] using hm
      have htime : t = s := Subtype.ext htimeVal
      subst s
      have hx (ht : t ≠ 1) : x = x' := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        have hv := congrArg
          (fun q : stdSimplex ℝ (Fin (m + m) × G) =>
            q.1 (leftDoubledJoinVertex v)) hsimplex
        simp only [doubledJoinCylinderSimplex_apply_left] at hv
        have hc : 1 - (t : ℝ) ≠ 0 := by
          intro h0
          apply ht
          apply Subtype.ext
          have htval : (t : ℝ) = 1 := by linarith
          simpa using htval
        exact mul_left_cancel₀ hc hv
      have hy (ht : t ≠ 0) : y = y' := by
        apply Subtype.ext
        apply Subtype.ext
        funext v
        have hv := congrArg
          (fun q : stdSimplex ℝ (Fin (m + m) × G) =>
            q.1 (rightDoubledJoinVertex v)) hsimplex
        simp only [doubledJoinCylinderSimplex_apply_right] at hv
        have hc : (t : ℝ) ≠ 0 := by
          intro h0
          apply ht
          exact Subtype.ext h0
        exact mul_left_cancel₀ hc hv
      apply Quotient.sound
      change topologicalJoinKey (t, (x, y)) =
        topologicalJoinKey (t, (x', y'))
      by_cases h1 : t = 1
      · have h0 : t ≠ 0 := by
          intro hzero
          exact zero_ne_one (hzero.symm.trans h1)
        simp [topologicalJoinKey, h1, h0, hy h0]
      · by_cases h0 : t = 0
        · simp [topologicalJoinKey, h1, h0, hx h1]
        · simp [topologicalJoinKey, h1, h0, hx h1, hy h0]

end FairDivision.Topology.Volovikov
