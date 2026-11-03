import FairDivision.Topology.CenteredScores
import FairDivision.Topology.Volovikov.ZeroReduction
import FairDivision.Topology.UnlabeledLotteryLift

/-!
# BF expected-score equalization from the prime-power obstruction

The topological obstruction is a separate external dependency. This module
applies its generic zero reduction to the corrected unlabeled-dummy complex,
using the manuscript's position scores and regular p-torus action.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Topology.Volovikov

/-- A prime-power no-equivariant-sphere-map theorem gives a point of the
corrected auxiliary complex at which all expected position scores agree. -/
theorem exists_equalizedAuxiliaryScore_of_noSphereMap
    (p rank m r c : ℕ) [NeZero p]
    (D : Finset (Fin m)) (v : Finset (Fin m) → ℝ)
    (hnoSphereMap :
      ∀ F : unlabeledLotterySpace (p ^ rank) m r c D →
          ReducedSphere (p ^ rank),
        Continuous F →
        (∀ (g : Fin rank → ZMod p)
          (x : unlabeledLotterySpace (p ^ rank) m r c D),
          F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
            relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) → False) :
    ∃ x : unlabeledLotterySpace (p ^ rank) m r c D,
      ∀ i : Fin (p ^ rank),
        unlabeledExpectedValue v x.1 i = auxiliaryAverageScore v x.1 := by
  let act : (Fin rank → ZMod p) →
      unlabeledLotterySpace (p ^ rank) m r c D →
      unlabeledLotterySpace (p ^ rank) m r c D :=
    fun g x => auxiliaryRelabel (pTorusPositionPerm p rank g) x
  let perm : (Fin rank → ZMod p) → Equiv.Perm (Fin (p ^ rank)) :=
    pTorusPositionPerm p rank
  let score : unlabeledLotterySpace (p ^ rank) m r c D →
      Fin (p ^ rank) → ℝ :=
    fun x i => auxiliaryCenteredScore v x.1 i
  have hContinuous : Continuous score := by
    apply continuous_pi
    intro i
    exact (auxiliaryCenteredScore_continuous v i).comp
      continuous_subtype_val
  have hPositions : 0 < p ^ rank :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
  have hCenter (x : unlabeledLotterySpace (p ^ rank) m r c D) :
      (∑ i : Fin (p ^ rank), score x i) = 0 :=
    auxiliaryCenteredScore_sum_zero hPositions v x.1
  have hEquiv (g : Fin rank → ZMod p)
      (x : unlabeledLotterySpace (p ^ rank) m r c D)
      (i : Fin (p ^ rank)) :
      score (act g x) (perm g i) = score x i :=
    auxiliaryCenteredScore_relabel (pTorusPositionPerm p rank g) v x.1 i
  obtain ⟨x, hx⟩ := zero_of_reducedSphere_obstruction
    act perm score hContinuous hCenter hEquiv hnoSphereMap
  refine ⟨x, ?_⟩
  apply (auxiliaryCenteredScore_zero_iff v x.1).mp
  intro i
  exact congrFun hx i

/-- The manuscript's representative choice turns an equalized auxiliary
point into an equitable compatible lottery on labeled partial allocations. -/
theorem compatibleLottery_of_equalized_auxiliary
    {k m r c : ℕ} (D : Finset (Fin m))
    (v : Finset (Fin m) → ℝ)
    (x : unlabeledLotterySpace k m r c D)
    (hx : ∀ i : Fin k,
      unlabeledExpectedValue v x.1 i = auxiliaryAverageScore v x.1) :
    ∃ μ : stdSimplex ℝ (PartialVertex k D r c),
      μ ∈ compatibleLotterySpace k m r c D ∧
      ∃ t : ℝ, ∀ i : Fin k,
        (∑ X : PartialVertex k D r c,
          μ.1 X * v (partialBundle X.1 i \ D)) = t := by
  obtain ⟨μ, hμ, hScores⟩ := exists_compatible_lift x.1 x.2
  refine ⟨μ, hμ, auxiliaryAverageScore v x.1, ?_⟩
  intro i
  rw [hScores v i, hx i]

end FairDivision.BF
