import FairDivision.Topology.Volovikov.PrimePowerConnectedObstruction
import FairDivision.Topology.UnlabeledActionHomeomorph
import FairDivision.Topology.VariableDummyUniformConnectivityFinal
import FairDivision.BF.EqualizingScores

/-!
# BF's actual auxiliary obstruction for every positive prime-power rank

Use the corrected unlabeled-dummy source, its already-proved connectivity,
and its exact continuous p-torus action. Only the external no-map result
is new here. All equal-score and compatible-lottery conversion proofs
are reused from the manuscript formalization.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology FairDivision.Topology.Volovikov
open FairDivision.Topology.NerveConnectivity

/-- The complete sphere obstruction on the actual bounded-dummy stock
used by both identical and heterogeneous BF existence arguments. -/
theorem no_reducedSphere_auxiliary_primePower
    (p rank q : ℕ) [Fact p.Prime] (hRank : 0<rank) (hq : 2≤q)
    (D : Finset (Fin (p^rank*q))) (hD : D.card≤p^rank)
    (F : unlabeledLotterySpace (p^rank) (p^rank*q) (q-1) 1 D→ReducedSphere (p^rank))
    (hContinuous : Continuous F)
    (hEquivariant : ∀(g : Fin rank→ZMod p)
      (x : unlabeledLotterySpace (p^rank) (p^rank*q) (q-1) 1 D),
      F (auxiliaryRelabel (pTorusPositionPerm p rank g) x)=
        relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) : False := by
  have hn : 0<p^rank:=pow_pos (Fact.out : p.Prime).pos rank
  have hConnected : NullConnectedSpace (p^rank-1)
      (unlabeledLotterySpace (p^rank) (p^rank*q) (q-1) 1 D) := by
    have h:=unlabeledLotterySpace_nullConnected
      (p^rank) q 1 D hn (by decide) hq (one_dvd _) hD
    unfold NullConnectedSet at h
    have transport (n s : ℕ) (hn : n=p^rank) (hs : s=q-1)
        (hc : NullConnectedSpace (n-1)
          (unlabeledLotterySpace n (p^rank*q) s 1 D)) :
        NullConnectedSpace (p^rank-1)
          (unlabeledLotterySpace (p^rank) (p^rank*q) (q-1) 1 D) := by
      subst n
      subst s
      exact hc
    exact transport (p^rank/1) (1*q-1) (Nat.div_one _) (by rw [one_mul]) h
  exact no_reducedSphere_map_primePower hRank (by omega) hConnected
    (pTorusAuxiliaryAction p rank (p^rank*q) (q-1) 1 D)
    (pTorusAuxiliaryAction_action p rank (p^rank*q) (q-1) 1 D)
    F hContinuous hEquivariant

/-- Original auxiliary expected scores equalize; no no-map premise is left. -/
theorem exists_equalizedAuxiliaryScore_primePower
    (p rank q : ℕ) [Fact p.Prime] (hRank : 0<rank) (hq : 2≤q)
    (D : Finset (Fin (p^rank*q))) (hD : D.card≤p^rank)
    (v : Finset (Fin (p^rank*q))→ℝ) :
    ∃x : unlabeledLotterySpace (p^rank) (p^rank*q) (q-1) 1 D,
      ∀i : Fin (p^rank),unlabeledExpectedValue v x.1 i=auxiliaryAverageScore v x.1 := by
  apply exists_equalizedAuxiliaryScore_of_noSphereMap p rank (p^rank*q) (q-1) 1 D v
  intro F hContinuous hEquivariant
  exact no_reducedSphere_auxiliary_primePower p rank q hRank hq D hD
    F hContinuous hEquivariant

/-- Existing compatible-lottery lift on the actual unlabeled-dummy source. -/
theorem exists_equitable_compatibleLottery_primePower
    (p rank q : ℕ) [Fact p.Prime] (hRank : 0<rank) (hq : 2≤q)
    (D : Finset (Fin (p^rank*q))) (hD : D.card≤p^rank)
    (v : Finset (Fin (p^rank*q))→ℝ) :
    ∃μ : stdSimplex ℝ (PartialVertex (p^rank) D (q-1) 1),
      μ∈compatibleLotterySpace (p^rank) (p^rank*q) (q-1) 1 D ∧
      ∃t : ℝ,∀i : Fin (p^rank),
        (∑X : PartialVertex (p^rank) D (q-1) 1,
          μ.1 X*v (partialBundle X.1 i\D))=t := by
  obtain ⟨x,hx⟩:=exists_equalizedAuxiliaryScore_primePower p rank q hRank hq D hD v
  exact compatibleLottery_of_equalized_auxiliary D v x hx

end FairDivision.BF
