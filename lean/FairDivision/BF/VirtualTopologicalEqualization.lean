import FairDivision.BF.VirtualScoreBridge
import FairDivision.Topology.RegularTranslation
import FairDivision.Topology.Volovikov.ZeroReduction

/-!
# BF Section 5: prime-power equalization of virtual-value scores

The manuscript applies the prime-power no-sphere-map obstruction to its
continuous, position-equivariant preference-score vector. This module
centers that vector and uses the generic zero reduction. The no-map theorem
is an explicit premise until the Volovikov and auxiliary-connectivity
branches discharge it.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

open FairDivision.Topology
open FairDivision.Topology.Volovikov

/-- The prime-power obstruction equalizes the preference scores formed from
any virtual-valuation specification at every positive tolerance. -/
theorem exists_equalized_virtualPreferenceScore_of_noSphereMap
    (p rank N q : ℕ) [NeZero p]
    (D : Finset (Fin N))
    (v : Fin (p ^ rank) → Finset (Fin (N - D.card)) → ℝ)
    (spec : VirtualValuationSpec (q := q) v)
    (ε : ℝ) (hε : 0 < ε)
    (hnoSphereMap :
      ∀ F : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D →
          ReducedSphere (p ^ rank),
        Continuous F →
        (∀ (g : Fin rank → ZMod p)
          (x : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D),
          F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
            relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) → False) :
    ∃ x : unlabeledLotterySpace (p ^ rank) N (q - 1) 1 D,
      ∀ s t : Fin (p ^ rank),
        positionScore (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank)
          (fun i z => spec.score z i) ε
          (fun a => unlabeledReducedMarginal a x) s =
        positionScore (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank)
          (fun i z => spec.score z i) ε
          (fun a => unlabeledReducedMarginal a x) t := by
  let n : ℕ := p ^ rank
  have hn : 0 < n := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
  let act : (Fin rank → ZMod p) →
      unlabeledLotterySpace n N (q - 1) 1 D →
      unlabeledLotterySpace n N (q - 1) 1 D :=
    fun g x => auxiliaryRelabel (pTorusPositionPerm p rank g) x
  let perm : (Fin rank → ZMod p) → Equiv.Perm (Fin n) :=
    pTorusPositionPerm p rank
  let value : Fin n →
      stdSimplex ℝ (FixedFinMarginalBundle (N - D.card) (q - 1)) → ℝ :=
    fun i z => spec.score z i
  let bundle : unlabeledLotterySpace n N (q - 1) 1 D →
      Fin n → stdSimplex ℝ (FixedFinMarginalBundle (N - D.card) (q - 1)) :=
    fun x s => unlabeledReducedMarginal s x
  let score : unlabeledLotterySpace n N (q - 1) 1 D → Fin n → ℝ :=
    fun x s => positionScore hn value ε (bundle x) s - 1
  have hval : ∀ i s : Fin n,
      Continuous (fun x => value i (bundle x s)) := by
    intro i s
    exact (continuous_apply i).comp
      (spec.continuous_score.comp
        (unlabeledReducedMarginal_continuous s))
  have hcont : Continuous score := by
    apply continuous_pi
    intro s
    exact ((continuous_apply s).comp
      (positionScore_continuous hn value ε hε bundle hval)).sub
      continuous_const
  have hcenter (x : unlabeledLotterySpace n N (q - 1) 1 D) :
      (∑ s : Fin n, score x s) = 0 := by
    simp only [score, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [positionScore_total hn value ε hε (bundle x)]
    ring
  have hequiv (g : Fin rank → ZMod p)
      (x : unlabeledLotterySpace n N (q - 1) 1 D)
      (s : Fin n) :
      score (act g x) (perm g s) = score x s := by
    let σ := perm g
    have hBundle : bundle (act g x) =
        fun a => bundle x (σ.symm a) := by
      funext a
      have h := unlabeledReducedMarginal_relabel σ x (σ.symm a)
      simpa only [Equiv.apply_symm_apply] using h
    change positionScore hn value ε (bundle (act g x)) (σ s) - 1 =
      positionScore hn value ε (bundle x) s - 1
    rw [hBundle]
    simpa only [Equiv.symm_apply_apply] using
      congrArg (fun z : ℝ => z - 1)
        (positionScore_permute hn value ε (bundle x) σ.symm (σ s))
  obtain ⟨x, hx⟩ := zero_of_reducedSphere_obstruction
    act perm score hcont hcenter hequiv hnoSphereMap
  refine ⟨x, ?_⟩
  intro s t
  have hs := congrFun hx s
  have ht := congrFun hx t
  change positionScore hn value ε (bundle x) s - 1 = 0 at hs
  change positionScore hn value ε (bundle x) t - 1 = 0 at ht
  dsimp only [value, bundle, n] at hs ht ⊢
  linarith

end FairDivision.BF
