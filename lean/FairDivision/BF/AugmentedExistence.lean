import FairDivision.BF.EqualizingScores
import FairDivision.Finite.EquitableCompletionBridge

/-!
# Prime-power BF allocation from the topological obstruction

This is the Section 3 dependency boundary: an equivariant no-sphere-map
statement gives an equitable compatible lottery, and the manuscript's
three-phase finite conversion gives a full augmented allocation. The
obstruction is an explicit premise until the Volovikov development proves it.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision.Topology
open FairDivision.Topology.Volovikov

/-- Once the prime-power equivariant no-map theorem is available for the
corrected auxiliary complex, the Section 3 construction yields full
one-dummy-capped augmented bundles bracketing a common value. -/
theorem exists_augmentedAllocation_of_noSphereMap
    (p rank q : ℕ) [NeZero p]
    (D : Finset (Fin ((p ^ rank) * q)))
    (v : Finset (Fin ((p ^ rank) * q)) → ℝ)
    (hq : 2 ≤ q) (hD : D.card ≤ p ^ rank)
    (hnoSphereMap :
      ∀ F : unlabeledLotterySpace (p ^ rank) ((p ^ rank) * q)
            (q - 1) 1 D → ReducedSphere (p ^ rank),
        Continuous F →
        (∀ (g : Fin rank → ZMod p)
          (x : unlabeledLotterySpace (p ^ rank) ((p ^ rank) * q)
            (q - 1) 1 D),
          F (auxiliaryRelabel (pTorusPositionPerm p rank g) x) =
            relabelReducedSphere (pTorusPositionPerm p rank g) (F x)) → False) :
    ∃ (A : FairDivision.Allocation (p ^ rank) ((p ^ rank) * q)) (t : ℝ),
      ∀ i : Fin (p ^ rank),
        (FairDivision.bundle A i).card = q ∧
        FairDivision.BracketsOneDeletion
          (fun F => v (F \ D)) (FairDivision.bundle A i) t ∧
        (FairDivision.bundle A i ∩ D).card ≤ 1 := by
  obtain ⟨x, hx⟩ :=
    exists_equalizedAuxiliaryScore_of_noSphereMap
      p rank ((p ^ rank) * q) (q - 1) 1 D v hnoSphereMap
  obtain ⟨lot, hComp, t, hMean⟩ :=
    compatibleLottery_of_equalized_auxiliary D v x hx
  have hq' : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hm : (p ^ rank) * q = (p ^ rank) * (q - 1 + 1) := by
    rw [hq']
  obtain ⟨A, hA⟩ :=
    FairDivision.Finite.allocation_of_equitableLottery
      hm hD lot hComp v t hMean
  exact ⟨A, t, by simpa only [hq'] using hA⟩

end FairDivision.BF
