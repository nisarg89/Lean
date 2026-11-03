import FairDivision.BF.PrimePowerTopologicalEqualization
import FairDivision.BF.ConditionalPrimePowerExistence

/-!
# BF Section 3: identical valuations at every prime-power agent count

Reuse the original finite argument, including its small-item branch,
minimal dummy padding, common threshold, dummy deletion, and item-type
cast. The external obstruction is discharged for all positive ranks;
rank zero is the already-proved one-agent allocation.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision FairDivision.Finite
open FairDivision.Topology FairDivision.Topology.Volovikov

/-- All prime powers, all item counts, arbitrary common bundle valuation,
and the exact common threshold already produced by the manuscript proof. -/
theorem identical_primePower_exists_balanced_commonThreshold
    (p rank m : ℕ) [Fact p.Prime] (v : Finset (Fin m)→ℝ) :
    ∃(A : Allocation (p^rank) m)(t : ℝ),IsBalanced A ∧HasCommonThreshold v A t := by
  by_cases hRank : rank=0
  · subst rank
    change ∃(A : Allocation 1 m)(t : ℝ),IsBalanced A ∧HasCommonThreshold v A t
    exact identical_one m v
  · have hPositive : 0<rank:=Nat.pos_of_ne_zero hRank
    apply identicalPrimePowerAllM_commonThreshold_of_boundedDummy_noSphereMap p rank m v
    intro hBig D hD F hContinuous hEquivariant
    have hn : 0<p^rank:=pow_pos (Fact.out : p.Prime).pos rank
    have hq : 2≤upperSize (p^rank) m:=upperSize_two_le_of_lt (p^rank) m hn hBig
    exact no_reducedSphere_auxiliary_primePower p rank (upperSize (p^rank) m)
      hPositive hq D hD F hContinuous hEquivariant

/-- Exact balanced EF[1,1] existence at every prime-power agent count. -/
theorem identical_primePower_exists_balanced_ef11
    (p rank m : ℕ) [Fact p.Prime] (v : Finset (Fin m)→ℝ) :
    ∃A : Allocation (p^rank) m,IsBalanced A ∧IsEF11 (fun _=>v) A := by
  obtain ⟨A,t,hBalanced,hThreshold⟩:=
    identical_primePower_exists_balanced_commonThreshold p rank m v
  exact ⟨A,hBalanced,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

end FairDivision.BF
