import FairDivision.BF.HeterogeneousExistenceFromObstruction
import FairDivision.BF.PrimePowerTopologicalEqualization

/-!
# BF heterogeneous existence at every prime-power agent count

The manuscript virtual valuation, finite-skeleton extension, compact
owner witness, real-item completion and balanced dummy removal are
already constructed. This file supplies only the now-proved external
prime-power obstruction to that existing argument. The one-agent branch
uses the existing finite result. No alternate allocation proof is added.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision FairDivision.Topology FairDivision.Topology.Volovikov

/-- Arbitrary heterogeneous bundle valuations admit a balanced EF[1,1]
allocation for every prime-power number of agents and every item count. -/
theorem heterogeneous_primePower_exists_balanced_ef11
    (p rank m : ℕ) [Fact p.Prime]
    (v : Fin (p^rank)→Finset (Fin m)→ℝ) :
    ∃A : Allocation (p^rank) m,IsBalanced A ∧IsEF11 v A := by
  by_cases hRank : rank=0
  · subst rank
    change ∃A : Allocation 1 m,IsBalanced A ∧IsEF11 v A
    exact heterogeneous_one_exists_balanced_ef11 m v
  · have hPositive : 0<rank:=Nat.pos_of_ne_zero hRank
    apply heterogeneousPrimePowerAllM_of_boundedDummy_noSphereMap p rank m v
    intro hBig D hD F hContinuous hEquivariant
    have hn : 0<p^rank:=pow_pos (Fact.out : p.Prime).pos rank
    have hq : 2≤upperSize (p^rank) m:=upperSize_two_le_of_lt (p^rank) m hn hBig
    exact no_reducedSphere_auxiliary_primePower p rank (upperSize (p^rank) m)
      hPositive hq D hD F hContinuous hEquivariant

end FairDivision.BF
