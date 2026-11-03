import FairDivision.BF.VirtualValuationConstruction
import FairDivision.BF.VirtualExistenceFromObstruction
import FairDivision.BF.PaddingArithmetic
import FairDivision.Finite.AllocationCast
import FairDivision.Finite.SmallInstances

/-!
# Full-item heterogeneous BF existence with only the external obstruction open

The actual manuscript virtual valuation is now constructed, not assumed.
The existing compactness, owner-witness and real-item completion theorem
performs the allocation argument. This file supplies the same standard
small/large item split, minimal dummy padding and literal item-type cast
already used by the identical-valuation endpoint.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision FairDivision.Finite
open FairDivision.Topology FairDivision.Topology.Volovikov

/-- The trivial one-agent branch for arbitrary bundle valuations. -/
theorem heterogeneous_one_exists_balanced_ef11 (m:ℕ)
    (v:Fin 1→Finset (Fin m)→ℝ):
    ∃A:Allocation 1 m,IsBalanced A ∧IsEF11 v A:=by
  let A:Allocation 1 m:=fun _=>0
  refine ⟨A,isBalanced_one m A,?_⟩
  intro i j
  have hij:i=j:=Subsingleton.elim i j
  subst j
  exact ⟨∅,∅,canDeleteOne_empty _,canDeleteOne_empty _,by simp⟩

/-- All finite construction steps of the heterogeneous manuscript endpoint,
with only the genuine prime-power topological obstruction supplied as a
premise, restricted to the actual bounded dummy stocks. -/
theorem heterogeneousPrimePowerAllM_of_boundedDummy_noSphereMap
    (p rank m:ℕ) [NeZero p]
    (v:Fin (p^rank)→Finset (Fin m)→ℝ)
    (hno:p^rank< m→
      ∀D:Finset (Fin ((p^rank)*upperSize (p^rank) m)),D.card≤p^rank→
      ∀F:unlabeledLotterySpace (p^rank) ((p^rank)*upperSize (p^rank) m)
          (upperSize (p^rank) m-1) 1 D→ReducedSphere (p^rank),
        Continuous F→
        (∀(g:Fin rank→ZMod p)
          (x:unlabeledLotterySpace (p^rank) ((p^rank)*upperSize (p^rank) m)
            (upperSize (p^rank) m-1) 1 D),
          F (auxiliaryRelabel (pTorusPositionPerm p rank g) x)=
            relabelReducedSphere (pTorusPositionPerm p rank g) (F x))→False):
    ∃A:Allocation (p^rank) m,IsBalanced A ∧IsEF11 v A:=by
  have hn:0<p^rank:=pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) rank
  by_cases hm:m≤p^rank
  ·exact heterogeneous_small hn hm v
  ·have hBig:p^rank< m:=by omega
   let n:ℕ:=p^rank
   let q:ℕ:=upperSize n m
   have hPad:=upperSize_padding n m hn
   have hEnough:m≤n*q:=hPad.1
   have hDummyLt:n*q-m<n:=hPad.2
   have hq:2≤q:=upperSize_two_le_of_lt n m hn hBig
   have hDCount:n*q-m≤(Finset.univ:Finset (Fin (n*q))).card:=by
     simp only [Finset.card_univ,Fintype.card_fin]
     omega
   obtain ⟨D,hDUniv,hDCard⟩:=Finset.exists_subset_card_eq hDCount
   have hDlt:D.card<n:=by rw [hDCard];exact hDummyLt
   have hRealCount:n*q-D.card=m:=by
     rw [hDCard]
     exact Nat.sub_sub_self hEnough
   let realValues:Fin n→Finset (Fin (n*q-D.card))→ℝ:=
     fun i=>castValuation hRealCount (v i)
   let spec:VirtualValuationSpec (q:=q) realValues:=virtualValuationSpec realValues (by omega)
   obtain ⟨A,hBalanced,hFair⟩:=exists_balanced_ef11_of_virtualSpec_and_noSphereMap
     p rank (n*q) q D realValues spec hq rfl hDlt (hno hBig D hDlt.le)
   exact ⟨castAllocation hRealCount A,castAllocation_balanced hRealCount A hBalanced,
     castAllocation_ef11 hRealCount v A hFair⟩

end FairDivision.BF
