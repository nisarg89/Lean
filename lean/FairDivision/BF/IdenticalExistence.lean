import FairDivision.BF.Recording.RootPoolRealization
import FairDivision.BF.Recording.RootZero
import FairDivision.BF.Recording.ActualDummyRemoval
import FairDivision.Finite.EquitableCompletionBridge
import FairDivision.Finite.SmallInstances
import FairDivision.BF.PaddingArithmetic

/-!
# BF Section 4: identical valuations for every positive agent count

This follows the manuscript's single proof. Construct the recorder along
prime factors; take the midpoint with the full real-and-dummy pool; find
one threshold zero; relabel actual dummy reserves; apply the integral
lottery conversion once; delete dummies. Small item counts and the
one-agent case are treated exactly as in the paper.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF

open FairDivision FairDivision.Topology FairDivision.Finite Recording

/-- The exact augmented conclusion used in the applications appendix:
before any dummy deletion, every q-item bundle brackets the SAME t after
EXACTLY one deletion and contains at most one actual dummy item. -/
theorem identical_exists_augmented_commonThreshold
    (n m q d:ℕ) (hn:0<n) (hq:2≤q) (hm:2≤ m)
    (hd:d<n) (hPad:m+d=n*q) (v:Finset (Fin m)→ℝ):
    ∃(A:Allocation n (m+d))(t:ℝ),∀i:Fin n,
      (bundle A i).card=q ∧
      BracketsOneDeletion (fun B=>v (realPart B)) (bundle A i) t ∧
      (bundle A i∩dummyLabels m d).card≤1:=by
  let x:Fin m:=⟨0,by omega⟩
  let y:Fin m:=⟨1,by omega⟩
  have hxy:x≠y:=by intro he;have hv:=congrArg Fin.val he;norm_num [x,y] at hv
  let b:=rootMidpoint hd hPad x y hxy
  obtain ⟨t,ht⟩:=exists_certifies_at n q m hn hq v b
  obtain ⟨hFullPool,μ,hμ,hMean⟩:=rootMidpoint_certifies_actual_spec hd hPad (by omega) x y hxy ht
  have hq':q-1+1=q:=Nat.sub_add_cancel (by omega)
  have hSize:m+d=n*(q-1+1):=by simpa only [hq'] using hPad
  have hD:(dummyLabels m d).card≤n:=by rw [card_dummyLabels];omega
  obtain ⟨A,hA⟩:=allocation_of_equitableLottery hSize hD μ hμ
    (fun B=>v (realPart B)) t (by
      intro i
      simpa only [realPart_sdiff_dummy] using hMean i)
  exact ⟨A,t,by simpa only [hq',realPart_sdiff_dummy] using hA⟩

/-- Theorem `identical-all-n`, retaining the manuscript's stronger common
threshold conclusion, for arbitrary real-valued set valuations. -/
theorem identical_exists_balanced_commonThreshold
    (n m:ℕ) (hn:0<n) (v:Finset (Fin m)→ℝ):
    ∃(A:Allocation n m)(t:ℝ),IsBalanced A ∧ HasCommonThreshold v A t:=by
  by_cases hOne:n=1
  · subst n
    exact identical_one m v
  by_cases hSmall:m≤n
  · exact identical_small hn hSmall v
  have hBig:n< m:=by omega
  let q:=upperSize n m
  let d:=n*q-m
  have hEnough:m≤n*q:=(upperSize_padding n m hn).1
  have hd:d<n:=(upperSize_padding n m hn).2
  have hPad:m+d=n*q:=Nat.add_sub_of_le hEnough
  have hq:2≤q:=upperSize_two_le_of_lt n m hn hBig
  obtain ⟨A,t,hA⟩:=identical_exists_augmented_commonThreshold n m q d hn hq
    (by omega) hd hPad v
  obtain ⟨R,hBalanced,hThreshold⟩:=actualDummyRemoval hPad hn (by omega) hd A v t hA
  exact ⟨R,t,hBalanced,hThreshold⟩

/-- The balanced EF[1,1] consequence for every positive agent count. -/
theorem identical_exists_balanced_ef11
    (n m:ℕ) (hn:0<n) (v:Finset (Fin m)→ℝ):
    ∃A:Allocation n m,IsBalanced A ∧ IsEF11 (fun _=>v) A:=by
  obtain ⟨A,t,hBalanced,hThreshold⟩:=identical_exists_balanced_commonThreshold n m hn v
  exact ⟨A,hBalanced,hasCommonThreshold_implies_ef11 v A t hThreshold⟩

end FairDivision.BF
