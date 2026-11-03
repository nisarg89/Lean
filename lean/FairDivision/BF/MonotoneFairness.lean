import FairDivision.BF.IdenticalExistence
import FairDivision.BF.PrimePowerHeterogeneousExistence

/-!
# Ordinary EF1 for monotone and antitone set valuations

These are the manuscript's restoration corollaries. They apply to arbitrary
set valuations: no additivity, sign normalization or submodularity is used.
The optional single deletion is from the rival bundle for nondecreasing
valuations and from one's own bundle for nonincreasing valuations.
-/

set_option autoImplicit false

namespace FairDivision.BF

open FairDivision

def IsGoodsEF1For {n m:ℕ} (v:Fin n→Finset (Fin m)→ℝ)
    (A:Allocation n m) (i:Fin n):Prop:=
  ∀j:Fin n,∃D:Finset (Fin m),CanDeleteOne D (bundle A j) ∧
    v i (bundle A j\D)≤v i (bundle A i)

def IsChoresEF1For {n m:ℕ} (v:Fin n→Finset (Fin m)→ℝ)
    (A:Allocation n m) (i:Fin n):Prop:=
  ∀j:Fin n,∃D:Finset (Fin m),CanDeleteOne D (bundle A i) ∧
    v i (bundle A j)≤v i (bundle A i\D)

def IsGoodsEF1 {n m:ℕ} (v:Fin n→Finset (Fin m)→ℝ) (A:Allocation n m):Prop:=
  ∀i,IsGoodsEF1For v A i

def IsChoresEF1 {n m:ℕ} (v:Fin n→Finset (Fin m)→ℝ) (A:Allocation n m):Prop:=
  ∀i,IsChoresEF1For v A i

/-- In an originally envying comparison the optional goods deletion is
necessarily an actual item of the rival bundle. Conversely, the no-envy
comparisons use the empty deletion. This is the usual item-witness reading
of EF1, including empty bundles. No monotonicity is needed for this reading. -/
theorem goodsEF1For_iff_actual_item_of_envy {n m : ℕ}
    (v : Fin n→Finset (Fin m)→ℝ) (A : Allocation n m) (i : Fin n) :
    IsGoodsEF1For v A i ↔
      ∀j : Fin n,v i (bundle A i)<v i (bundle A j)→
        ∃g∈bundle A j,v i ((bundle A j).erase g)≤v i (bundle A i) := by
  classical
  constructor
  · intro hFair j hEnvy
    obtain ⟨D,hD,hValue⟩:=hFair j
    have hNonempty : D.Nonempty := by
      by_contra hEmpty
      have hDZero : D=∅:=Finset.not_nonempty_iff_eq_empty.mp hEmpty
      have hNoEnvy : v i (bundle A j)≤v i (bundle A i) := by
        simpa only [hDZero,Finset.sdiff_empty] using hValue
      exact (not_le_of_gt hEnvy) hNoEnvy
    have hCard : D.card=1 := by
      have hPositive:=Finset.card_pos.mpr hNonempty
      have hAtMost : D.card≤1:=hD.2
      omega
    obtain ⟨g,hSingleton⟩:=Finset.card_eq_one.mp hCard
    have hgD : g∈D := by rw [hSingleton]; exact Finset.mem_singleton_self g
    refine ⟨g,hD.1 hgD,?_⟩
    simpa only [hSingleton,Finset.sdiff_singleton_eq_erase] using hValue
  · intro hItems j
    by_cases hEnvy : v i (bundle A i)<v i (bundle A j)
    · obtain ⟨g,hg,hValue⟩:=hItems j hEnvy
      refine ⟨{g},⟨?_,by simp⟩,?_⟩
      · intro x hx
        rcases Finset.mem_singleton.mp hx with rfl
        exact hg
      · simpa only [Finset.sdiff_singleton_eq_erase] using hValue
    · refine ⟨∅,⟨Finset.empty_subset _,by simp⟩,?_⟩
      simpa only [Finset.sdiff_empty] using le_of_not_gt hEnvy

/-- The dual item-witness reading: under original envy, chores EF1 really
removes an item from the envious agent's own bundle. An empty own bundle
therefore cannot satisfy the comparison merely through a fictitious item. -/
theorem choresEF1For_iff_actual_item_of_envy {n m : ℕ}
    (v : Fin n→Finset (Fin m)→ℝ) (A : Allocation n m) (i : Fin n) :
    IsChoresEF1For v A i ↔
      ∀j : Fin n,v i (bundle A i)<v i (bundle A j)→
        ∃g∈bundle A i,v i (bundle A j)≤v i ((bundle A i).erase g) := by
  classical
  constructor
  · intro hFair j hEnvy
    obtain ⟨D,hD,hValue⟩:=hFair j
    have hNonempty : D.Nonempty := by
      by_contra hEmpty
      have hDZero : D=∅:=Finset.not_nonempty_iff_eq_empty.mp hEmpty
      have hNoEnvy : v i (bundle A j)≤v i (bundle A i) := by
        simpa only [hDZero,Finset.sdiff_empty] using hValue
      exact (not_le_of_gt hEnvy) hNoEnvy
    have hCard : D.card=1 := by
      have hPositive:=Finset.card_pos.mpr hNonempty
      have hAtMost : D.card≤1:=hD.2
      omega
    obtain ⟨g,hSingleton⟩:=Finset.card_eq_one.mp hCard
    have hgD : g∈D := by rw [hSingleton]; exact Finset.mem_singleton_self g
    refine ⟨g,hD.1 hgD,?_⟩
    simpa only [hSingleton,Finset.sdiff_singleton_eq_erase] using hValue
  · intro hItems j
    by_cases hEnvy : v i (bundle A i)<v i (bundle A j)
    · obtain ⟨g,hg,hValue⟩:=hItems j hEnvy
      refine ⟨{g},⟨?_,by simp⟩,?_⟩
      · intro x hx
        rcases Finset.mem_singleton.mp hx with rfl
        exact hg
      · simpa only [Finset.sdiff_singleton_eq_erase] using hValue
    · refine ⟨∅,⟨Finset.empty_subset _,by simp⟩,?_⟩
      simpa only [Finset.sdiff_empty] using le_of_not_gt hEnvy

/-- Restore the own-bundle deletion, as in the paper. -/
theorem ef11_goodsEF1_for {n m:ℕ} {v:Fin n→Finset (Fin m)→ℝ}
    {A:Allocation n m} (hFair:IsEF11 v A) (i:Fin n) (hMono:Monotone (v i)):
    IsGoodsEF1For v A i:=by
  intro j
  obtain ⟨C,G,hC,hG,hVal⟩:=hFair i j
  exact ⟨G,hG,hVal.trans (hMono Finset.sdiff_subset)⟩

/-- Restore the rival-bundle deletion, as in the paper. -/
theorem ef11_choresEF1_for {n m:ℕ} {v:Fin n→Finset (Fin m)→ℝ}
    {A:Allocation n m} (hFair:IsEF11 v A) (i:Fin n) (hAnti:Antitone (v i)):
    IsChoresEF1For v A i:=by
  intro j
  obtain ⟨C,G,hC,hG,hVal⟩:=hFair i j
  exact ⟨C,hC,(hAnti Finset.sdiff_subset).trans hVal⟩

/-- Section 5 corollary, permitting the monotonicity direction to differ
from agent to agent in the SAME balanced allocation. -/
theorem heterogeneous_primePower_exists_balanced_ordinaryEF1
    (p rank m:ℕ) [Fact p.Prime] (v:Fin (p^rank)→Finset (Fin m)→ℝ)
    (hDirections:∀i,Monotone (v i) ∨Antitone (v i)):
    ∃A:Allocation (p^rank) m,IsBalanced A ∧
      ∀i,(Monotone (v i)→IsGoodsEF1For v A i) ∧
        (Antitone (v i)→IsChoresEF1For v A i):=by
  obtain ⟨A,hBalance,hFair⟩:=heterogeneous_primePower_exists_balanced_ef11 p rank m v
  exact ⟨A,hBalance,fun i=>⟨ef11_goodsEF1_for hFair i,ef11_choresEF1_for hFair i⟩⟩

/-- Arbitrary positive agent count, identical nondecreasing valuations. -/
theorem identical_exists_balanced_goodsEF1 (n m:ℕ) (hn:0<n)
    (v:Finset (Fin m)→ℝ) (hMono:Monotone v):
    ∃A:Allocation n m,IsBalanced A ∧IsGoodsEF1 (fun _=>v) A:=by
  obtain ⟨A,hBalance,hFair⟩:=identical_exists_balanced_ef11 n m hn v
  exact ⟨A,hBalance,fun i=>ef11_goodsEF1_for hFair i hMono⟩

/-- Arbitrary positive agent count, identical nonincreasing valuations. -/
theorem identical_exists_balanced_choresEF1 (n m:ℕ) (hn:0<n)
    (v:Finset (Fin m)→ℝ) (hAnti:Antitone v):
    ∃A:Allocation n m,IsBalanced A ∧IsChoresEF1 (fun _=>v) A:=by
  obtain ⟨A,hBalance,hFair⟩:=identical_exists_balanced_ef11 n m hn v
  exact ⟨A,hBalance,fun i=>ef11_choresEF1_for hFair i hAnti⟩

end FairDivision.BF
