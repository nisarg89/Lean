import FairDivision.BF.Applications.GraphDensityTransfer
import FairDivision.BF.Applications.DensitySharpnessSizes

/-!
# Finite descent for the exceptional one-large-part density case

The measure is exactly the number of edgeless SMALL parts in the paper.
Move a noncentral star leaf to one of those parts. If fewer than r new edges
appear, the required density window is reached. Otherwise the new large
part is a star and the measure strictly decreases. No threshold invariant
is imposed after this transfer, in agreement with the manuscript.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.Applications

open FairDivision
open scoped Classical

/-- Size bookkeeping for the literal one-remainder regime. -/
theorem singleRemainder_balanced_of_sizes {k m r:ℕ} (hk:2≤k)
    (hCount:m=k*r+1) (A:Allocation k m)
    (hSizes:∀i,(bundle A i).card=r ∨(bundle A i).card=r+1):IsBalanced A:=by
  have hFloor:m/k=r:=by
    rw [hCount,Nat.mul_add_div (by omega :0<k),Nat.div_eq_of_lt (by omega :1<k)]
    omega
  have hMod:m%k=1:=by
    rw [hCount,Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega :1<k)]
  intro i
  rcases hSizes i with hi|hi
  ·exact Or.inl (hi.trans hFloor.symm)
  ·right
   simpa only [upperSize,hFloor,hMod,show ¬(1:ℕ)=0 by omega,if_false] using hi

/-- Exactly the edgeless-small-part count decreased in the paper. -/
def edgelessSmallParts {k m:ℕ} (G:SimpleGraph (Fin m)) (A:Allocation k m)
    (j:Fin k):Finset (Fin k):=
  Finset.univ.filter (fun i=>i≠j ∧inducedEdges G (bundle A i)=0)

/-- The initial descent measure is at most k-1, since the unique large
part is excluded from the literal set being counted. -/
theorem edgelessSmallParts_card_le {k m:ℕ} (G:SimpleGraph (Fin m))
    (A:Allocation k m) (j:Fin k):
    (edgelessSmallParts G A j).card≤k-1:=by
  have hSubset:edgelessSmallParts G A j⊆(Finset.univ:Finset (Fin k)).erase j:=by
    intro i hi
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hi).2.1,Finset.mem_univ _⟩
  have hCard:=Finset.card_le_card hSubset
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ,Fintype.card_fin] using hCard

theorem edgelessSmallParts_card_lt {k m:ℕ} (G:SimpleGraph (Fin m))
    (A:Allocation k m) (j:Fin k):
    (edgelessSmallParts G A j).card<k:=by
  have h:=edgelessSmallParts_card_le G A j
  have hj:=j.isLt
  omega

private theorem density_positive_lower {m r:ℕ} (G:SimpleGraph (Fin m))
    (S:Finset (Fin m)) (hr:0<r) (hSize:S.card=r) (hPos:inducedEdges G S≠0):
    (1:ℝ)/r≤graphDensity G S:=by
  have hEdgeNat:1≤ inducedEdges G S:=Nat.one_le_iff_ne_zero.mpr hPos
  have hEdge:(1:ℝ)≤ inducedEdges G S:=by exact_mod_cast hEdgeNat
  dsimp only [graphDensity]
  rw [hSize]
  exact div_le_div_of_nonneg_right hEdge (Nat.cast_nonneg _)

private theorem density_star_value {m r:ℕ} (G:SimpleGraph (Fin m))
    (S:Finset (Fin m)) (hSize:S.card=r+1) (hStar:IsDensityStar G S):
    graphDensity G S=densityRadius (r+1):=by
  obtain ⟨c,hc,hEdges,hDelete⟩:=hStar
  rw [graphDensity,hEdges,hSize]
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,densityRadius]
  congr 1
  ring

private theorem densityRadius_single_arithmetic {r:ℕ} (hr:2≤r):
    (1:ℝ)/r≤densityRadius (r+1) ∧
      densityRadius (r+1)-(1:ℝ)/r≤densityRadius r:=by
  have hrR:(2:ℝ)≤r:=by exact_mod_cast hr
  have hPos:0<(r:ℝ):=by linarith
  have hSucc:0<(r:ℝ)+1:=by linarith
  constructor
  · dsimp [densityRadius]
    push_cast
    rw [div_le_div_iff₀ hPos hSucc]
    have hSquare:2*(r:ℝ)≤(r:ℝ)*(r:ℝ):=by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hrR hPos.le
    nlinarith
  · have hAlpha:densityRadius r=1-(1:ℝ)/r:=by
      unfold densityRadius
      rw [sub_div,div_self hPos.ne']
    have hBeta:densityRadius (r+1)≤1:=by
      unfold densityRadius
      push_cast
      apply (div_le_iff₀ hSucc).mpr
      linarith
    rw [hAlpha]
    linarith

/-- With no edgeless small part, positive integer edge counts give the
paper's final beta-1/r≤alpha estimate. -/
theorem densityStar_no_edgeless_spread {k m r:ℕ} (hr:2≤r)
    (G:SimpleGraph (Fin m)) (A:Allocation k m) (j:Fin k)
    (hLarge:(bundle A j).card=r+1) (hStar:IsDensityStar G (bundle A j))
    (hSmall:∀i:Fin k,i≠j→(bundle A i).card=r ∧
      0≤graphDensity G (bundle A i) ∧graphDensity G (bundle A i)≤densityRadius r)
    (hNo:(edgelessSmallParts G A j)=∅):HasDensitySpread G A (densityRadius r):=by
  have hLargeVal:=density_star_value G _ hLarge hStar
  have hRadius:=densityRadius_mono (by omega :0<r) (Nat.le_succ r)
  have hArithmetic:=densityRadius_single_arithmetic hr
  have hBounds:∀i:Fin k,(1:ℝ)/r≤graphDensity G (bundle A i) ∧
      graphDensity G (bundle A i)≤densityRadius (r+1):=by
    intro i
    by_cases hi:i=j
    ·subst i
     rw [hLargeVal]
     exact ⟨hArithmetic.1,le_rfl⟩
    ·have hPos:inducedEdges G (bundle A i)≠0:=by
       intro he
       have hiMem:i∈edgelessSmallParts G A j:=Finset.mem_filter.mpr
         ⟨Finset.mem_univ _,hi,he⟩
       simpa only [hNo,Finset.notMem_empty] using hiMem
     exact ⟨density_positive_lower G _ (by omega) (hSmall i hi).1 hPos,
       (hSmall i hi).2.2.trans hRadius⟩
  intro i l
  linarith [(hBounds i).2,(hBounds l).1,hArithmetic.2]

/-- One literal leaf transfer either reaches the target window, or
recreates the same star state with strictly fewer edgeless small parts. -/
theorem densityStar_transfer_step {k m r:ℕ} (hk:2≤k) (hr:2≤r)
    (hCount:m=k*r+1) (G:SimpleGraph (Fin m)) (A:Allocation k m) (j:Fin k)
    (hLarge:(bundle A j).card=r+1) (hStar:IsDensityStar G (bundle A j))
    (hSmall:∀i:Fin k,i≠j→(bundle A i).card=r ∧
      0≤graphDensity G (bundle A i) ∧graphDensity G (bundle A i)≤densityRadius r)
    (i:Fin k) (hi:i∈edgelessSmallParts G A j):
    (∃A':Allocation k m,IsBalanced A' ∧HasDensitySpread G A' (densityRadius r)) ∨
    ∃(A':Allocation k m)(j':Fin k),
      (bundle A' j').card=r+1 ∧IsDensityStar G (bundle A' j') ∧
      (∀l:Fin k,l≠j'→(bundle A' l).card=r ∧
        0≤graphDensity G (bundle A' l) ∧graphDensity G (bundle A' l)≤densityRadius r) ∧
      (edgelessSmallParts G A' j').card<(edgelessSmallParts G A j).card:=by
  obtain ⟨hij,hEmpty⟩:=(Finset.mem_filter.mp hi).2
  obtain ⟨c,hc,hEdges,hDelete⟩:=hStar
  have hLeafCount:0<((bundle A j).erase c).card:=by
    rw [Finset.card_erase_of_mem hc,hLarge]
    omega
  obtain ⟨z,hzErase⟩:=Finset.card_pos.mp hLeafCount
  have hz:z∈bundle A j:=(Finset.mem_erase.mp hzErase).2
  have hzc:z≠c:=(Finset.mem_erase.mp hzErase).1
  have hOwner:A z=j:=(Finset.mem_filter.mp hz).2
  have hzNot:z∉bundle A i:=by
    intro hzI
    exact hij ((Finset.mem_filter.mp hzI).2.symm.trans hOwner)
  let A':=transferVertex A z i
  have hRecipient:bundle A' i=insert z (bundle A i):=
    transferVertex_recipient A z i (by rw [hOwner];exact hij.symm)
  have hDonor:bundle A' j=(bundle A j).erase z:=transferVertex_donor A z i j hOwner hij
  have hOther:∀l:Fin k,l≠i→l≠j→bundle A' l=bundle A l:=
    fun l hli hlj=>transferVertex_other A z i j l hOwner hli hlj
  have hNewSize:(bundle A' i).card=r+1:=by
    rw [hRecipient,Finset.card_insert_of_notMem hzNot,(hSmall i hij).1]
  have hOldSize:(bundle A' j).card=r:=by
    rw [hDonor,Finset.card_erase_of_mem hz,hLarge]
    omega
  have hEraseChoice :
      @Finset.erase (Fin m) (Classical.decEq (Fin m)) (bundle A j) z=
        (bundle A j).erase z:=by
    ext y
    simp only [Finset.mem_erase]
  have hInsertChoice :
      @insert (Fin m) (Finset (Fin m))
        (@Finset.instInsert (Fin m) (Classical.decEq (Fin m))) z (bundle A i)=
        insert z (bundle A i):=by
    ext y
    simp only [Finset.mem_insert]
  have hOldEdges:inducedEdges G (bundle A' j)=r-1:=by
    have hLeaf:=densityStar_erase_leaf_edges G _ c z hc hEdges hDelete hz hzc
    rw [hEraseChoice,hLarge] at hLeaf
    rw [hDonor,hLeaf]
    omega
  have hOldDensity:graphDensity G (bundle A' j)=densityRadius r:=by
    rw [graphDensity,hOldEdges,hOldSize,densityRadius,Nat.cast_sub (by omega :1≤r)]
    norm_num
  have hNewEdges:inducedEdges G (bundle A' i)≤r:=by
    rw [hRecipient]
    simpa only [hInsertChoice,(hSmall i hij).1] using
      (edges_insert_into_edgeless G _ z hzNot hEmpty).2
  have hBalanced:IsBalanced A':=by
    apply singleRemainder_balanced_of_sizes hk hCount
    intro l
    by_cases hli:l=i
    ·subst l;exact Or.inr hNewSize
    by_cases hlj:l=j
    ·subst l;exact Or.inl hOldSize
    ·exact Or.inl (by rw [hOther l hli hlj];exact (hSmall l hlj).1)
  by_cases hFull:inducedEdges G (bundle A' i)=r
  · right
    have hNewStar:IsDensityStar G (bundle A' i):=by
      rw [hRecipient]
      have hInserted:inducedEdges G
          (@insert (Fin m) (Finset (Fin m))
            (@Finset.instInsert (Fin m) (Classical.decEq (Fin m))) z (bundle A i))=
          (bundle A i).card:=by
        simpa only [hInsertChoice,←hRecipient,(hSmall i hij).1] using hFull
      simpa only [hInsertChoice] using
        inserted_full_degree_is_densityStar G _ z hzNot hEmpty hInserted
    have hNewSmall:∀l:Fin k,l≠i→(bundle A' l).card=r ∧
        0≤graphDensity G (bundle A' l) ∧graphDensity G (bundle A' l)≤densityRadius r:=by
      intro l hli
      by_cases hlj:l=j
      ·subst l
       exact ⟨hOldSize,graphDensity_nonneg _ _,hOldDensity.le⟩
      ·rw [hOther l hli hlj]
       exact hSmall l hlj
    have hMeasure:edgelessSmallParts G A' i=(edgelessSmallParts G A j).erase i:=by
      ext l
      by_cases hli:l=i
      ·subst l;simp [edgelessSmallParts]
      by_cases hlj:l=j
      ·subst l
       have hPositive:inducedEdges G (bundle A' j)≠0:=by rw [hOldEdges];omega
       simp [edgelessSmallParts,hij.symm,hPositive]
      ·simp only [edgelessSmallParts,Finset.mem_filter,Finset.mem_univ,true_and,
         Finset.mem_erase,hli,hlj,hOther l hli hlj]
       tauto
    refine ⟨A',i,hNewSize,hNewStar,hNewSmall,?_⟩
    rw [hMeasure,Finset.card_erase_of_mem hi]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨i,hi⟩) (by omega)
  · left
    have hStrict:inducedEdges G (bundle A' i)≤r-1:=by omega
    have hrR:0<(r:ℝ):=by exact_mod_cast (by omega :0<r)
    have hSuccR:0<(r:ℝ)+1:=by linarith
    have hNewDensity:graphDensity G (bundle A' i)≤densityRadius r:=by
      rw [graphDensity,hNewSize,densityRadius]
      have he:(inducedEdges G (bundle A' i):ℝ)≤(r:ℝ)-1:=by
        have h:(inducedEdges G (bundle A' i):ℝ)≤(r-1:ℕ):=by exact_mod_cast hStrict
        simpa only [Nat.cast_sub (by omega :1≤r),Nat.cast_one] using h
      push_cast
      rw [div_le_div_iff₀ hSuccR hrR]
      have hrOne:(1:ℝ)≤r:=by exact_mod_cast (by omega :1≤r)
      have hMul:=mul_le_mul_of_nonneg_right he hrR.le
      nlinarith
    have hAll:∀l:Fin k,graphDensity G (bundle A' l)≤densityRadius r:=by
      intro l
      by_cases hli:l=i
      ·subst l;exact hNewDensity
      by_cases hlj:l=j
      ·subst l;exact hOldDensity.le
      ·rw [hOther l hli hlj];exact (hSmall l hlj).2.2
    exact ⟨A',hBalanced,fun l u=>by linarith [hAll l,graphDensity_nonneg G (bundle A' u)]⟩

/-- The paper's complete finite descent, with no preserved-threshold
premise: the natural edgeless-small count decreases after every continued
transfer, hence at most k-1 transfers can occur. -/
theorem densityStar_descent_exists {k m r:ℕ} (hk:2≤k) (hr:2≤r)
    (hCount:m=k*r+1) (G:SimpleGraph (Fin m)) (A:Allocation k m) (j:Fin k)
    (hLarge:(bundle A j).card=r+1) (hStar:IsDensityStar G (bundle A j))
    (hSmall:∀i:Fin k,i≠j→(bundle A i).card=r ∧
      0≤graphDensity G (bundle A i) ∧graphDensity G (bundle A i)≤densityRadius r):
    ∃A':Allocation k m,IsBalanced A' ∧HasDensitySpread G A' (densityRadius r):=by
  suffices h:∀b:ℕ,∀(A:Allocation k m)(j:Fin k),
      (bundle A j).card=r+1→IsDensityStar G (bundle A j)→
      (∀i:Fin k,i≠j→(bundle A i).card=r ∧
        0≤graphDensity G (bundle A i) ∧graphDensity G (bundle A i)≤densityRadius r)→
      (edgelessSmallParts G A j).card=b→
      ∃A':Allocation k m,IsBalanced A' ∧HasDensitySpread G A' (densityRadius r) by
    exact h _ A j hLarge hStar hSmall rfl
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro A j hLarge hStar hSmall hMeasure
    by_cases hEmpty:edgelessSmallParts G A j=∅
    · refine ⟨A,singleRemainder_balanced_of_sizes hk hCount A ?_,
        densityStar_no_edgeless_spread hr G A j hLarge hStar hSmall hEmpty⟩
      intro i
      by_cases hi:i=j
      ·subst i;exact Or.inr hLarge
      ·exact Or.inl (hSmall i hi).1
    · obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hEmpty
      rcases densityStar_transfer_step hk hr hCount G A j hLarge hStar hSmall i hi with
        hDone|⟨A',j',hLarge',hStar',hSmall',hDecrease⟩
      ·exact hDone
      ·apply ih (edgelessSmallParts G A' j').card (by simpa only [hMeasure] using hDecrease)
        A' j' hLarge' hStar' hSmall' rfl

end FairDivision.BF.Applications
