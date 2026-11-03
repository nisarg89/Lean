import FairDivision.BF.SwapPerturbedValuation

/-!
# The manuscript's mixed-set obstruction and disjoint coordinate blocks

Every swap of at most t items preserves a strict majority of its original
q-bundle when q≥2t+1. The obstruction puts every such majority-i mixed
set below 1/2 and every majority-j mixed set above 1/2. These constraints
cannot conflict, and their actual coordinate sets are disjoint for
DIFFERENT unordered pairs of allocation bundles. These are exactly the
combinatorial inputs to the conditional probability calculation.
-/

set_option autoImplicit false

namespace FairDivision.BF.SwapObstruction

open FairDivision.BF
open SwapPerturbedValuation

variable {m q : ℕ}

/-- A mixed q-subset meets both specified original bundles. -/
def Mixed (q : ℕ) (S T U : Finset (Fin m)) : Prop :=
  U⊆S∪T ∧U.card=q ∧(U∩S).Nonempty ∧(U∩T).Nonempty

/-- The literal obstruction event, oriented from the lower ORIGINAL
bundle weight to the higher one. Tied half-and-half subsets are unrestricted. -/
def Obstruction (q : ℕ) (W : Finset (Fin m)→ℝ) (S T : Finset (Fin m)) : Prop :=
  ∀U,Mixed q S T U→
    (q<2*(U∩S).card→W U<(1 : ℝ)/2) ∧
    (q<2*(U∩T).card→(1 : ℝ)/2<W U)

/-- Disjoint original bundles cannot both have a strict majority in a
single q-item subset. -/
theorem majority_incompatible (S T U : Finset (Fin m)) (hST : Disjoint S T)
    (hU : U.card=q) : ¬(q<2*(U∩S).card ∧q<2*(U∩T).card) := by
  have hDisjoint : Disjoint (U∩S) (U∩T):=
    hST.mono Finset.inter_subset_right Finset.inter_subset_right
  have hCard : (U∩S).card+(U∩T).card≤q := by
    rw [←Finset.card_union_of_disjoint hDisjoint,←hU]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
  omega

/-- Exact post-swap intersections, using only the two subset constraints
and disjointness of the two original bundles. -/
theorem post_intersections (S T X Y : Finset (Fin m))
    (hST : Disjoint S T) (hX : X⊆S) (hY : Y⊆T) :
    (((S\X)∪Y)∩S=S\X) ∧(((S\X)∪Y)∩T=Y) := by
  classical
  have hSeparate : ∀g : Fin m,g∈S → g∈T → False:=Finset.disjoint_left.mp hST
  constructor <;> ext g <;>
    simp only [Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff] <;>
    aesop

/-- A genuine small swap produces a mixed q-set with strict majority
from the bundle retaining q−k items. -/
theorem post_mixed_majority {t k : ℕ}
    (hThreshold : 2*t+1≤q) (hkPositive : 1≤k) (hk : k≤t)
    (S T X Y : Finset (Fin m)) (hST : Disjoint S T)
    (hS : S.card=q) (hT : T.card=q) (hX : X⊆S) (hY : Y⊆T)
    (hXC : X.card=k) (hYC : Y.card=k) :
    Mixed q S T ((S\X)∪Y) ∧q<2*(((S\X)∪Y)∩S).card := by
  have hInter:=post_intersections S T X Y hST hX hY
  have hCard : ((S\X)∪Y).card=q := by
    rw [Finset.card_union_of_disjoint (hST.mono Finset.sdiff_subset hY),
      Finset.card_sdiff_of_subset hX,hS,hXC,hYC]
    have hkq : k≤q:=by omega
    omega
  have hSC : (((S\X)∪Y)∩S).card=q-k := by
    rw [hInter.1,Finset.card_sdiff_of_subset hX,hS,hXC]
  have hTC : (((S\X)∪Y)∩T).card=k:=by rw [hInter.2,hYC]
  refine ⟨⟨Finset.union_subset
    (Finset.Subset.trans Finset.sdiff_subset Finset.subset_union_left)
    (Finset.Subset.trans hY Finset.subset_union_right),hCard,
    Finset.card_pos.mp (by omega),Finset.card_pos.mp (by omega)⟩,?_⟩
  rw [hSC]
  omega

/-- Effect of the event on EVERY legal swap, as in the manuscript's swap argument. -/
theorem obstruction_blocks_every_swap {t : ℕ} (hThreshold : 2*t+1≤q)
    (W : Finset (Fin m)→ℝ) (S T : Finset (Fin m)) (hST : Disjoint S T)
    (hS : S.card=q) (hT : T.card=q) (hObstruction : Obstruction q W S T)
    (X Y : Finset (Fin m)) (hX : X⊆S) (hY : Y⊆T)
    (hkPositive : 1≤X.card) (hkEqual : X.card=Y.card) (hk : X.card≤t) :
    value q W ((S\X)∪Y)<value q W ((T\Y)∪X) := by
  have hLeft:=post_mixed_majority hThreshold hkPositive hk S T X Y hST hS hT
    hX hY rfl hkEqual.symm
  have hRight:=post_mixed_majority hThreshold hkPositive hk T S Y X hST.symm hT hS
    hY hX hkEqual.symm rfl
  have hMixedRight : Mixed q S T ((T\Y)∪X) := by
    obtain ⟨hSub,hCard,hMeetT,hMeetS⟩:=hRight.1
    exact ⟨by simpa only [Finset.union_comm] using hSub,hCard,hMeetS,hMeetT⟩
  apply (comparison_on_layer W _ _ hLeft.1.2.1 hRight.1.2.1).mpr
  exact lt_trans ((hObstruction _ hLeft.1).1 hLeft.2)
    ((hObstruction _ hMixedRight).2 hRight.2)

/-- A mixed subset intersects exactly the two named allocation bundles. -/
theorem mixed_meets_iff {n : ℕ} (A : Allocation n m) (i j k : Fin n)
    (U : Finset (Fin m)) (hU : Mixed q (bundle A i) (bundle A j) U) :
    (U∩bundle A k).Nonempty ↔ k=i ∨k=j := by
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨hgU,hgK⟩:=Finset.mem_inter.mp hg
    have hOwnerK : A g=k:=by simpa only [bundle,Finset.mem_filter,
      Finset.mem_univ,true_and] using hgK
    rcases Finset.mem_union.mp (hU.1 hgU) with hgI|hgJ
    · left
      have hOwnerI : A g=i:=by simpa only [bundle,Finset.mem_filter,
        Finset.mem_univ,true_and] using hgI
      exact hOwnerK.symm.trans hOwnerI
    · right
      have hOwnerJ : A g=j:=by simpa only [bundle,Finset.mem_filter,
        Finset.mem_univ,true_and] using hgJ
      exact hOwnerK.symm.trans hOwnerJ
  · rintro (rfl|rfl)
    · exact hU.2.2.1
    · exact hU.2.2.2

/-- The coordinates on which different unordered-pair events depend are
literally disjoint, not just pairwise uncorrelated. -/
theorem mixed_pair_unique {n : ℕ} (A : Allocation n m) (i j k l : Fin n)
    (U : Finset (Fin m))
    (hFirst : Mixed q (bundle A i) (bundle A j) U)
    (hSecond : Mixed q (bundle A k) (bundle A l) U) :
    ({i,j} : Finset (Fin n))={k,l} := by
  classical
  ext h
  simpa only [Finset.mem_insert,Finset.mem_singleton] using
    (mixed_meets_iff A i j h U hFirst).symm.trans (mixed_meets_iff A k l h U hSecond)

/-- No mixed coordinate is an original allocation-bundle coordinate, so
conditioning on all original bundle weights fixes NONE of these variables. -/
theorem mixed_ne_original_bundle {n : ℕ} (A : Allocation n m)
    (i j : Fin n) (hij : i≠j) (U : Finset (Fin m))
    (hMixed : Mixed q (bundle A i) (bundle A j) U) (k : Fin n) : U≠bundle A k := by
  intro hEq
  have hSeparate (a b : Fin n) (hMeet : (bundle A a∩bundle A b).Nonempty) : a=b := by
    obtain ⟨g,hg⟩:=hMeet
    obtain ⟨hgA,hgB⟩:=Finset.mem_inter.mp hg
    have hA : A g=a:=by simpa [bundle] using hgA
    have hB : A g=b:=by simpa [bundle] using hgB
    exact hA.symm.trans hB
  apply hij
  have hKI : k=i:=hSeparate k i (by simpa only [hEq] using hMixed.2.2.1)
  have hKJ : k=j:=hSeparate k j (by simpa only [hEq] using hMixed.2.2.2)
  exact hKI.symm.trans hKJ

/-- Disjointness of actual owner-map bundles, kept in the BF layer so
this certificate never imports the FE optimization development. -/
theorem allocation_bundle_disjoint {n : ℕ} (A : Allocation n m)
    (i j : Fin n) (hij : i≠j) : Disjoint (bundle A i) (bundle A j) := by
  apply Finset.disjoint_left.mpr
  intro g hgi hgj
  have hI : A g=i:=by simpa [bundle] using hgi
  have hJ : A g=j:=by simpa [bundle] using hgj
  exact hij (hI.symm.trans hJ)

/-- One oriented obstruction with strict original envy rules out the
actual t-swap allocation predicate. -/
theorem not_tSwapEF_of_obstruction {n t : ℕ} (hThreshold : 2*t+1≤q)
    (W : Finset (Fin m)→ℝ) (A : Allocation n m) (hSize : HasEqualBundleSize A q)
    (i j : Fin n) (hEnvy : W (bundle A i)<W (bundle A j))
    (hObstruction : Obstruction q W (bundle A i) (bundle A j)) :
    ¬IsTSwapEF t (fun _=>value q W) A := by
  intro hFair
  have hOriginalEnvy : value q W (bundle A i)<value q W (bundle A j) :=
    (comparison_on_layer W _ _ (hSize i) (hSize j)).mpr hEnvy
  obtain ⟨X,Y,hX,hY,hPositive,hEqual,hLe,hPost⟩:=hFair i j hOriginalEnvy
  have hij : i≠j:=by
    intro h
    subst j
    exact (lt_irrefl _) hEnvy
  have hDisjoint:=allocation_bundle_disjoint A i j hij
  exact (not_lt_of_ge hPost) (obstruction_blocks_every_swap hThreshold W _ _ hDisjoint
    (hSize i) (hSize j) hObstruction X Y hX hY hPositive hEqual hLe)

end FairDivision.BF.SwapObstruction
