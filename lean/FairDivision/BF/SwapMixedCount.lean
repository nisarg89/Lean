import FairDivision.BF.SwapObstruction

/-!
# Exact count and pair indexing for the manuscript's obstruction event

Among the choose(2q,q) q-subsets of two disjoint q-bundles, exactly their
two complete bundles are unmixed. The resulting count depends only on q.
The event variables remain actual item subsets throughout; no quotient of
random coordinates or duplicate-removal premise is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace FairDivision.BF.SwapObstruction

open scoped BigOperators

variable {n m q : ℕ}

/-- Actual finite coordinate block of a pair-event. -/
def mixedFamily (q : ℕ) (S T : Finset (Fin m)) : Finset (Finset (Fin m)) := by
  classical
  exact ((S∪T).powersetCard q).filter (fun U=>(U∩S).Nonempty ∧(U∩T).Nonempty)

@[simp] theorem mem_mixedFamily (S T U : Finset (Fin m)) :
    U∈mixedFamily q S T ↔Mixed q S T U := by
  classical
  simp only [mixedFamily,Finset.mem_filter,Finset.mem_powersetCard,Mixed,and_assoc]

theorem mixedFamily_comm (S T : Finset (Fin m)) : mixedFamily q S T=mixedFamily q T S := by
  classical
  ext U
  simp only [mem_mixedFamily,Mixed,Finset.union_comm,and_comm,and_left_comm,and_assoc]

/-- The exact two unmixed subsets are removed physically from the finite
q-subset family. -/
theorem mixedFamily_eq_erase (hq : 0<q) (S T : Finset (Fin m))
    (hST : Disjoint S T) (hS : S.card=q) (hT : T.card=q) :
    mixedFamily q S T=(((S∪T).powersetCard q).erase S).erase T := by
  classical
  ext U
  simp only [mem_mixedFamily,Finset.mem_erase,Finset.mem_powersetCard]
  constructor
  · rintro ⟨hSub,hCard,hMeetS,hMeetT⟩
    have hNotS : U≠S:=by
      intro h
      have hEmpty : U∩T=∅:=by rw [h];exact Finset.disjoint_iff_inter_eq_empty.mp hST
      simpa only [hEmpty,Finset.not_nonempty_empty] using hMeetT
    have hNotT : U≠T:=by
      intro h
      have hEmpty : U∩S=∅:=by rw [h];exact Finset.disjoint_iff_inter_eq_empty.mp hST.symm
      simpa only [hEmpty,Finset.not_nonempty_empty] using hMeetS
    exact ⟨hNotT,hNotS,hSub,hCard⟩
  · rintro ⟨hNotT,hNotS,hSub,hCard⟩
    refine ⟨hSub,hCard,?_,?_⟩
    · by_contra hMeet
      apply hNotT
      apply Finset.eq_of_subset_of_card_le ?_ (by omega)
      intro g hg
      rcases Finset.mem_union.mp (hSub hg) with hgS|hgT
      · exact False.elim (hMeet ⟨g,Finset.mem_inter.mpr ⟨hg,hgS⟩⟩)
      · exact hgT
    · by_contra hMeet
      apply hNotS
      apply Finset.eq_of_subset_of_card_le ?_ (by omega)
      intro g hg
      rcases Finset.mem_union.mp (hSub hg) with hgS|hgT
      · exact hgS
      · exact False.elim (hMeet ⟨g,Finset.mem_inter.mpr ⟨hg,hgT⟩⟩)

theorem mixedFamily_card (hq : 0<q) (S T : Finset (Fin m))
    (hST : Disjoint S T) (hS : S.card=q) (hT : T.card=q) :
    (mixedFamily q S T).card=(2*q).choose q-2 := by
  classical
  have hSNonempty : S.Nonempty:=Finset.card_pos.mp (by omega)
  have hDifferent : S≠T := by
    intro h
    obtain ⟨g,hg⟩:=hSNonempty
    exact Finset.disjoint_left.mp hST hg (h▸hg)
  have hMemS : S∈(S∪T).powersetCard q := by simp only [Finset.mem_powersetCard];exact ⟨Finset.subset_union_left,hS⟩
  have hMemT : T∈((S∪T).powersetCard q).erase S := by
    exact Finset.mem_erase.mpr ⟨hDifferent.symm,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_union_right,hT⟩⟩
  rw [mixedFamily_eq_erase hq S T hST hS hT,Finset.card_erase_of_mem hMemT,
    Finset.card_erase_of_mem hMemS,Finset.card_powersetCard,
    Finset.card_union_of_disjoint hST,hS,hT]
  have hDouble : q+q=2*q:=by omega
  rw [hDouble]
  omega

/-- One actual unordered pair of distinct agent labels. -/
abbrev AgentPair (n : ℕ):={S : Finset (Fin n) // S.card=2}

/-- Its cardinality is Mathlib's existing powerset-cardinality formula. -/
theorem agentPair_card (n : ℕ) : Fintype.card (AgentPair n)=n.choose 2 := by
  classical
  let e : AgentPair n ≃ ↥((Finset.univ : Finset (Fin n)).powersetCard 2) :=
    { toFun := fun S=>⟨S.1,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,S.2⟩⟩
      invFun := fun S=>⟨S.1,(Finset.mem_powersetCard.mp S.2).2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard,
    Finset.card_univ,Fintype.card_fin]

/-- Fixed representative order; probability conditioning orients it later
according to the sampled original bundle weights. -/
def representatives (P : AgentPair n) : Fin n×Fin n:=
  let h:=Finset.card_eq_two.mp P.2
  (h.choose,h.choose_spec.choose)

theorem representatives_spec (P : AgentPair n) :
    (representatives P).1≠(representatives P).2 ∧
      P.1={(representatives P).1,(representatives P).2} := by
  have h:=Finset.card_eq_two.mp P.2
  exact h.choose_spec.choose_spec

/-- The physical mixed-coordinate block attached to an unordered pair. -/
def pairBlock (A : Allocation n m) (P : AgentPair n) : Finset (Finset (Fin m)) :=
  mixedFamily q (bundle A (representatives P).1) (bundle A (representatives P).2)

/-- Exactly the coordinate-disjointness asserted in the manuscript's
conditional independence lemma. -/
theorem pairBlocks_disjoint (A : Allocation n m) :
    Set.PairwiseDisjoint Set.univ (pairBlock (q:=q) A) := by
  classical
  intro P hP Q hQ hDifferent
  apply Finset.disjoint_left.mpr
  intro U hUP hUQ
  apply hDifferent
  apply Subtype.ext
  rw [(representatives_spec P).2,(representatives_spec Q).2]
  exact mixed_pair_unique A _ _ _ _ U
    ((mem_mixedFamily (q:=q) _ _ U).mp hUP)
    ((mem_mixedFamily (q:=q) _ _ U).mp hUQ)

end FairDivision.BF.SwapObstruction
