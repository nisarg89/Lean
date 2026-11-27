import EF1FPO.Model

/-! Supporting prices, bounded transfers, and rounding on a forest. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO.Instance

variable (I : Instance)

theorem bid_le_price (w : I.Weights) (i : I.Agent) (g : I.Good) :
    I.bid w i g ≤ I.price w g := by
  exact Finset.le_sup' (fun j => I.bid w j g) (Finset.mem_univ i)

theorem highest_bidder_iff_bid_eq_price (w : I.Weights) (i : I.Agent) (g : I.Good) :
    I.IsHighestBidder w i g ↔ I.bid w i g = I.price w g := by
  constructor
  · intro hi
    apply le_antisymm (Finset.le_sup' (fun j => I.bid w j g) (Finset.mem_univ i))
    exact Finset.sup'_le _ _ (fun j _ => hi j)
  · intro hi j
    rw [hi]
    exact Finset.le_sup' (fun k => I.bid w k g) (Finset.mem_univ j)

theorem exists_highest_bidder (w : I.Weights) (g : I.Good) :
    ∃ i, I.IsHighestBidder w i g := by
  have hn : (Finset.univ : Finset I.Agent).Nonempty := ⟨⟨0, I.hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hn (fun j => I.bid w j g)
  refine ⟨i, fun j => ?_⟩
  rw [← hi]
  exact Finset.le_sup' (fun k => I.bid w k g) (Finset.mem_univ j)

theorem price_nonneg (w : I.Weights) (hw : I.Positive w) (g : I.Good) :
    0 ≤ I.price w g := by
  let i : I.Agent := ⟨0, I.hn⟩
  have hv : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
  exact (mul_nonneg (hw i).le hv).trans
    (Finset.le_sup' (fun j => I.bid w j g) (Finset.mem_univ i))

theorem trim_le_delete (w : I.Weights) (S : Finset I.Good) {g : I.Good} (hg : g ∈ S) :
    I.trim w S ≤ I.bundlePrice w (S.erase g) := by
  unfold trim bundlePrice
  rw [dite_eq_left ⟨g, hg⟩]
  have hprice := Finset.le_sup' (I.price w) hg
  have hsum := Finset.sum_erase_add S (I.price w) hg
  linarith

theorem exists_delete_eq_trim (w : I.Weights) (S : Finset I.Good) (hS : S.Nonempty) :
    ∃ g ∈ S, I.bundlePrice w (S.erase g) = I.trim w S := by
  obtain ⟨g, hg, hprice⟩ := Finset.exists_mem_eq_sup' hS (I.price w)
  refine ⟨g, hg, ?_⟩
  unfold trim bundlePrice
  rw [dite_eq_left hS, hprice]
  have hsum := Finset.sum_erase_add S (I.price w) hg
  linarith

theorem trim_mono (w : I.Weights) (hw : I.Positive w)
    {S T : Finset I.Good} (hST : S ⊆ T) : I.trim w S ≤ I.trim w T := by
  have hsum {S' T' : Finset I.Good} (h : S' ⊆ T') :
      I.bundlePrice w S' ≤ I.bundlePrice w T' :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => I.price_nonneg w hw g)
  by_cases hT : T.Nonempty
  · obtain ⟨g, hg, htrim⟩ := I.exists_delete_eq_trim w T hT
    rw [← htrim]
    by_cases hgS : g ∈ S
    · exact (I.trim_le_delete w S hgS).trans (hsum (Finset.erase_subset_erase g hST))
    · have hsub : S ⊆ T.erase g := fun f hf =>
        Finset.mem_erase.mpr ⟨fun hfg => hgS (hfg ▸ hf), hST hf⟩
      by_cases hS : S.Nonempty
      · obtain ⟨f, _, htrimS⟩ := I.exists_delete_eq_trim w S hS
        rw [← htrimS]
        exact hsum ((Finset.erase_subset f S).trans hsub)
      · rw [trim, dite_eq_right hS]
        exact Finset.sum_nonneg (fun f _ => I.price_nonneg w hw f)
  · have hTe : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hSe : S = ∅ := Finset.subset_empty.mp (hTe ▸ hST)
    simp [hSe, hTe]

theorem supported_bundlePrice (w : I.Weights) (A : I.Allocation) (hA : I.IsSupported w A)
    (i : I.Agent) :
    I.bundlePrice w (FairDivision.bundle A i) = w i * I.utility i (FairDivision.bundle A i) := by
  simp only [bundlePrice, FairDivision.additiveValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have howner : A g = i := by simpa [FairDivision.bundle] using hg
  exact ((I.highest_bidder_iff_bid_eq_price w i g).mp (howner ▸ hA g)).symm

theorem fractional_weighted_utility_le_total_price (w : I.Weights) (x : I.Shares)
    (hx : I.IsFractional x) : (∑ i, w i * I.fractionalUtility x i) ≤ ∑ g, I.price w g := by
  obtain ⟨hn, hcol⟩ := hx
  calc
    (∑ i, w i * I.fractionalUtility x i) = ∑ g, ∑ i, I.bid w i g * x i g := by
      simp only [FairDivision.fractionalValue, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro i _
      unfold bid
      ring
    _ ≤ ∑ g, ∑ i, I.price w g * x i g := by
      refine Finset.sum_le_sum (fun g _ => Finset.sum_le_sum (fun i _ => ?_))
      exact mul_le_mul_of_nonneg_right (I.bid_le_price w i g) (hn i g)
    _ = ∑ g, I.price w g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.mul_sum, hcol, mul_one]

theorem supported_weighted_utility_eq_total_price (w : I.Weights) (A : I.Allocation)
    (hA : I.IsSupported w A) :
    (∑ i, w i * I.utility i (FairDivision.bundle A i)) = ∑ g, I.price w g := by
  rw [← Finset.sum_fiberwise Finset.univ A (I.price w)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [FairDivision.additiveValue, Finset.mul_sum, FairDivision.bundle]
  apply Finset.sum_congr rfl
  intro g hg
  have howner : A g = i := (Finset.mem_filter.mp hg).2
  exact (I.highest_bidder_iff_bid_eq_price w i g).mp (howner ▸ hA g)

/-- Supporting weights certify efficiency also against fractional competitors. -/
theorem fpo_of_supported (w : I.Weights) (A : I.Allocation)
    (hw : I.Positive w) (hA : I.IsSupported w A) : I.IsFPO A := by
  rintro x hx ⟨hweak, i, hstrict⟩
  have hbetter : (∑ j, w j * I.utility j (FairDivision.bundle A j)) <
      ∑ j, w j * I.fractionalUtility x j := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_le_mul_of_nonneg_left (hweak j) (hw j).le
    · exact ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hstrict (hw i)⟩
  rw [I.supported_weighted_utility_eq_total_price w A hA] at hbetter
  exact (not_lt_of_ge (I.fractional_weighted_utility_le_total_price w x hx)) hbetter

/-- A lower spending band and an upper after-removal band imply EF1. -/
theorem ef1_of_bands (w : I.Weights) (A : I.Allocation) (τ : ℝ)
    (hw : I.Positive w) (hA : I.IsSupported w A) (hb : I.Bands w A τ) : I.IsEF1 A := by
  intro i j hj
  obtain ⟨g, hg, hdelete⟩ := I.exists_delete_eq_trim w (FairDivision.bundle A j) hj
  refine ⟨g, hg, (mul_le_mul_iff_of_pos_left (hw i)).mp ?_⟩
  calc
    w i * I.utility i ((FairDivision.bundle A j).erase g) ≤
        I.bundlePrice w ((FairDivision.bundle A j).erase g) := by
      simp only [FairDivision.additiveValue, Finset.mul_sum, bundlePrice]
      exact Finset.sum_le_sum (fun f _ => I.bid_le_price w i f)
    _ = I.trim w (FairDivision.bundle A j) := hdelete
    _ ≤ τ := hb.2 j
    _ ≤ I.bundlePrice w (FairDivision.bundle A i) := hb.1 i
    _ = w i * I.utility i (FairDivision.bundle A i) := I.supported_bundlePrice w A hA i

/-- Goods assigned to different owners in the two allocations. -/
def disagreement (A C : I.Allocation) : Finset I.Good :=
  Finset.univ.filter (fun g => A g ≠ C g)

/-- A path of transfers toward the covering allocation `C`. The supported
and upper-band conditions hold throughout the path. -/
inductive TransferPath (w : I.Weights) (τ : ℝ) (C : I.Allocation) :
    ℕ → I.Allocation → I.Allocation → Prop where
  | done (A : I.Allocation) (hS : I.IsSupported w A) (hU : I.UpperBand w A τ) :
      TransferPath w τ C 0 A A
  | move {k : ℕ} {A B : I.Allocation} (g : I.Good) (hd : A g ≠ C g)
      (hS : I.IsSupported w A) (hU : I.UpperBand w A τ)
      (tail : TransferPath w τ C k (Function.update A g (C g)) B) :
      TransferPath w τ C (k + 1) A B

theorem transfer_toward_cover (w : I.Weights) (C A : I.Allocation) (τ : ℝ) (i : I.Agent)
    (hw : I.Positive w) (hC : I.IsSupported w C) (hL : I.LowerBand w C τ)
    (hA : I.IsSupported w A) (hU : I.UpperBand w A τ)
    (hi : I.bundlePrice w (FairDivision.bundle A i) < τ) :
    ∃ g : I.Good, C g = i ∧ A g ≠ i ∧
      let A' := Function.update A g (C g)
      I.IsSupported w A' ∧ I.UpperBand w A' τ ∧
        (I.disagreement A' C).card + 1 = (I.disagreement A C).card := by
  have hnotSubset : ¬ FairDivision.bundle C i ⊆ FairDivision.bundle A i := by
    intro hsub
    have hle : I.bundlePrice w (FairDivision.bundle C i) ≤
        I.bundlePrice w (FairDivision.bundle A i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => I.price_nonneg w hw g)
    exact (not_le_of_gt (hi.trans_le (hL i))) hle
  obtain ⟨g, hg⟩ := Finset.sdiff_nonempty.mpr hnotSubset
  obtain ⟨hgC, hgA⟩ := Finset.mem_sdiff.mp hg
  have hcg : C g = i := by simpa [FairDivision.bundle] using hgC
  have hag : A g ≠ i := by simpa [FairDivision.bundle] using hgA
  let A' := Function.update A g (C g)
  refine ⟨g, hcg, hag, ?_⟩
  change I.IsSupported w A' ∧ I.UpperBand w A' τ ∧
    (I.disagreement A' C).card + 1 = (I.disagreement A C).card
  refine ⟨?_, ?_, ?_⟩
  · intro f
    by_cases hf : f = g
    · subst f
      simpa [A'] using hC g
    · simpa [A', Function.update_of_ne hf] using hA f
  · intro j
    by_cases hji : j = i
    · subst j
      have hmember : g ∈ FairDivision.bundle A' i := by simp [FairDivision.bundle, A', hcg]
      have herase : (FairDivision.bundle A' i).erase g = FairDivision.bundle A i := by
        ext f
        by_cases hf : f = g
        · subst f
          simp [FairDivision.bundle, hag]
        · simp [FairDivision.bundle, A', hf]
      have htrim := I.trim_le_delete w (FairDivision.bundle A' i) hmember
      rw [herase] at htrim
      exact htrim.trans hi.le
    · have hsub : FairDivision.bundle A' j ⊆ FairDivision.bundle A j := by
        intro f hf
        by_cases heq : f = g
        · subst f
          exact False.elim (hji (by simpa [FairDivision.bundle, A', hcg, eq_comm] using hf))
        · simpa [FairDivision.bundle, A', Function.update_of_ne heq] using hf
      exact (I.trim_mono w hw hsub).trans (hU j)
  · have herase : I.disagreement A' C = (I.disagreement A C).erase g := by
      ext f
      by_cases hf : f = g
      · subst f
        simp [disagreement, A']
      · simp [disagreement, A', hf]
    rw [herase]
    exact Finset.card_erase_add_one (by simp [disagreement, hcg, hag])

/-- Combine an independently covering allocation and an independently
upper-band allocation by at most one transfer per mismatching good. -/
theorem combine_allocations (w : I.Weights) (C D : I.Allocation) (τ : ℝ)
    (hw : I.Positive w) (_hτ : 0 ≤ τ) (hC : I.IsSupported w C) (hL : I.LowerBand w C τ)
    (hD : I.IsSupported w D) (hU : I.UpperBand w D τ) :
    ∃ (k : ℕ) (A : I.Allocation), k ≤ (I.disagreement D C).card ∧
      I.TransferPath w τ C k D A ∧ I.IsSupported w A ∧ I.Bands w A τ := by
  classical
  have advance (d : ℕ) : ∀ A : I.Allocation, (I.disagreement A C).card = d →
      I.IsSupported w A → I.UpperBand w A τ →
      ∃ (k : ℕ) (B : I.Allocation), k ≤ d ∧ I.TransferPath w τ C k A B ∧
        I.IsSupported w B ∧ I.Bands w B τ := by
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro A hcount hA hupper
      by_cases hlower : I.LowerBand w A τ
      · exact ⟨0, A, Nat.zero_le _, .done A hA hupper, hA, hlower, hupper⟩
      · have hfail : ¬ ∀ i, τ ≤ I.bundlePrice w (FairDivision.bundle A i) := hlower
        obtain ⟨i, hi⟩ := not_forall.mp hfail
        obtain ⟨g, hcg, hag, hstep⟩ :=
          I.transfer_toward_cover w C A τ i hw hC hL hA hupper (lt_of_not_ge hi)
        let A' := Function.update A g (C g)
        have hstep' : I.IsSupported w A' ∧ I.UpperBand w A' τ ∧
            (I.disagreement A' C).card + 1 = (I.disagreement A C).card := hstep
        obtain ⟨hA', hupper', hcard⟩ := hstep'
        have hlt : (I.disagreement A' C).card < d := by omega
        obtain ⟨k, B, hk, hpath, hB, hbands⟩ :=
          ih (I.disagreement A' C).card hlt A' rfl hA' hupper'
        have hmove : A g ≠ C g := fun heq => hag (heq.trans hcg)
        refine ⟨k + 1, B, ?_, .move g hmove hA hupper hpath, hB, hbands⟩
        omega
  exact advance _ D rfl hD hU

/-- In a forest each good with multiple highest bidders can be assigned to a
distinct highest bidder. -/
theorem exists_distinct_shared_owners (w : I.Weights) (hforest : I.IsForest w) :
    ∃ f : {g : I.Good // ∃ i j, i ≠ j ∧ I.IsHighestBidder w i g ∧
        I.IsHighestBidder w j g} → I.Agent,
      Function.Injective f ∧ ∀ g, I.IsHighestBidder w (f g) g := by
  classical
  let V := I.Agent ⊕ I.Good
  let G : SimpleGraph V := I.highestBidderGraph w
  have hG : G.IsAcyclic := hforest
  have hrepr (c : G.ConnectedComponent) : ∃ r, G.connectedComponentMk r = c :=
    Quot.mk_surjective c
  let root (v : V) : V := (hrepr (G.connectedComponentMk v)).choose
  have hroot_adj {u v : V} (h : G.Adj u v) : root u = root v := by
    unfold root
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h]
  have hpath (v : V) : ∃ p : G.Walk (root v) v, p.IsPath :=
    (SimpleGraph.ConnectedComponent.exact (hrepr (G.connectedComponentMk v)).choose_spec).exists_isPath
  let path (v : V) : G.Path (root v) v := ⟨(hpath v).choose, (hpath v).choose_spec⟩
  have adj_of_highest (i : I.Agent) (g : I.Good) (h : I.IsHighestBidder w i g) :
      G.Adj (Sum.inl i) (Sum.inr g) := by
    simpa [G, highestBidderGraph] using h
  let Shared := {g : I.Good // ∃ i j, i ≠ j ∧ I.IsHighestBidder w i g ∧ I.IsHighestBidder w j g}
  have howner (g : Shared) : ∃ i, I.IsHighestBidder w i g ∧
      Sum.inl i ∉ (path (Sum.inr g.val)).val.support := by
    obtain ⟨i, j, hij, hi, hj⟩ := g.property
    by_cases hip : Sum.inl i ∈ (path (Sum.inr g.val)).val.support
    · refine ⟨j, hj, fun hjp => hij (Sum.inl.inj (β := I.Good) ?_)⟩
      have heqi := hG.eq_penultimate_of_adj_end (path (Sum.inr g.val)).property
        (adj_of_highest i g hi).symm hip
      have heqj := hG.eq_penultimate_of_adj_end (path (Sum.inr g.val)).property
        (adj_of_highest j g hj).symm hjp
      exact heqi.trans heqj.symm
    · exact ⟨i, hi, hip⟩
  let owner (g : Shared) : I.Agent := (howner g).choose
  have hparent (g : Shared) :
      (path (Sum.inl (owner g))).val.penultimate = Sum.inr g.val := by
    let p := path (Sum.inr g.val)
    have hg : G.Adj (Sum.inr g.val) (Sum.inl (owner g)) :=
      (adj_of_highest (owner g) g (howner g).choose_spec.1).symm
    let q := p.val.concat hg
    have hq : q.IsPath := p.property.concat (howner g).choose_spec.2 hg
    let q' : G.Path (root (Sum.inl (owner g))) (Sum.inl (owner g)) :=
      ⟨q.copy (hroot_adj hg) rfl, by simpa using hq⟩
    have heq : path (Sum.inl (owner g)) = q' := (hG.subsingleton_path _ _).elim _ _
    rw [heq]
    change (q.copy (hroot_adj hg) rfl).getVert
      ((q.copy (hroot_adj hg) rfl).length - 1) = Sum.inr g.val
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.getVert_copy]
    exact SimpleGraph.Walk.penultimate_concat p.val hg
  refine ⟨owner, ?_, fun g => (howner g).choose_spec.1⟩
  intro g h heq
  have heqParent := congrArg (fun i : I.Agent => (path (Sum.inl i)).val.penultimate) heq
  exact Subtype.ext (Sum.inr.inj ((hparent g).symm.trans (heqParent.trans (hparent h))))

theorem exists_upper_on_forest (w : I.Weights) (hw : I.Positive w)
    (hforest : I.IsForest w) (hforced : I.ForcedFeasible w) :
    ∃ A : I.Allocation, I.IsSupported w A ∧ I.UpperBand w A 1 := by
  classical
  let shared (g : I.Good) : Prop :=
    ∃ i j, i ≠ j ∧ I.IsHighestBidder w i g ∧ I.IsHighestBidder w j g
  obtain ⟨f, hfi, hf⟩ := I.exists_distinct_shared_owners w hforest
  let A : I.Allocation := fun g =>
    if h : shared g then f ⟨g, h⟩ else (I.exists_highest_bidder w g).choose
  have hA : I.IsSupported w A := by
    intro g
    by_cases hg : shared g
    · simp only [A, dite_eq_left hg]
      exact hf ⟨g, hg⟩
    · simp only [A, dite_eq_right hg]
      exact (I.exists_highest_bidder w g).choose_spec
  refine ⟨A, hA, fun i => ?_⟩
  let S := FairDivision.bundle A i
  have eachForced (g : I.Good) (hg : g ∈ S) (hn : ¬ shared g) : g ∈ I.forcedGoods w i := by
    have hai : A g = i := by simpa [S, FairDivision.bundle] using hg
    have hi : I.IsHighestBidder w i g := hai ▸ hA g
    simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hji
    refine lt_of_le_of_ne (hi j) (fun heq => hn ?_)
    have hj : I.IsHighestBidder w j g := fun k => (hi k).trans heq.ge
    exact ⟨j, i, hji, hj, hi⟩
  have hsum {T : Finset I.Good} (hT : T ⊆ I.forcedGoods w i) : I.bundlePrice w T ≤ 1 := by
    have hle : I.bundlePrice w T ≤ I.bundlePrice w (I.forcedGoods w i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun g _ _ => I.price_nonneg w hw g)
    exact hle.trans (hforced i)
  by_cases ht : ∃ g ∈ S, shared g
  · obtain ⟨g, hg, hgshared⟩ := ht
    refine (I.trim_le_delete w S hg).trans (hsum ?_)
    intro k hk
    obtain ⟨hne, hkS⟩ := Finset.mem_erase.mp hk
    refine eachForced k hkS (fun hkshared => ?_)
    have hownerEq : A k = A g := by
      have hkI : A k = i := by simpa [S, FairDivision.bundle] using hkS
      have hgI : A g = i := by simpa [S, FairDivision.bundle] using hg
      exact hkI.trans hgI.symm
    have hfEq : f ⟨k, hkshared⟩ = f ⟨g, hgshared⟩ := by
      simpa only [A, dite_eq_left hkshared, dite_eq_left hgshared] using hownerEq
    exact hne (congrArg Subtype.val (hfi hfEq))
  · by_cases hS : S.Nonempty
    · obtain ⟨g, hg⟩ := hS
      refine (I.trim_le_delete w S hg).trans (hsum (fun k hk => ?_))
      have hkS := Finset.mem_of_mem_erase hk
      exact eachForced k hkS (fun hs => ht ⟨k, hkS, hs⟩)
    · change I.trim w S ≤ 1
      simp [trim, hS]

/-- Semantic rounding guarantee. The computational contract must produce the
lower-band witness by the forest dynamic program. -/
theorem round_on_forest (w : I.Weights) (hw : I.Positive w)
    (hforest : I.IsForest w) (hcover : I.Covers w) (hforced : I.ForcedFeasible w) :
    ∃ A : I.Allocation, I.IsSupported w A ∧ I.Bands w A 1 := by
  obtain ⟨C, hC, hL⟩ := hcover
  obtain ⟨D, hD, hU⟩ := I.exists_upper_on_forest w hw hforest hforced
  obtain ⟨_, A, _, _, hA, hbands⟩ :=
    I.combine_allocations w C D 1 hw zero_le_one hC hL hD hU
  exact ⟨A, hA, hbands⟩

end EF1FPO.Instance
