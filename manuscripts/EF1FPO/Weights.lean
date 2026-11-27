import EF1FPO.Prices

/-! One-agent thresholds and the greatest feasible positive weight vector. -/

set_option autoImplicit false

open scoped BigOperators

namespace EF1FPO.Instance

variable (I : Instance)

def PositiveRow (i : I.Agent) : Prop := ∃ g, 0 < I.value i g

noncomputable def positiveGoods (i : I.Agent) : Finset I.Good := by
  classical
  exact Finset.univ.filter (fun g => 0 < I.value i g)

noncomputable def positiveBundles (i : I.Agent) : Finset (Finset I.Good) :=
  (I.positiveGoods i).powerset.erase ∅

/-- The own weight at which `i` can tie with all rival bids for `g`.
The term for `i` is zero, so this is zero in the absence of any positive rival bid. -/
noncomputable def rivalThreshold (w : I.Weights) (i : I.Agent) (g : I.Good) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ _⟩
    (fun j => if j = i then 0 else I.bid w j g / I.value i g)

/-- The finite minimum over nonempty bundles of positively valued goods in
equation (5). If there is no such bundle the threshold contracts do not apply. -/
noncomputable def threshold (w : I.Weights) (i : I.Agent) : ℝ := by
  classical
  exact if h : (I.positiveBundles i).Nonempty then
    (I.positiveBundles i).inf' h (fun S =>
      max (I.utility i S)⁻¹ (if hS : S.Nonempty then S.sup' hS (I.rivalThreshold w i) else 0))
    else 0

theorem threshold_pos (w : I.Weights) (i : I.Agent) (hi : I.PositiveRow i) :
    0 < I.threshold w i := by
  classical
  obtain ⟨g, hg⟩ := hi
  have hg' : g ∈ I.positiveGoods i := by
    simp [positiveGoods]
    exact_mod_cast hg
  have hne : (I.positiveBundles i).Nonempty := by
    refine ⟨{g}, Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty _, ?_⟩⟩
    exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hg')
  rw [threshold, dite_eq_left hne, Finset.lt_inf'_iff]
  intro S hS
  obtain ⟨hneS, hsub⟩ := Finset.mem_erase.mp hS
  have hSpos : 0 < I.utility i S := by
    apply Finset.sum_pos _ (Finset.nonempty_iff_ne_empty.mpr hneS)
    intro f hf
    have hgood := Finset.mem_powerset.mp hsub hf
    simpa [positiveGoods] using hgood
  exact (inv_pos.mpr hSpos).trans_le (le_max_left _ _)

private theorem mem_positiveBundles_iff (i : I.Agent) (S : Finset I.Good) :
    S ∈ I.positiveBundles i ↔ S.Nonempty ∧ ∀ g ∈ S, 0 < I.value i g := by
  classical
  rw [positiveBundles, Finset.mem_erase, Finset.mem_powerset, ← Finset.nonempty_iff_ne_empty]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h g hg
    simpa [positiveGoods] using h hg
  · intro h g hg
    have hg' := h g hg
    simpa [positiveGoods] using hg'

private theorem exists_positiveBundle (i : I.Agent) (hi : I.PositiveRow i) :
    (I.positiveBundles i).Nonempty := by
  obtain ⟨g, hg⟩ := hi
  refine ⟨{g}, (I.mem_positiveBundles_iff i {g}).2 ⟨Finset.singleton_nonempty _, ?_⟩⟩
  intro k hk
  rw [Finset.mem_singleton.mp hk]
  exact hg

private noncomputable def thresholdTerm (w : I.Weights) (i : I.Agent) (S : Finset I.Good) : ℝ := by
  classical
  exact max (I.utility i S)⁻¹ (if hS : S.Nonempty then S.sup' hS (I.rivalThreshold w i) else 0)

private theorem threshold_le_term (w : I.Weights) (i : I.Agent) (S : Finset I.Good)
    (hS : S ∈ I.positiveBundles i) : I.threshold w i ≤ I.thresholdTerm w i S := by
  have hne : (I.positiveBundles i).Nonempty := ⟨S, hS⟩
  rw [threshold, dite_eq_left hne]
  exact Finset.inf'_le (I.thresholdTerm w i) hS

private theorem exists_threshold_term (w : I.Weights) (i : I.Agent) (hi : I.PositiveRow i) :
    ∃ S ∈ I.positiveBundles i, I.threshold w i = I.thresholdTerm w i S := by
  have hne := I.exists_positiveBundle i hi
  rw [threshold, dite_eq_left hne]
  exact Finset.exists_mem_eq_inf' hne (I.thresholdTerm w i)

private theorem highest_update_iff (w : I.Weights) (i : I.Agent) (g : I.Good) (t : ℝ)
    (ht : 0 ≤ t) (hg : 0 < I.value i g) :
    I.IsHighestBidder (Function.update w i t) i g ↔ I.rivalThreshold w i g ≤ t := by
  constructor
  · intro h
    unfold rivalThreshold
    refine Finset.sup'_le _ _ (fun j _ => ?_)
    by_cases hj : j = i
    · simp [hj, ht]
    · simp only [hj, ite_false]
      apply (div_le_iff₀ hg).2
      simpa only [bid, Function.update_self, Function.update_of_ne hj] using h j
  · intro h j
    by_cases hj : j = i
    · subst j
      exact le_rfl
    · have hquot := (Finset.le_sup'
          (fun k => if k = i then 0 else I.bid w k g / I.value i g)
          (Finset.mem_univ j)).trans h
      simp only [hj, ite_false] at hquot
      have hbid := (div_le_iff₀ hg).1 hquot
      simpa only [bid, Function.update_self, Function.update_of_ne hj] using hbid

private theorem utility_pos_of_positiveBundle (i : I.Agent) (S : Finset I.Good)
    (hS : S ∈ I.positiveBundles i) : 0 < I.utility i S := by
  obtain ⟨hne, hval⟩ := (I.mem_positiveBundles_iff i S).1 hS
  exact Finset.sum_pos hval hne

private theorem utility_inter_positiveGoods (i : I.Agent) (S : Finset I.Good) :
    I.utility i (S ∩ I.positiveGoods i) = I.utility i S := by
  apply Finset.sum_subset Finset.inter_subset_left
  intro g hg hgs
  have hnot : ¬ 0 < I.value i g := fun hpos =>
    hgs (Finset.mem_inter.mpr ⟨hg, by simpa [positiveGoods] using hpos⟩)
  have hv : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
  exact le_antisymm (le_of_not_gt hnot) hv

/-- An attained minimum with rival weights fixed and own weight still positive. -/
theorem threshold_isLeast_covering (w : I.Weights) (i : I.Agent)
    (hw : I.Positive w) (hi : I.PositiveRow i) :
    IsLeast {t : ℝ | 0 < t ∧ ∃ A : I.Allocation,
      I.IsSupported (Function.update w i t) A ∧
        1 ≤ I.bundlePrice (Function.update w i t) (FairDivision.bundle A i)}
      (I.threshold w i) := by
  classical
  let b := I.threshold w i
  have hb : 0 < b := I.threshold_pos w i hi
  constructor
  · obtain ⟨S, hS, hbEq⟩ := I.exists_threshold_term w i hi
    have hbEq' : b = I.thresholdTerm w i S := hbEq
    obtain ⟨hne, hval⟩ := (I.mem_positiveBundles_iff i S).1 hS
    rw [thresholdTerm, dite_eq_left hne] at hbEq'
    let u := Function.update w i b
    have hsuppS (g : I.Good) (hg : g ∈ S) : I.IsHighestBidder u i g := by
      apply (I.highest_update_iff w i g b hb.le (hval g hg)).2
      rw [hbEq']
      exact (Finset.le_sup' (I.rivalThreshold w i) hg).trans (le_max_right _ _)
    let A : I.Allocation := fun g => if g ∈ S then i else (I.exists_highest_bidder u g).choose
    have hA : I.IsSupported u A := by
      intro g
      by_cases hg : g ∈ S
      · simpa [A, hg] using hsuppS g hg
      · simpa [A, hg] using (I.exists_highest_bidder u g).choose_spec
    have hsub : S ⊆ FairDivision.bundle A i := by
      intro g hg
      simp [FairDivision.bundle, A, hg]
    have hvalue : I.utility i S ≤ I.utility i (FairDivision.bundle A i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by exact_mod_cast I.nonneg i g)
    refine ⟨hb, A, hA, ?_⟩
    change 1 ≤ I.bundlePrice u (FairDivision.bundle A i)
    rw [I.supported_bundlePrice u A hA i]
    have hinv : (I.utility i S)⁻¹ ≤ b := by rw [hbEq']; exact le_max_left _ _
    have hbSpend : 1 ≤ b * I.utility i S :=
      (inv_le_iff_one_le_mul₀ (I.utility_pos_of_positiveBundle i S hS)).1 hinv
    simpa [u] using hbSpend.trans (mul_le_mul_of_nonneg_left hvalue hb.le)
  · rintro t ⟨ht, A, hA, hSpend⟩
    let S := FairDivision.bundle A i ∩ I.positiveGoods i
    have huse : I.utility i S = I.utility i (FairDivision.bundle A i) :=
      I.utility_inter_positiveGoods i _
    rw [I.supported_bundlePrice (Function.update w i t) A hA i, Function.update_self, ← huse]
      at hSpend
    have hpos : 0 < I.utility i S := pos_of_mul_pos_right (zero_lt_one.trans_le hSpend) ht.le
    have hne : S.Nonempty := by
      by_contra hn
      have hSempty := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hSempty, FairDivision.additiveValue] at hpos
    have hval (g : I.Good) (hg : g ∈ S) : 0 < I.value i g := by
      have hgood := (Finset.mem_inter.mp hg).2
      simpa [positiveGoods] using hgood
    have hS : S ∈ I.positiveBundles i := (I.mem_positiveBundles_iff i S).2 ⟨hne, hval⟩
    apply (I.threshold_le_term w i S hS).trans
    rw [thresholdTerm, dite_eq_left hne]
    apply max_le ((inv_le_iff_one_le_mul₀ hpos).2 hSpend)
    refine Finset.sup'_le _ _ (fun g hg => ?_)
    have howner : A g = i := by simpa [FairDivision.bundle] using (Finset.mem_inter.mp hg).1
    exact (I.highest_update_iff w i g t ht.le (hval g hg)).1 (howner ▸ hA g)

private theorem forced_bundlePrice (w : I.Weights) (i : I.Agent) :
    I.bundlePrice w (I.forcedGoods w i) = w i * I.utility i (I.forcedGoods w i) := by
  simp only [bundlePrice, FairDivision.additiveValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hstrict : ∀ j, j ≠ i → I.bid w j g < I.bid w i g := by
    simpa [forcedGoods] using hg
  have hi : I.IsHighestBidder w i g := fun j => by
    by_cases hji : j = i
    · simp [hji]
    · exact (hstrict j hji).le
  exact ((I.highest_bidder_iff_bid_eq_price w i g).mp hi).symm

theorem forced_spending_le_one_iff (w : I.Weights) (i : I.Agent)
    (hw : I.Positive w) (hi : I.PositiveRow i) :
    I.bundlePrice w (I.forcedGoods w i) ≤ 1 ↔ w i ≤ I.threshold w i := by
  classical
  rw [I.forced_bundlePrice w i]
  constructor
  · intro hforce
    by_contra hnot
    have hb_lt : I.threshold w i < w i := lt_of_not_ge hnot
    obtain ⟨S, hS, hbeq⟩ := I.exists_threshold_term w i hi
    obtain ⟨hne, hvalued⟩ := (I.mem_positiveBundles_iff i S).1 hS
    have hUpos := I.utility_pos_of_positiveBundle i S hS
    rw [thresholdTerm, dite_eq_left hne] at hbeq
    have hsub : S ⊆ I.forcedGoods w i := by
      intro g hg
      have hgR : I.rivalThreshold w i g ≤ I.threshold w i := by
        rw [hbeq]
        exact (Finset.le_sup' (I.rivalThreshold w i) hg).trans (le_max_right _ _)
      simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj
      have hJ : I.bid w j g / I.value i g ≤ I.rivalThreshold w i g := by
        unfold rivalThreshold
        simpa only [hj, ite_false] using
          (Finset.le_sup' (fun k => if k = i then 0 else I.bid w k g / I.value i g)
            (Finset.mem_univ j))
      exact (div_lt_iff₀ (hvalued g hg)).1 ((hJ.trans hgR).trans_lt hb_lt)
    have hinv : (I.utility i S)⁻¹ ≤ I.threshold w i := by rw [hbeq]; exact le_max_left _ _
    have hbelow : 1 ≤ I.threshold w i * I.utility i S :=
      (inv_le_iff_one_le_mul₀ hUpos).1 hinv
    have habove : 1 < w i * I.utility i S :=
      hbelow.trans_lt (mul_lt_mul_of_pos_right hb_lt hUpos)
    have hu_le : I.utility i S ≤ I.utility i (I.forcedGoods w i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by exact_mod_cast I.nonneg i g)
    exact not_le_of_gt (habove.trans_le (mul_le_mul_of_nonneg_left hu_le (hw i).le)) hforce
  · intro hb
    by_contra hfail
    let S := I.forcedGoods w i ∩ I.positiveGoods i
    have hu_eq : I.utility i S = I.utility i (I.forcedGoods w i) := I.utility_inter_positiveGoods i _
    have hSpend : 1 < w i * I.utility i S := by rw [hu_eq]; exact lt_of_not_ge hfail
    have hpos : 0 < I.utility i S := pos_of_mul_pos_right (zero_lt_one.trans hSpend) (hw i).le
    have hne : S.Nonempty := by
      by_contra hn
      have hSempty := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hSempty, FairDivision.additiveValue] at hpos
    have hvalued (g : I.Good) (hg : g ∈ S) : 0 < I.value i g := by
      have hgood := (Finset.mem_inter.mp hg).2
      simpa [positiveGoods] using hgood
    have hS : S ∈ I.positiveBundles i := (I.mem_positiveBundles_iff i S).2 ⟨hne, hvalued⟩
    have hc_lt : I.thresholdTerm w i S < w i := by
      rw [thresholdTerm, dite_eq_left hne]
      apply max_lt ((inv_lt_iff_one_lt_mul₀ hpos).2 hSpend)
      rw [Finset.sup'_lt_iff]
      intro g hg
      have hgF : g ∈ I.forcedGoods w i := (Finset.mem_inter.mp hg).1
      have hstrict : ∀ j, j ≠ i → I.bid w j g < I.bid w i g := by
        simpa [forcedGoods] using hgF
      unfold rivalThreshold
      refine (Finset.sup'_lt_iff (show (Finset.univ : Finset I.Agent).Nonempty from
        ⟨i, Finset.mem_univ i⟩)).2 ?_
      intro j _
      by_cases hj : j = i
      · simpa [hj] using hw i
      · simp only [hj, ite_false]
        exact (div_lt_iff₀ (hvalued g hg)).2 (hstrict j hj)
    exact not_le_of_gt ((I.threshold_le_term w i S hS).trans_lt hc_lt) hb

theorem threshold_monotone (i : I.Agent) : Monotone (fun w => I.threshold w i) := by
  classical
  intro x y hxy
  have hr (g : I.Good) : I.rivalThreshold x i g ≤ I.rivalThreshold y i g := by
    unfold rivalThreshold
    apply Finset.sup'_mono_fun
    intro j _
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ite_false, bid]
      have hj : 0 ≤ I.value j g := by exact_mod_cast I.nonneg j g
      have hi : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hxy j) hj) hi
  by_cases hne : (I.positiveBundles i).Nonempty
  · simp only [threshold, dite_eq_left hne]
    apply Finset.inf'_mono_fun
    intro S _
    apply max_le_max le_rfl
    by_cases hS : S.Nonempty
    · simp only [dite_eq_left hS]
      exact Finset.sup'_mono_fun (fun g _ => hr g)
    · simp [hS]
  · simp [threshold, hne]

theorem threshold_continuous (i : I.Agent) : Continuous (fun w => I.threshold w i) := by
  classical
  have hr (g : I.Good) : Continuous (fun w => I.rivalThreshold w i g) := by
    unfold rivalThreshold
    refine Continuous.finset_sup'_apply _ (fun j _ => ?_)
    by_cases hji : j = i
    · simp only [hji, ite_true]
      exact continuous_const
    · simp only [hji, ite_false, bid]
      exact ((continuous_apply j).mul continuous_const).div_const _
  by_cases hne : (I.positiveBundles i).Nonempty
  · simp only [threshold, dite_eq_left hne]
    refine Continuous.finset_inf'_apply hne (fun S _ => continuous_const.max ?_)
    by_cases hS : S.Nonempty
    · simp only [dite_eq_left hS]
      exact Continuous.finset_sup'_apply hS (fun g _ => hr g)
    · simpa only [dite_eq_right hS] using
        (continuous_const : Continuous (fun _ : I.Weights => (0 : ℝ)))
  · simpa only [threshold, dite_eq_right hne] using
      (continuous_const : Continuous (fun _ : I.Weights => (0 : ℝ)))

private theorem continuous_bid (i : I.Agent) (g : I.Good) :
    Continuous (fun w => I.bid w i g) := by
  unfold bid
  exact (continuous_apply i).mul continuous_const

private theorem continuous_bundlePrice (S : Finset I.Good) :
    Continuous (fun w => I.bundlePrice w S) := by
  unfold bundlePrice
  refine continuous_finsetSum S (fun g _ => ?_)
  unfold price
  exact Continuous.finset_sup'_apply _ (fun i _ => I.continuous_bid i g)

theorem isClosed_nonneg_forcedFeasible :
    IsClosed {w : I.Weights | (∀ i, 0 ≤ w i) ∧ I.ForcedFeasible w} := by
  let K (i : I.Agent) (S : Finset I.Good) : Set I.Weights :=
    {w | I.bundlePrice w S ≤ 1} ∪
      ⋃ g : S, ⋃ j : {j : I.Agent // j ≠ i}, {w | I.bid w i g ≤ I.bid w j g}
  have hK (i : I.Agent) (S : Finset I.Good) : IsClosed (K i S) := by
    apply IsClosed.union (isClosed_le (I.continuous_bundlePrice S) continuous_const)
    refine isClosed_iUnion_of_finite (fun g => isClosed_iUnion_of_finite (fun j => ?_))
    exact isClosed_le (I.continuous_bid i g) (I.continuous_bid j g)
  let N : Set I.Weights := {w | ∀ i, 0 ≤ w i}
  have hN : IsClosed N := by
    unfold N
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : {w : I.Weights | (∀ i, 0 ≤ w i) ∧ I.ForcedFeasible w} =
      N ∩ ⋂ i, ⋂ S, K i S := by
    ext w
    simp only [N, K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_iUnion]
    refine and_congr_right (fun hw => ?_)
    constructor
    · intro h i S
      by_cases hbad : ∃ (g : S) (j : {j : I.Agent // j ≠ i}), I.bid w i g ≤ I.bid w j g
      · exact Or.inr hbad
      · refine Or.inl ((Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (h i))
        · intro g hg
          simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
          exact fun j hj => lt_of_not_ge (fun hle => hbad ⟨⟨g, hg⟩, ⟨j, hj⟩, hle⟩)
        · intro g _ _
          let j : I.Agent := ⟨0, I.hn⟩
          have hv : 0 ≤ I.value j g := by exact_mod_cast I.nonneg j g
          exact (mul_nonneg (hw j) hv).trans (I.bid_le_price w j g)
    · intro h i
      rcases h i (I.forcedGoods w i) with hb | ⟨g, j, hle⟩
      · exact hb
      · have hstrict : ∀ k, k ≠ i → I.bid w k g < I.bid w i g := by
          simpa [forcedGoods] using g.property
        exact (not_le_of_gt (hstrict j j.property) hle).elim
  rw [heq]
  exact hN.inter (isClosed_iInter (fun i => isClosed_iInter (hK i)))

theorem isClosed_covers : IsClosed {w : I.Weights | I.Covers w} := by
  unfold Covers
  rw [Set.ofPred_exists]
  refine isClosed_iUnion_of_finite (fun A => ?_)
  rw [Set.ofPred_and]
  apply IsClosed.inter
  · change IsClosed {w : I.Weights | ∀ g j, I.bid w j g ≤ I.bid w (A g) g}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun g => isClosed_iInter (fun j =>
      isClosed_le (I.continuous_bid j g) (I.continuous_bid (A g) g)))
  · change IsClosed {w : I.Weights | ∀ i, 1 ≤ I.bundlePrice w (FairDivision.bundle A i)}
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const
      (I.continuous_bundlePrice (FairDivision.bundle A i)))

theorem exists_feasible (u : I.Weights) (hu : I.Positive u) :
    ∃ w, I.IsFeasible u w := by
  let b : ℝ := (∑ i, I.utility i Finset.univ) + 1
  have hnonneg (i : I.Agent) (g : I.Good) : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
  have hsum_nonneg (i : I.Agent) (S : Finset I.Good) : 0 ≤ I.utility i S :=
    Finset.sum_nonneg (fun g _ => hnonneg i g)
  have hb : 0 < b := by
    dsimp [b]
    have hsum : 0 ≤ ∑ i, I.utility i Finset.univ :=
      Finset.sum_nonneg (fun i _ => hsum_nonneg i _)
    linarith
  let w : I.Weights := fun i => min (u i) b⁻¹
  have hw : I.Positive w := fun i => lt_min (hu i) (inv_pos.mpr hb)
  refine ⟨w, hw, fun i => min_le_left _ _, fun i => ?_⟩
  rw [I.forced_bundlePrice w i]
  have hsize : I.utility i (I.forcedGoods w i) ≤ b := by
    calc
      _ ≤ I.utility i Finset.univ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hnonneg i g)
      _ ≤ ∑ j, I.utility j Finset.univ :=
        Finset.single_le_sum (fun j _ => hsum_nonneg j _) (Finset.mem_univ i)
      _ ≤ b := by dsimp [b]; linarith
  calc
    _ ≤ b⁻¹ * b := mul_le_mul (min_le_right _ _) hsize (hsum_nonneg i _) (inv_nonneg.mpr hb.le)
    _ = 1 := inv_mul_cancel₀ hb.ne'

theorem isFeasible_sup (u a b : I.Weights)
    (ha : I.IsFeasible u a) (hb : I.IsFeasible u b) : I.IsFeasible u (a ⊔ b) := by
  let y := a ⊔ b
  have hay : a ≤ y := le_sup_left
  have hby : b ≤ y := le_sup_right
  have hy : I.Positive y := fun i => (ha.1 i).trans_le (hay i)
  refine ⟨hy, sup_le ha.2.1 hb.2.1, fun i => ?_⟩
  change I.bundlePrice y (I.forcedGoods y i) ≤ 1
  rw [I.forced_bundlePrice y i]
  have compare (w : I.Weights) (hw : I.IsFeasible u w) (hwy : w ≤ y) (heq : y i = w i) :
      y i * I.utility i (I.forcedGoods y i) ≤ 1 := by
    have hsub : I.forcedGoods y i ⊆ I.forcedGoods w i := by
      intro g hg
      have hg' : ∀ j, j ≠ i → I.bid y j g < I.bid y i g := by simpa [forcedGoods] using hg
      simp only [forcedGoods, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hji
      have hv : 0 ≤ I.value j g := by exact_mod_cast I.nonneg j g
      have hbLe : I.bid w j g ≤ I.bid y j g := mul_le_mul_of_nonneg_right (hwy j) hv
      simpa only [bid, heq] using hbLe.trans_lt (hg' j hji)
    calc
      y i * I.utility i (I.forcedGoods y i) ≤ w i * I.utility i (I.forcedGoods w i) := by
        rw [heq]
        apply mul_le_mul_of_nonneg_left _ (hw.1 i).le
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by
          exact_mod_cast I.nonneg i g)
      _ = I.bundlePrice w (I.forcedGoods w i) := (I.forced_bundlePrice w i).symm
      _ ≤ 1 := hw.2.2 i
  by_cases hab : a i ≤ b i
  · exact compare b hb hby (max_eq_right hab)
  · exact compare a ha hay (max_eq_left (le_of_not_ge hab))

theorem cover_positiveRow (w : I.Weights) (_hw : I.Positive w) (hcover : I.Covers w)
    (i : I.Agent) : I.PositiveRow i := by
  obtain ⟨A, hA, hband⟩ := hcover
  by_contra hnot
  have hzero (g : I.Good) : I.value i g = 0 := by
    have hnonneg : 0 ≤ I.value i g := by exact_mod_cast I.nonneg i g
    exact le_antisymm (le_of_not_gt (fun hg => hnot ⟨g, hg⟩)) hnonneg
  have hspend := hband i
  rw [I.supported_bundlePrice w A hA i] at hspend
  norm_num [FairDivision.additiveValue, hzero] at hspend

theorem decrease_cover_of_not_forcedFeasible (u y w : I.Weights)
    (hy : I.IsFeasible u y) (hyw : y ≤ w) (_hwu : w ≤ u)
    (hcover : I.Covers w) (hfail : ¬ I.ForcedFeasible w) :
    ∃ w', y ≤ w' ∧ w' ≤ w ∧ w' ≠ w ∧ I.Covers w' := by
  classical
  have hw : I.Positive w := fun j => (hy.1 j).trans_le (hyw j)
  have hf : ¬ ∀ i, I.bundlePrice w (I.forcedGoods w i) ≤ 1 := hfail
  obtain ⟨i, hi⟩ := not_forall.mp hf
  have hrow := I.cover_positiveRow w hw hcover i
  let b := I.threshold w i
  have hb : 0 < b := I.threshold_pos w i hrow
  have hwi : b < w i := by
    apply lt_of_not_ge
    intro hle
    exact hi ((I.forced_spending_le_one_iff w i hw hrow).2 hle)
  have hyi : y i ≤ b := by
    have hyBound := (I.forced_spending_le_one_iff y i hy.1 hrow).1 (hy.2.2 i)
    exact hyBound.trans (I.threshold_monotone i hyw)
  let w' := Function.update w i b
  have hself : w' i = b := by simp [w']
  have hsame (j : I.Agent) (hji : j ≠ i) : w' j = w j := Function.update_of_ne hji b w
  have hy' : y ≤ w' := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [hself] using hyi
    · simpa only [hsame j hji] using hyw j
  have h'w : w' ≤ w := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [hself] using hwi.le
    · rw [hsame j hji]
  have hne : w' ≠ w := by
    intro hwEq
    have hba : b = w i := hself.symm.trans (congrFun hwEq i)
    exact hwi.ne hba
  obtain ⟨A, hA, hAlower⟩ := hcover
  obtain ⟨_, D, hD, hDspend⟩ := (I.threshold_isLeast_covering w i hw hrow).1
  let E : I.Allocation := fun g => if A g = i then D g else A g
  have hE : I.IsSupported w' E := by
    intro g
    by_cases hgi : A g = i
    · simpa only [E, hgi, ite_true] using hD g
    · have hf : E g = A g := by simp [E, hgi]
      intro j
      have hv : 0 ≤ I.value j g := by exact_mod_cast I.nonneg j g
      rw [hf]
      calc
        I.bid w' j g ≤ I.bid w j g := mul_le_mul_of_nonneg_right (h'w j) hv
        _ ≤ I.bid w (A g) g := hA g j
        _ = I.bid w' (A g) g := by simp only [bid, hsame (A g) hgi]
  have htransfer (g : I.Good) (hg : D g = i) (hv : 0 < I.value i g) : A g = i := by
    by_contra hgi
    have hkeep : I.bid w' (A g) g = I.bid w (A g) g := by simp only [bid, hsame (A g) hgi]
    have hwon : I.bid w' (A g) g ≤ I.bid w' i g := hg ▸ hD g (A g)
    have hbetter : I.bid w' i g < I.bid w i g := by
      simp only [bid, hself]
      exact mul_lt_mul_of_pos_right hwi hv
    rw [hkeep] at hwon
    exact not_lt_of_ge (hA g i) (hwon.trans_lt hbetter)
  refine ⟨w', hy', h'w, hne, E, hE, fun j => ?_⟩
  rw [I.supported_bundlePrice w' E hE j]
  have hpos' : 0 ≤ w' j := ((hy.1 j).trans_le (hy' j)).le
  by_cases hji : j = i
  · subst j
    let S := FairDivision.bundle D i ∩ I.positiveGoods i
    have hsub : S ⊆ FairDivision.bundle E i := by
      intro g hg
      obtain ⟨hgD, hgval⟩ := Finset.mem_inter.mp hg
      have hgD' : D g = i := by simpa [FairDivision.bundle] using hgD
      have hv : 0 < I.value i g := by simpa [positiveGoods] using hgval
      have hgA : A g = i := htransfer g hgD' hv
      simp [FairDivision.bundle, E, hgA, hgD']
    have hu_eq : I.utility i S = I.utility i (FairDivision.bundle D i) :=
      I.utility_inter_positiveGoods i _
    have hdu : I.utility i S ≤ I.utility i (FairDivision.bundle E i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by exact_mod_cast I.nonneg i g)
    have hspend : 1 ≤ I.bundlePrice w' (FairDivision.bundle D i) := hDspend
    rw [I.supported_bundlePrice w' D hD i, ← hu_eq] at hspend
    exact hspend.trans (mul_le_mul_of_nonneg_left hdu hpos')
  · have hsub : FairDivision.bundle A j ⊆ FairDivision.bundle E j := by
      intro g hg
      have hgA : A g = j := by simpa [FairDivision.bundle] using hg
      simp [FairDivision.bundle, E, hgA, hji]
    have hu : I.utility j (FairDivision.bundle A j) ≤ I.utility j (FairDivision.bundle E j) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by exact_mod_cast I.nonneg j g)
    have hspend := hAlower j
    rw [I.supported_bundlePrice w A hA j, ← hsame j hji] at hspend
    exact hspend.trans (mul_le_mul_of_nonneg_left hu hpos')

/-- The greatest feasible weights exist below a positive covering cap, and
admit one integral allocation covering every agent simultaneously. -/
theorem greatest_weights (u : I.Weights) (hu : I.Positive u) (hcover : I.Covers u) :
    ∃ w, I.IsGreatestFeasible u w ∧ I.Covers w ∧
      ∀ i, w i = min (u i) (I.threshold w i) := by
  classical
  obtain ⟨a, ha⟩ := I.exists_feasible u hu
  let total (w : I.Weights) : ℝ := ∑ i, w i
  have htotal : Continuous total := continuous_finsetSum _ (fun i _ => continuous_apply i)
  have strictly {p q : I.Weights} (h : p ≤ q) (hne : p ≠ q) : total p < total q := by
    have hnot : ¬ ∀ i, q i ≤ p i := fun h' => hne (le_antisymm h h')
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ i, lt_of_not_ge hi⟩
  let feasible : Set I.Weights := Set.Icc a u ∩
    {w | (∀ i, 0 ≤ w i) ∧ I.ForcedFeasible w}
  have hcompact : IsCompact feasible := isCompact_Icc.inter_right I.isClosed_nonneg_forcedFeasible
  have haMem : a ∈ feasible := ⟨⟨le_rfl, ha.2.1⟩, (fun i => (ha.1 i).le), ha.2.2⟩
  obtain ⟨Y, hYMem, hYmax⟩ := hcompact.exists_isMaxOn ⟨a, haMem⟩ htotal.continuousOn
  have hY : I.IsFeasible u Y :=
    ⟨fun i => (ha.1 i).trans_le (hYMem.1.1 i), hYMem.1.2, hYMem.2.2⟩
  have greatest (w : I.Weights) (hw : I.IsFeasible u w) : w ≤ Y := by
    by_contra hnot
    let b := Y ⊔ w
    have hb : I.IsFeasible u b := I.isFeasible_sup u Y w hY hw
    have hYb : Y ≤ b := le_sup_left
    have hneq : Y ≠ b := fun hEq => hnot (le_sup_right.trans hEq.ge)
    have hbMem : b ∈ feasible :=
      ⟨⟨hYMem.1.1.trans hYb, hb.2.1⟩, (fun i => (hb.1 i).le), hb.2.2⟩
    exact not_le_of_gt (strictly hYb hneq) (isMaxOn_iff.mp hYmax b hbMem)
  let covers : Set I.Weights := Set.Icc Y u ∩ {w | I.Covers w}
  have hcompactCover : IsCompact covers := isCompact_Icc.inter_right I.isClosed_covers
  have huMem : u ∈ covers := ⟨⟨hY.2.1, le_rfl⟩, hcover⟩
  obtain ⟨z, hzMem, hzMin⟩ := hcompactCover.exists_isMinOn ⟨u, huMem⟩ htotal.continuousOn
  have hzpos : I.Positive z := fun i => (hY.1 i).trans_le (hzMem.1.1 i)
  have hzForced : I.ForcedFeasible z := by
    by_contra hfail
    obtain ⟨z', hYz', hz'z, hne, hc⟩ :=
      I.decrease_cover_of_not_forcedFeasible u Y z hY hzMem.1.1 hzMem.1.2 hzMem.2 hfail
    have hz'Mem : z' ∈ covers := ⟨⟨hYz', hz'z.trans hzMem.1.2⟩, hc⟩
    exact not_le_of_gt (strictly hz'z hne) (isMinOn_iff.mp hzMin z' hz'Mem)
  have hzEq : z = Y := le_antisymm (greatest z ⟨hzpos, hzMem.1.2, hzForced⟩) hzMem.1.1
  have hcoverY : I.Covers Y := hzEq ▸ hzMem.2
  refine ⟨Y, ⟨hY, fun w hw => greatest w hw⟩, hcoverY, ?_⟩
  let T : I.Weights := fun i => min (u i) (I.threshold Y i)
  have hrow (i : I.Agent) : I.PositiveRow i := I.cover_positiveRow Y hY.1 hcoverY i
  have hYT : Y ≤ T := fun i => le_min (hY.2.1 i)
    ((I.forced_spending_le_one_iff Y i hY.1 (hrow i)).1 (hY.2.2 i))
  have hTpos : I.Positive T := fun i => (hY.1 i).trans_le (hYT i)
  have hT : I.IsFeasible u T := by
    refine ⟨hTpos, fun i => min_le_left _ _, fun i => ?_⟩
    apply (I.forced_spending_le_one_iff T i hTpos (hrow i)).2
    exact (min_le_right _ _).trans (I.threshold_monotone i hYT)
  exact fun i => congrFun (le_antisymm hYT (greatest T hT)) i

end EF1FPO.Instance
