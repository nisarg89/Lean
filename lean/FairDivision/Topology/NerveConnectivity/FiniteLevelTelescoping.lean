import FairDivision.Topology.NerveConnectivity.BarycentricInverseWeight

/-!
# Finite layer gaps

For a finite set of real coordinate levels, the gaps between each level
and its preceding level sum to the maximum level. This is the finite
layer-cake identity used to normalize barycentric inverse coordinates.
-/

set_option autoImplicit false

open scoped Classical

namespace FairDivision.Topology.NerveConnectivity

/-- The maximum of a finite set of levels, or zero for the empty set. -/
noncomputable def finiteLevelTop (S : Finset ℝ) : ℝ :=
  if hS : S.Nonempty then S.max' hS else 0

/-- The greatest level strictly below `t`, or zero if none exists. -/
noncomputable def finiteLevelPred (S : Finset ℝ) (t : ℝ) : ℝ :=
  finiteLevelTop (S.filter (· < t))

@[simp] theorem finiteLevelTop_empty : finiteLevelTop ∅ = 0 := by
  simp [finiteLevelTop]

/-- Inserting a new strict maximum makes it the top level. -/
theorem finiteLevelTop_insert_max (S : Finset ℝ) (a : ℝ)
    (ha : ∀ t ∈ S, t < a) : finiteLevelTop (insert a S) = a := by
  classical
  have hne : (insert a S).Nonempty := Finset.insert_nonempty _ _
  unfold finiteLevelTop
  rw [dif_pos hne]
  apply (Finset.max'_eq_iff (insert a S) hne a).2
  constructor
  · simp
  · intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact le_refl _
    · exact le_of_lt (ha t ht)

/-- Inserting a new strict maximum leaves all older predecessor levels
unchanged. -/
theorem finiteLevelPred_insert_old (S : Finset ℝ) (a t : ℝ)
    (ha : t < a) :
    finiteLevelPred (insert a S) t = finiteLevelPred S t := by
  classical
  have hat : ¬ a < t := not_lt.mpr ha.le
  simp [finiteLevelPred, Finset.filter_insert, hat]

/-- The predecessor of a newly inserted strict maximum is the old top. -/
theorem finiteLevelPred_insert_max (S : Finset ℝ) (a : ℝ)
    (ha : ∀ t ∈ S, t < a) :
    finiteLevelPred (insert a S) a = finiteLevelTop S := by
  classical
  have hfilter : (insert a S).filter (· < a) = S := by
    simp [Finset.filter_insert, Finset.filter_eq_self.mpr ha]
  simp [finiteLevelPred, hfilter]

/-- Finite level gaps telescope to the greatest level. No sign
assumption on the levels is required. -/
theorem finiteLevelGap_sum_eq_top (S : Finset ℝ) :
    S.sum (fun t => t - finiteLevelPred S t) = finiteLevelTop S := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp [finiteLevelTop]
  | insert a S ha ih =>
    have hnot : a ∉ S := by
      intro hmem
      exact (lt_irrefl a) (ha a hmem)
    rw [Finset.sum_insert hnot]
    rw [finiteLevelPred_insert_max S a ha]
    have hsum : S.sum (fun t => t - finiteLevelPred (insert a S) t) =
        S.sum (fun t => t - finiteLevelPred S t) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [finiteLevelPred_insert_old S a t (ha t ht)]
    rw [hsum, ih, finiteLevelTop_insert_max S a ha]
    ring

/-- The predecessor of a positive level is strictly below that level. -/
theorem finiteLevelPred_lt_of_pos (S : Finset ℝ) (t : ℝ) (ht : 0 < t) :
    finiteLevelPred S t < t := by
  classical
  let T := S.filter (· < t)
  by_cases hT : T.Nonempty
  · change (if h : T.Nonempty then T.max' h else 0) < t
    rw [dif_pos hT]
    apply (Finset.max'_lt_iff T hT).2
    intro u hu
    exact (Finset.mem_filter.mp hu).2
  · change (if h : T.Nonempty then T.max' h else 0) < t
    simp [hT, ht]

/-- Restricting to levels at most `a` does not change the predecessor
of a level `t ≤ a`. -/
theorem finiteLevelPred_filter_le (S : Finset ℝ) (a t : ℝ)
    (hta : t ≤ a) :
    finiteLevelPred (S.filter (· ≤ a)) t = finiteLevelPred S t := by
  classical
  unfold finiteLevelPred
  congr 1
  ext u
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨huS, _⟩, hut⟩
    exact ⟨huS, hut⟩
  · rintro ⟨huS, hut⟩
    exact ⟨⟨huS, (le_of_lt hut).trans hta⟩, hut⟩

/-- An attained level is the maximum of all levels below it. -/
theorem finiteLevelTop_filter_le_eq (S : Finset ℝ) (a : ℝ)
    (ha : a ∈ S) : finiteLevelTop (S.filter (· ≤ a)) = a := by
  classical
  let T := S.filter (· ≤ a)
  have haT : a ∈ T := Finset.mem_filter.mpr ⟨ha, le_refl a⟩
  have hT : T.Nonempty := ⟨a, haT⟩
  unfold finiteLevelTop
  rw [dif_pos hT]
  apply (Finset.max'_eq_iff T hT a).2
  exact ⟨haT, fun t ht => (Finset.mem_filter.mp ht).2⟩

/-- The gaps of all levels at most an attained level `a` sum to `a`. -/
theorem finiteLevelGap_sum_le_eq (S : Finset ℝ) (a : ℝ)
    (ha : a ∈ S) :
    (S.filter (· ≤ a)).sum (fun t => t - finiteLevelPred S t) = a := by
  let T := S.filter (· ≤ a)
  have hsum : T.sum (fun t => t - finiteLevelPred S t) =
      T.sum (fun t => t - finiteLevelPred T t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hta : t ≤ a := (Finset.mem_filter.mp ht).2
    rw [finiteLevelPred_filter_le S a t hta]
  rw [hsum, finiteLevelGap_sum_eq_top, finiteLevelTop_filter_le_eq S a ha]

/-- Zero has predecessor zero when all levels are nonnegative. -/
theorem finiteLevelPred_zero_of_nonneg (S : Finset ℝ)
    (hS : ∀ t ∈ S, 0 ≤ t) : finiteLevelPred S 0 = 0 := by
  have hEmpty : S.filter (· < 0) = ∅ := by
    apply Finset.filter_false_of_mem
    intro t htS
    exact not_lt_of_ge (hS t htS)
  simp [finiteLevelPred, hEmpty, finiteLevelTop]

/-- For nonnegative levels, only positive levels contribute to the gap
sum through an attained level. -/
theorem finitePositiveLevelGap_sum_le_eq (S : Finset ℝ) (a : ℝ)
    (hS : ∀ t ∈ S, 0 ≤ t) (ha : a ∈ S) :
    ((S.filter (0 < ·)).filter (· ≤ a)).sum
      (fun t => t - finiteLevelPred S t) = a := by
  classical
  have hsub : (S.filter (0 < ·)).filter (· ≤ a) ⊆ S.filter (· ≤ a) := by
    intro t ht
    obtain ⟨htPosSet, hta⟩ := Finset.mem_filter.mp ht
    obtain ⟨htS, _⟩ := Finset.mem_filter.mp htPosSet
    exact Finset.mem_filter.mpr ⟨htS, hta⟩
  have hsum : (S.filter (· ≤ a)).sum (fun t => t - finiteLevelPred S t) =
      ((S.filter (0 < ·)).filter (· ≤ a)).sum
        (fun t => t - finiteLevelPred S t) := by
    symm
    apply Finset.sum_subset hsub
    intro t ht hnot
    obtain ⟨htS, _⟩ := Finset.mem_filter.mp ht
    have htnot : ¬ 0 < t := by
      intro htp
      exact hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨htS, htp⟩, (Finset.mem_filter.mp ht).2⟩)
    have ht0 : t = 0 := le_antisymm (le_of_not_gt htnot) (hS t htS)
    subst t
    simp [finiteLevelPred_zero_of_nonneg S hS]
  rw [← hsum]
  exact finiteLevelGap_sum_le_eq S a ha

end FairDivision.Topology.NerveConnectivity
