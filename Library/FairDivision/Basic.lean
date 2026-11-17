import FairDivision.Definitions

/-!
# Finite bridges for the existence certificates

These lemmas are proved from the reviewed statement definitions. They do not
add a separate human statement-review obligation.
-/

set_option autoImplicit false

namespace FairDivision

@[simp] theorem canDeleteOne_empty {m : ℕ} (B : Finset (Fin m)) :
    CanDeleteOne ∅ B := by
  simp [CanDeleteOne]

/-- The common-threshold property implies EF[1,1] for identical valuations. -/
theorem hasCommonThreshold_implies_ef11 {n m : ℕ}
    (v : Finset (Fin m) → ℝ) (A : Allocation n m) (t : ℝ)
    (h : HasCommonThreshold v A t) : IsEF11 (fun _ => v) A := by
  intro i j
  obtain ⟨_, ⟨C, hC, hCi⟩⟩ := h i
  obtain ⟨⟨G, hG, hGj⟩, _⟩ := h j
  exact ⟨C, G, hC, hG, le_trans hGj hCi⟩

/-- With one agent, every item belongs to its only bundle. -/
@[simp] theorem bundle_one (m : ℕ) (A : Allocation 1 m) (i : Fin 1) :
    bundle A i = Finset.univ := by
  ext g
  simp [bundle, Subsingleton.elim (A g) i]

/-- The unique one-agent allocation is balanced. -/
theorem isBalanced_one (m : ℕ) (A : Allocation 1 m) : IsBalanced A := by
  intro i
  left
  simpa using congrArg Finset.card (bundle_one m A i)

/-- The common-threshold theorem holds directly for one agent. -/
theorem identical_one (m : ℕ) (v : Finset (Fin m) → ℝ) :
    ∃ (A : Allocation 1 m) (t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t := by
  let A : Allocation 1 m := fun _ => 0
  refine ⟨A, v Finset.univ, isBalanced_one m A, ?_⟩
  intro i
  refine ⟨⟨∅, canDeleteOne_empty _, ?_⟩,
    ⟨∅, canDeleteOne_empty _, ?_⟩⟩
  · simp
  · simp

/-- With no items, all bundles are empty. -/
@[simp] theorem bundle_zero {n : ℕ} (A : Allocation n 0) (i : Fin n) :
    bundle A i = ∅ := by
  simp [bundle]

/-- Every empty-item allocation is balanced for a positive agent count. -/
theorem isBalanced_zero {n : ℕ} (hn : 0 < n) (A : Allocation n 0) :
    IsBalanced A := by
  intro i
  left
  simp

/-- The empty-item case of both identical-valuation existence statements. -/
theorem identical_zero {n : ℕ} (hn : 0 < n)
    (v : Finset (Fin 0) → ℝ) :
    ∃ (A : Allocation n 0) (t : ℝ),
      IsBalanced A ∧ HasCommonThreshold v A t := by
  let A : Allocation n 0 := Fin.elim0
  refine ⟨A, v ∅, isBalanced_zero hn A, ?_⟩
  intro i
  refine ⟨⟨∅, canDeleteOne_empty _, ?_⟩,
    ⟨∅, canDeleteOne_empty _, ?_⟩⟩
  · simp
  · simp

/-- A strictly positive weighted-welfare maximizer is fractionally Pareto
optimal against every feasible balanced fractional competitor. -/
theorem constrainedFPO_of_weighted_max {n m : ℕ}
    (v : Fin n → Fin m → ℝ) (A : Allocation n m)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hmax : ∀ x : Fin n → Fin m → ℝ, IsBalancedFractional x →
      (∑ i : Fin n, w i * fractionalValue v x i) ≤
        ∑ i : Fin n, w i * additiveValue v i (bundle A i)) :
    IsConstrainedFPO v A := by
  intro x hx himprovement
  obtain ⟨hweak, i, hstrict⟩ := himprovement
  have hlt :
      (∑ j : Fin n, w j * additiveValue v j (bundle A j)) <
        ∑ j : Fin n, w j * fractionalValue v x j := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_le_mul_of_nonneg_left (hweak j) (le_of_lt (hw j))
    · exact ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hstrict (hw i)⟩
  exact (not_lt_of_ge (hmax x hx)) hlt

/-- The empty-item instance of the balanced fairness-and-efficiency theorem. -/
theorem balancedFairEfficient_zero {n : ℕ} (hn : 0 < n)
    (v : Fin n → Fin 0 → ℝ) :
    ∃ A : Allocation n 0,
      IsBalanced A ∧ IsEF11 (additiveAsBundleValue v) A ∧
      IsConstrainedFPO v A ∧ (n ∣ 0 → IsSwapEF v A) := by
  let A : Allocation n 0 := Fin.elim0
  refine ⟨A, isBalanced_zero hn A, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨∅, ∅, canDeleteOne_empty _, canDeleteOne_empty _, ?_⟩
    simp [additiveAsBundleValue, additiveValue]
  · intro x _ himprovement
    obtain ⟨_, i, hi⟩ := himprovement
    simp [additiveValue, fractionalValue] at hi
  · intro _ i j
    left
    simp [additiveValue]

/-- With one agent, the all-to-one allocation is balanced, fair, and
fractionally Pareto optimal in the balanced feasible polytope. -/
theorem balancedFairEfficient_one (m : ℕ) (v : Fin 1 → Fin m → ℝ) :
    ∃ A : Allocation 1 m,
      IsBalanced A ∧ IsEF11 (additiveAsBundleValue v) A ∧
      IsConstrainedFPO v A ∧ (1 ∣ m → IsSwapEF v A) := by
  let A : Allocation 1 m := fun _ => 0
  refine ⟨A, isBalanced_one m A, ?_, ?_, ?_⟩
  · intro i j
    refine ⟨∅, ∅, canDeleteOne_empty _, canDeleteOne_empty _, ?_⟩
    simp [bundle_one, additiveAsBundleValue]
  · intro x hx himprovement
    obtain ⟨_, i, hi⟩ := himprovement
    have hxi (g : Fin m) : x i g = 1 := by
      have hcol := hx.2.1 g
      simpa [Fin.sum_univ_one, Subsingleton.elim i 0] using hcol
    have hval : fractionalValue v x i = additiveValue v i (bundle A i) := by
      simp [fractionalValue, additiveValue, bundle_one, hxi]
    exact (lt_irrefl _ ) (hval ▸ hi)
  · intro _ i j
    left
    simp [bundle_one]

end FairDivision
