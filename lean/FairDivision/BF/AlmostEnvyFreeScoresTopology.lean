import FairDivision.BF.AlmostEnvyFreeScores

/-!
# Continuity and normalization of BF preference scores

The scores are built from finite maxima, positive denominators, and finite
sums. These facts support the topological equalization step in BF Section 5.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

/-- Total position score equals the number of agents. -/
theorem positionScore_total {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → Z) :
    ∑ s : Fin n, positionScore hn v ε y s = (n : ℝ) := by
  simp only [positionScore]
  rw [Finset.sum_comm]
  simp [preferenceWeight_row_sum hn v ε hε y]

/-- Equal position scores all equal one, by the total-score identity. -/
theorem positionScore_eq_one_of_equalized {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → Z)
    (heq : ∀ s t : Fin n,
      positionScore hn v ε y s = positionScore hn v ε y t) :
    ∀ s : Fin n, positionScore hn v ε y s = 1 := by
  intro s
  have hsum := positionScore_total hn v ε hε y
  have hsame :
      (∑ t : Fin n, positionScore hn v ε y t) =
        (n : ℝ) * positionScore hn v ε y s := by
    calc
      _ = ∑ _t : Fin n, positionScore hn v ε y s := by
        apply Finset.sum_congr rfl
        intro t _
        exact heq t s
      _ = (n : ℝ) * positionScore hn v ε y s := by
        simp [mul_comm]
  have hprod :
      (n : ℝ) * positionScore hn v ε y s = (n : ℝ) * 1 := by
    simpa only [mul_one] using hsame.symm.trans hsum
  exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) hprod)

/-- The favorite value varies continuously when every agent-position value
does. -/
theorem favoriteValue_continuous {n : ℕ} (hn : 0 < n)
    {Y Z : Type*} [TopologicalSpace Y]
    (v : Fin n → Z → ℝ) (bundle : Y → Fin n → Z)
    (hval : ∀ i s : Fin n, Continuous (fun y => v i (bundle y s)))
    (i : Fin n) :
    Continuous (fun y => favoriteValue hn v (bundle y) i) := by
  unfold favoriteValue
  exact Continuous.finset_sup'_apply (fin_univ_nonempty hn)
    (fun s _ => hval i s)

/-- Each nonnegative preference numerator is continuous. -/
theorem preferenceNumerator_continuous {n : ℕ} (hn : 0 < n)
    {Y Z : Type*} [TopologicalSpace Y]
    (v : Fin n → Z → ℝ) (ε : ℝ)
    (bundle : Y → Fin n → Z)
    (hval : ∀ i s : Fin n, Continuous (fun y => v i (bundle y s)))
    (i s : Fin n) :
    Continuous (fun y => preferenceNumerator hn v ε (bundle y) i s) := by
  unfold preferenceNumerator
  exact continuous_const.max
    ((continuous_const.add (hval i s)).sub
      (favoriteValue_continuous hn v bundle hval i))

/-- Each preference denominator is continuous. -/
theorem preferenceDenominator_continuous {n : ℕ} (hn : 0 < n)
    {Y Z : Type*} [TopologicalSpace Y]
    (v : Fin n → Z → ℝ) (ε : ℝ)
    (bundle : Y → Fin n → Z)
    (hval : ∀ i s : Fin n, Continuous (fun y => v i (bundle y s)))
    (i : Fin n) :
    Continuous (fun y => preferenceDenominator hn v ε (bundle y) i) := by
  unfold preferenceDenominator
  exact continuous_finsetSum Finset.univ
    (fun s _ => preferenceNumerator_continuous hn v ε bundle hval i s)

/-- Normalized preference weights vary continuously. -/
theorem preferenceWeight_continuous {n : ℕ} (hn : 0 < n)
    {Y Z : Type*} [TopologicalSpace Y]
    (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (bundle : Y → Fin n → Z)
    (hval : ∀ i s : Fin n, Continuous (fun y => v i (bundle y s)))
    (i s : Fin n) :
    Continuous (fun y => preferenceWeight hn v ε (bundle y) i s) := by
  unfold preferenceWeight
  exact (preferenceNumerator_continuous hn v ε bundle hval i s).div
    (preferenceDenominator_continuous hn v ε bundle hval i)
    (fun y => (ne_of_gt (preferenceDenominator_pos hn v ε hε (bundle y) i)))

/-- The manuscript's position-score vector is continuous. -/
theorem positionScore_continuous {n : ℕ} (hn : 0 < n)
    {Y Z : Type*} [TopologicalSpace Y]
    (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (bundle : Y → Fin n → Z)
    (hval : ∀ i s : Fin n, Continuous (fun y => v i (bundle y s))) :
    Continuous (fun y => fun s => positionScore hn v ε (bundle y) s) := by
  apply continuous_pi
  intro s
  unfold positionScore
  exact continuous_finsetSum Finset.univ
    (fun i _ => preferenceWeight_continuous hn v ε hε bundle hval i s)

/-- The equal-score hypothesis has the approximate envy-free consequence
claimed in BF Section 5. -/
theorem exists_approxEnvyFree_of_equalized_scores
    {n : ℕ} (hn : 0 < n) {Z : Type*}
    (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z)
    (heq : ∀ s t : Fin n,
      positionScore hn v ε y s = positionScore hn v ε y t) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i j : Fin n, v i (y (σ j)) - ε < v i (y (σ i)) := by
  exact exists_approxEnvyFree_of_equal_scores hn v ε hε y
    (positionScore_eq_one_of_equalized hn v ε hε y heq)

end FairDivision.BF
