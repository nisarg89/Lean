import Mathlib.Analysis.Convex.Birkhoff

/-!
# A positive perfect matching in a doubly stochastic matrix

This is the Birkhoff step in the preference-score argument of BF Section 5.
It extracts a permutation whose selected entry is strictly positive in
every row, so that each agent receives a bundle to which she gave positive
approximate-favorite weight.
-/

set_option autoImplicit false

namespace FairDivision.Finite

open scoped BigOperators Classical

open Matrix

/-- Retain the positive coefficient β of an actual permutation in
Mathlib's Birkhoff decomposition. Every selected entry is at least β. -/
theorem exists_positive_matching_with_weight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M ∈ doublyStochastic ℝ ι) :
    ∃ (σ : Equiv.Perm ι) (β : ℝ), 0 < β ∧ ∀ i : ι, β ≤ M i (σ i) := by
  classical
  obtain ⟨w, hw, hwsum, hdecomp⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hM
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm ι, 0 < w σ := by
    by_contra h
    push_neg at h
    have hzero (τ : Equiv.Perm ι) : w τ = 0 :=
      le_antisymm (h τ) (hw τ)
    simp [hzero] at hwsum
  refine ⟨σ, w σ, hσ, fun i => ?_⟩
  have hsum := congrArg
    (fun N : Matrix ι ι ℝ => N i (σ i)) hdecomp
  have hterm_nonneg (τ : Equiv.Perm ι) :
      0 ≤ w τ * τ.permMatrix ℝ i (σ i) := by
    apply mul_nonneg (hw τ)
    exact (mem_doublyStochastic_iff_sum.mp
      (permMatrix_mem_doublyStochastic (R := ℝ) (σ := τ))).1 _ _
  have hsum' :
      (∑ τ : Equiv.Perm ι,
        w τ * τ.permMatrix ℝ i (σ i)) = M i (σ i) := by
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hsum
  have hle : w σ * σ.permMatrix ℝ i (σ i) ≤ M i (σ i) := by
    rw [← hsum']
    exact Finset.single_le_sum (fun τ _ => hterm_nonneg τ)
      (Finset.mem_univ σ)
  have hone : σ.permMatrix ℝ i (σ i) = 1 := by
    simp [Equiv.Perm.permMatrix]
  rw [hone, mul_one] at hle
  exact hle

/-- A doubly stochastic real matrix supports a positive permutation. -/
theorem exists_positive_matching_of_doublyStochastic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M ∈ doublyStochastic ℝ ι) :
    ∃ σ : Equiv.Perm ι, ∀ i : ι, 0 < M i (σ i) := by
  obtain ⟨σ, β, hβ, hSelected⟩ := exists_positive_matching_with_weight M hM
  exact ⟨σ, fun i => hβ.trans_le (hSelected i)⟩

/-- The preference-score argument after score equalization: if each positive
matrix entry points to an `ε`-favorite bundle, Birkhoff selects a distinct
`ε`-favorite position for every agent. The reordering of the bundles is
performed by the returned permutation. -/
theorem exists_approxEnvyFree_reordering
    {ι Z : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Z → ℝ) (y : ι → Z) (ε : ℝ)
    (α : Matrix ι ι ℝ) (hα : α ∈ doublyStochastic ℝ ι)
    (hsupport : ∀ i s : ι, 0 < α i s →
      ∀ t : ι, v i (y t) - ε < v i (y s)) :
    ∃ σ : Equiv.Perm ι,
      ∀ i j : ι, v i (y (σ j)) - ε < v i (y (σ i)) := by
  obtain ⟨σ, hσ⟩ :=
    exists_positive_matching_of_doublyStochastic α hα
  exact ⟨σ, fun i j => hsupport i (σ i) (hσ i) (σ j)⟩

end FairDivision.Finite
