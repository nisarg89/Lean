import FairDivision.BF.AlmostEnvyFreeScores

/-!
# Position-relabeling equivariance of BF preference scores

Permuting the current bundles permutes the score columns, while every
agent's favorite value and denominator remain unchanged. This is exactly
the equivariance needed before applying the BF equalizing-scores lemma.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

/-- Relabeling positions does not change any agent's favorite value. -/
theorem favoriteValue_permute {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (y : Fin n → Z)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    favoriteValue hn v (fun s => y (σ s)) i =
      favoriteValue hn v y i := by
  unfold favoriteValue
  apply le_antisymm
  · apply Finset.sup'_le
    intro s _
    exact Finset.le_sup' (fun t => v i (y t))
      (Finset.mem_univ (σ s))
  · apply Finset.sup'_le
    intro t _
    have hle := Finset.le_sup'
      (fun s => v i (y (σ s)))
      (Finset.mem_univ (σ.symm t))
    simpa only [Equiv.apply_symm_apply] using hle

/-- The raw weight on a relabeled position is the old raw weight of the
corresponding original position. -/
theorem preferenceNumerator_permute {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (σ : Equiv.Perm (Fin n))
    (i s : Fin n) :
    preferenceNumerator hn v ε (fun t => y (σ t)) i s =
      preferenceNumerator hn v ε y i (σ s) := by
  unfold preferenceNumerator
  rw [favoriteValue_permute hn v y σ i]

/-- Position relabeling preserves each agent's normalizing denominator. -/
theorem preferenceDenominator_permute {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    preferenceDenominator hn v ε (fun t => y (σ t)) i =
      preferenceDenominator hn v ε y i := by
  unfold preferenceDenominator
  simp_rw [preferenceNumerator_permute hn v ε y σ i]
  exact Equiv.sum_comp σ
    (fun s => preferenceNumerator hn v ε y i s)

/-- Normalized preference weights commute with relabeling. -/
theorem preferenceWeight_permute {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (σ : Equiv.Perm (Fin n))
    (i s : Fin n) :
    preferenceWeight hn v ε (fun t => y (σ t)) i s =
      preferenceWeight hn v ε y i (σ s) := by
  unfold preferenceWeight
  rw [preferenceNumerator_permute hn v ε y σ i s,
    preferenceDenominator_permute hn v ε y σ i]

/-- The position-score vector is equivariant under bundle relabeling. -/
theorem positionScore_permute {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (σ : Equiv.Perm (Fin n))
    (s : Fin n) :
    positionScore hn v ε (fun t => y (σ t)) s =
      positionScore hn v ε y (σ s) := by
  unfold positionScore
  simp_rw [preferenceWeight_permute hn v ε y σ]

end FairDivision.BF
