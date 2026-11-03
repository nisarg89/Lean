import FairDivision.Finite.PositiveBirkhoffMatching

/-!
# BF Section 5: approximate preference scores

This is the preference-score construction in the manuscript. Each agent
places unit total weight on positions within `ε` of their favorite. Equal
column scores make the weight matrix doubly stochastic, and the existing
Birkhoff matching step then reorders the positions into an approximately
envy-free family.
-/

set_option autoImplicit false

namespace FairDivision.BF

open scoped BigOperators Classical

open Matrix

theorem fin_univ_nonempty {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- Agent `i`'s favorite value among the current `n` positions. -/
noncomputable def favoriteValue {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (y : Fin n → Z) (i : Fin n) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' (fin_univ_nonempty hn)
    (fun s => v i (y s))

private theorem value_le_favorite {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (y : Fin n → Z)
    (i s : Fin n) :
    v i (y s) ≤ favoriteValue hn v y i := by
  exact Finset.le_sup' (fun t => v i (y t)) (Finset.mem_univ s)

private theorem exists_favorite_position {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (y : Fin n → Z)
    (i : Fin n) :
    ∃ s : Fin n, v i (y s) = favoriteValue hn v y i := by
  obtain ⟨s, _, hs⟩ :=
    (Finset.univ : Finset (Fin n)).exists_mem_eq_sup'
      (fin_univ_nonempty hn) (fun t => v i (y t))
  exact ⟨s, hs.symm⟩

/-- The nonnegative numerator of agent `i`'s weight on position `s`. -/
noncomputable def preferenceNumerator {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (i s : Fin n) : ℝ :=
  max 0 (ε + v i (y s) - favoriteValue hn v y i)

/-- The sum of agent `i`'s preference numerators. -/
noncomputable def preferenceDenominator {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (i : Fin n) : ℝ :=
  ∑ s : Fin n, preferenceNumerator hn v ε y i s

/-- Agent `i`'s normalized weight on position `s`. -/
noncomputable def preferenceWeight {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (i s : Fin n) : ℝ :=
  preferenceNumerator hn v ε y i s /
    preferenceDenominator hn v ε y i

/-- Total preference weight received by position `s`. -/
noncomputable def positionScore {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (s : Fin n) : ℝ :=
  ∑ i : Fin n, preferenceWeight hn v ε y i s

private theorem numerator_nonneg {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ)
    (y : Fin n → Z) (i s : Fin n) :
    0 ≤ preferenceNumerator hn v ε y i s :=
  le_max_left _ _

/-- A favorite position contributes exactly ε, so the denominator is
at least the tolerance itself, as stated in the manuscript. -/
theorem preferenceDenominator_ge_tolerance {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (y : Fin n → Z) (i : Fin n) :
    ε ≤ preferenceDenominator hn v ε y i := by
  obtain ⟨s, hs⟩ := exists_favorite_position hn v y i
  have hnum : preferenceNumerator hn v ε y i s = ε := by
    unfold preferenceNumerator
    rw [hs]
    simp [max_eq_right hε]
  have hle : preferenceNumerator hn v ε y i s ≤
      preferenceDenominator hn v ε y i := by
    unfold preferenceDenominator
    exact Finset.single_le_sum
      (fun t _ => numerator_nonneg hn v ε y i t)
      (Finset.mem_univ s)
  simpa only [hnum] using hle

/-- Positive tolerance makes every normalizing denominator strictly
positive; no agent or position is discarded. -/
theorem preferenceDenominator_pos {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z) (i : Fin n) :
    0 < preferenceDenominator hn v ε y i :=
  hε.trans_le (preferenceDenominator_ge_tolerance hn v ε hε.le y i)

/-- Every normalized entry is nonnegative for the SAME positive tolerance. -/
theorem preferenceWeight_nonneg {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z) (i s : Fin n) :
    0 ≤ preferenceWeight hn v ε y i s :=
  div_nonneg (numerator_nonneg hn v ε y i s)
    (preferenceDenominator_pos hn v ε hε y i).le

/-- Agent weights form probability distributions over positions. -/
theorem preferenceWeight_row_sum {n : ℕ} (hn : 0 < n)
    {Z : Type*} (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z) (i : Fin n) :
    ∑ s : Fin n, preferenceWeight hn v ε y i s = 1 := by
  rw [show (∑ s : Fin n, preferenceWeight hn v ε y i s) =
      (∑ s : Fin n, preferenceNumerator hn v ε y i s) /
        preferenceDenominator hn v ε y i from by
          simp only [preferenceWeight, Finset.sum_div]]
  rw [show (∑ s : Fin n, preferenceNumerator hn v ε y i s) =
      preferenceDenominator hn v ε y i from rfl]
  exact div_self (ne_of_gt (preferenceDenominator_pos hn v ε hε y i))

/-- Exact support of the manuscript's normalized preference matrix:
positive entries are precisely the positions strictly within ε of the
agent's maximum, including the stated strict endpoint convention. -/
theorem preferenceWeight_pos_iff_near_favorite {n : ℕ}
    (hn : 0 < n) {Z : Type*} (v : Fin n → Z → ℝ)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → Z) (i s : Fin n) :
    0 < preferenceWeight hn v ε y i s ↔
      favoriteValue hn v y i - ε < v i (y s) := by
  have hden := preferenceDenominator_pos hn v ε hε y i
  constructor
  · intro hpos
    have hnum : 0 < preferenceNumerator hn v ε y i s :=
      (div_pos_iff_of_pos_right hden).mp hpos
    have hraw : 0 < ε + v i (y s) - favoriteValue hn v y i := by
      simpa [preferenceNumerator, lt_max_iff] using hnum
    linarith
  · intro hnear
    have hraw : 0 < ε + v i (y s) - favoriteValue hn v y i := by linarith
    have hnum : 0 < preferenceNumerator hn v ε y i s :=
      hraw.trans_le (le_max_right 0 _)
    exact (div_pos_iff_of_pos_right hden).mpr hnum

/-- Positive weight identifies a position strictly within ε of every
competing position, by the SAME maximum comparison used in the manuscript. -/
theorem preferenceWeight_pos_implies_near_favorite {n : ℕ}
    (hn : 0 < n) {Z : Type*} (v : Fin n → Z → ℝ)
    (ε : ℝ) (hε : 0 < ε) (y : Fin n → Z)
    (i s t : Fin n)
    (hpos : 0 < preferenceWeight hn v ε y i s) :
    v i (y t) - ε < v i (y s) := by
  have hnear := (preferenceWeight_pos_iff_near_favorite hn v ε hε y i s).mp hpos
  have hle := value_le_favorite hn v y i t
  linarith

/-- Equal scores turn the preference weights into a doubly stochastic
matrix, exactly as in the manuscript. -/
theorem preferenceWeight_doublyStochastic_of_equal_scores
    {n : ℕ} (hn : 0 < n) {Z : Type*}
    (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z)
    (heq : ∀ s : Fin n, positionScore hn v ε y s = 1) :
    (fun i s => preferenceWeight hn v ε y i s) ∈
      doublyStochastic ℝ (Fin n) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro i s
    exact preferenceWeight_nonneg hn v ε hε y i s
  · exact preferenceWeight_row_sum hn v ε hε y
  · exact heq

/-- Equalized preference scores yield the manuscript's approximate envy
comparisons after one permutation of positions. -/
theorem exists_approxEnvyFree_of_equal_scores
    {n : ℕ} (hn : 0 < n) {Z : Type*}
    (v : Fin n → Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (y : Fin n → Z)
    (heq : ∀ s : Fin n, positionScore hn v ε y s = 1) :
    ∃ σ : Equiv.Perm (Fin n),
      ∀ i j : Fin n, v i (y (σ j)) - ε < v i (y (σ i)) := by
  let α : Matrix (Fin n) (Fin n) ℝ :=
    fun i s => preferenceWeight hn v ε y i s
  have hα : α ∈ doublyStochastic ℝ (Fin n) :=
    preferenceWeight_doublyStochastic_of_equal_scores hn v ε hε y heq
  exact FairDivision.Finite.exists_approxEnvyFree_reordering
    v y ε α hα
    (fun i s his t =>
      preferenceWeight_pos_implies_near_favorite hn v ε hε y i s t his)

end FairDivision.BF
