import FairDivision.LinearAlgebra.RankMinorForward
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Extracting a nonzero square minor from rectangular rank

The FE few-ties proof uses rank preservation after specializing the value
indeterminates. This module extracts the converse to `RankMinorForward`:
a finite rational matrix of rank `r` has an `r × r` nonzero minor. It
chooses independent rows from their finite span, then independent columns
from the resulting full-row-rank matrix.
-/

set_option autoImplicit false

namespace FairDivision.LinearAlgebra

open Matrix

private theorem exists_nonzero_column_minor_of_independent_rows
    {K : Type*} [Field K] {r : ℕ} {n : Type*} [Fintype n]
    (M : Matrix (Fin r) n K)
    (hrow : LinearIndependent K M.row) :
    ∃ cols : Fin r → n, (M.submatrix id cols).det ≠ 0 := by
  classical
  let s : Set (Fin r → K) := Set.range M.col
  haveI : Module.Finite K (Submodule.span K s) :=
    Module.Finite.span_of_finite K (Set.finite_range M.col)
  have hdim : Module.finrank K (Submodule.span K s) = r := by
    rw [← M.rank_eq_finrank_span_cols]
    simpa only [Fintype.card_fin] using hrow.rank_matrix
  have hex := Submodule.exists_fun_fin_finrank_span_eq K s
  rw [hdim] at hex
  obtain ⟨f, hfmem, _hspan, hfli⟩ := hex
  have hfmem' : ∀ i, ∃ j, M.col j = f i := hfmem
  choose cols hcols using hfmem'
  have hcol : LinearIndependent K (fun i => M.col (cols i)) := by
    have heq : (fun i => M.col (cols i)) = f := by
      funext i
      exact hcols i
    rw [heq]
    exact hfli
  let B : Matrix (Fin r) (Fin r) K := M.submatrix id cols
  have hBcol : LinearIndependent K B.col := by
    have heq : B.col = (fun i => M.col (cols i)) := by
      funext j i
      rfl
    rw [heq]
    exact hcol
  have hBnon : B.Nonsingular := Matrix.linearIndependent_col_iff.mp hBcol
  exact ⟨cols, Matrix.nonsingular_iff_det_ne_zero.mp hBnon⟩

/-- A finite matrix over a field of rank `r` has a nonzero square minor of
size `r`. This is the missing direction in the manuscript's claim that
preserving all determinant minors preserves every submatrix rank. -/
theorem exists_nonzero_minor_at_rank
    {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K) :
    ∃ (rows : Fin M.rank → m) (cols : Fin M.rank → n),
      (M.submatrix rows cols).det ≠ 0 := by
  classical
  let s : Set (n → K) := Set.range M.row
  haveI : Module.Finite K (Submodule.span K s) :=
    Module.Finite.span_of_finite K (Set.finite_range M.row)
  have hdim : Module.finrank K (Submodule.span K s) = M.rank := by
    exact M.rank_eq_finrank_span_row.symm
  have hex := Submodule.exists_fun_fin_finrank_span_eq K s
  rw [hdim] at hex
  obtain ⟨f, hfmem, _hspan, hfli⟩ := hex
  have hfmem' : ∀ i, ∃ j, M.row j = f i := hfmem
  choose rows hrows using hfmem'
  have hrow : LinearIndependent K (fun i => M.row (rows i)) := by
    have heq : (fun i => M.row (rows i)) = f := by
      funext i
      exact hrows i
    rw [heq]
    exact hfli
  let B : Matrix (Fin M.rank) n K := M.submatrix rows id
  have hBrow : LinearIndependent K B.row := by
    have heq : B.row = (fun i => M.row (rows i)) := by
      funext j i
      rfl
    rw [heq]
    exact hrow
  obtain ⟨cols, hdet⟩ :=
    exists_nonzero_column_minor_of_independent_rows B hBrow
  refine ⟨rows, cols, ?_⟩
  simpa [B, Matrix.submatrix] using hdet

/-- Two matrices over a field have the same rank if the zero/nonzero pattern
of every square minor agrees. The FE few-ties proof applies this to each
row submatrix, both with and without a selected weight column. -/
theorem rank_eq_of_all_minors_nonzero_iff
    {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    (M N : Matrix m n K)
    (hminor : ∀ k : ℕ, ∀ (rows : Fin k → m) (cols : Fin k → n),
      (M.submatrix rows cols).det ≠ 0 ↔
        (N.submatrix rows cols).det ≠ 0) :
    M.rank = N.rank := by
  apply Nat.le_antisymm
  · obtain ⟨rows, cols, hdet⟩ := exists_nonzero_minor_at_rank M
    simpa only [Fintype.card_fin] using
      rank_at_least_of_nonzero_minor N rows cols
        ((hminor M.rank rows cols).mp hdet)
  · obtain ⟨rows, cols, hdet⟩ := exists_nonzero_minor_at_rank N
    simpa only [Fintype.card_fin] using
      rank_at_least_of_nonzero_minor M rows cols
        ((hminor N.rank rows cols).mpr hdet)

/-- Matrices over different fields have equal ranks when all corresponding
square minors share the same zero/nonzero pattern. This lets the generic
rational-function comparison matrix and a rational specialization be
compared without first coercing either matrix into the other field. -/
theorem rank_eq_of_all_minors_nonzero_iff_cross_field
    {K L : Type*} [Field K] [Field L]
    {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K) (N : Matrix m n L)
    (hminor : ∀ k : ℕ, ∀ (rows : Fin k → m) (cols : Fin k → n),
      (M.submatrix rows cols).det ≠ 0 ↔
        (N.submatrix rows cols).det ≠ 0) :
    M.rank = N.rank := by
  apply Nat.le_antisymm
  · obtain ⟨rows, cols, hdet⟩ := exists_nonzero_minor_at_rank M
    simpa only [Fintype.card_fin] using
      rank_at_least_of_nonzero_minor N rows cols
        ((hminor M.rank rows cols).mp hdet)
  · obtain ⟨rows, cols, hdet⟩ := exists_nonzero_minor_at_rank N
    simpa only [Fintype.card_fin] using
      rank_at_least_of_nonzero_minor M rows cols
        ((hminor N.rank rows cols).mpr hdet)

/-- The cross-field minor criterion also applies after arbitrary row and
column selection. -/
theorem rank_submatrix_eq_of_all_minors_nonzero_iff_cross_field
    {K L : Type*} [Field K] [Field L]
    {m n a b : Type*}
    [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    (M : Matrix m n K) (N : Matrix m n L)
    (hminor : ∀ k : ℕ, ∀ (rows : Fin k → m) (cols : Fin k → n),
      (M.submatrix rows cols).det ≠ 0 ↔
        (N.submatrix rows cols).det ≠ 0)
    (r : a → m) (c : b → n) :
    (M.submatrix r c).rank = (N.submatrix r c).rank := by
  apply rank_eq_of_all_minors_nonzero_iff_cross_field
  intro k rows cols
  simpa only [Matrix.submatrix_submatrix] using
    hminor k (r ∘ rows) (c ∘ cols)

/-- The same minor pattern preserves the rank of every selected row and
column submatrix. In the FE few-ties argument the column selector may omit
one welfare-weight column. -/
theorem rank_submatrix_eq_of_all_minors_nonzero_iff
    {K : Type*} [Field K] {m n a b : Type*}
    [Fintype m] [Fintype n] [Fintype a] [Fintype b]
    (M N : Matrix m n K)
    (hminor : ∀ k : ℕ, ∀ (rows : Fin k → m) (cols : Fin k → n),
      (M.submatrix rows cols).det ≠ 0 ↔
        (N.submatrix rows cols).det ≠ 0)
    (r : a → m) (c : b → n) :
    (M.submatrix r c).rank = (N.submatrix r c).rank := by
  apply rank_eq_of_all_minors_nonzero_iff
  intro k rows cols
  simpa only [Matrix.submatrix_submatrix] using
    hminor k (r ∘ rows) (c ∘ cols)

end FairDivision.LinearAlgebra
