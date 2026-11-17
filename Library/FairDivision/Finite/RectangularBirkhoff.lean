import FairDivision.Finite.SlotStochastic
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Birkhoff decomposition of a rectangular balanced assignment

The slot expansion adds dummy columns, then reindexes them to obtain a
square doubly stochastic matrix. This isolates the general transportation
integrality step from fairness and welfare arguments.
-/

set_option autoImplicit false

namespace FairDivision

open Matrix

/-- The square matrix obtained by reindexing real and dummy columns to
agent slots. -/
noncomputable def squareExpandedMatrix {n m : ℕ} (hn : 0 < n)
    (x : Fin n → Fin m → ℝ) :
    Matrix (AssignmentSlot n m) (AssignmentSlot n m) ℝ :=
  fun s t => expandedMatrix x s ((assignmentColumnEquiv n m hn).symm t)

/-- The reindexed expansion is doubly stochastic. -/
theorem squareExpandedMatrix_mem_doublyStochastic {n m : ℕ}
    (hn : 0 < n) (x : Fin n → Fin m → ℝ)
    (hx : IsBalancedFractional x) :
    squareExpandedMatrix hn x ∈
      doublyStochastic ℝ (AssignmentSlot n m) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    exact expandedMatrix_nonneg hn x hx s _
  · intro s
    change (∑ t : AssignmentSlot n m,
      expandedMatrix x s ((assignmentColumnEquiv n m hn).symm t)) = 1
    rw [Equiv.sum_comp (assignmentColumnEquiv n m hn).symm]
    exact expanded_row_sum hn x hx s
  · intro t
    exact expanded_column_sum hn x hx _

/-- The slot expansion has a finite convex Birkhoff decomposition. -/
theorem exists_slot_perm_decomposition {n m : ℕ}
    (hn : 0 < n) (x : Fin n → Fin m → ℝ)
    (hx : IsBalancedFractional x) :
    ∃ w : Equiv.Perm (AssignmentSlot n m) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧
      (∑ σ, w σ) = 1 ∧
      (∑ σ, w σ • σ.permMatrix ℝ) = squareExpandedMatrix hn x := by
  exact exists_eq_sum_perm_of_mem_doublyStochastic
    (squareExpandedMatrix_mem_doublyStochastic hn x hx)

end FairDivision
