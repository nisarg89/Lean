import FairDivision.Finite.RectangularBirkhoff

/-!
# Support of permutations in the rectangular Birkhoff decomposition

The expansion has zero entries from regular agent slots to dummy columns.
A positive coefficient in a Birkhoff decomposition therefore cannot assign
a dummy column to any regular slot.
-/

set_option autoImplicit false

namespace FairDivision

open Matrix

/-- A permutation of the expanded square matrix never sends a regular
agent slot to a dummy column. -/
def PermRespectsDummy {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m)) : Prop :=
  ∀ (i : Fin n) (k : Fin (m / n)) (d : Fin (dummyCount n m)),
    σ.permMatrix ℝ (i, .inl k)
      (assignmentColumnEquiv n m hn (.inr d)) = 0

/-- Every positive-weight permutation in the Birkhoff decomposition
respects the forbidden dummy edges. -/
theorem positive_weight_perm_respects_dummy {n m : ℕ}
    (hn : 0 < n) (x : Fin n → Fin m → ℝ)
    (w : Equiv.Perm (AssignmentSlot n m) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ)
    (hdecomp : (∑ σ, w σ • σ.permMatrix ℝ) =
      squareExpandedMatrix hn x)
    (σ : Equiv.Perm (AssignmentSlot n m)) (hσ : 0 < w σ) :
    PermRespectsDummy hn σ := by
  intro i k d
  let t := assignmentColumnEquiv n m hn (.inr d)
  have hzero : squareExpandedMatrix hn x (i, .inl k) t = 0 := by
    simp [squareExpandedMatrix, t, expandedMatrix]
  have hsum :
      (∑ τ : Equiv.Perm (AssignmentSlot n m),
        w τ * τ.permMatrix ℝ (i, .inl k) t) = 0 := by
    have h := congrArg
      (fun M : Matrix (AssignmentSlot n m) (AssignmentSlot n m) ℝ =>
        M (i, .inl k) t) hdecomp
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hzero] using h
  have hterm_nonneg (τ : Equiv.Perm (AssignmentSlot n m)) :
      0 ≤ w τ * τ.permMatrix ℝ (i, .inl k) t := by
    apply mul_nonneg (hw τ)
    exact (mem_doublyStochastic_iff_sum.mp
      (permMatrix_mem_doublyStochastic (R := ℝ) (σ := τ))).1 _ _
  have hle :
      w σ * σ.permMatrix ℝ (i, .inl k) t ≤ 0 := by
    rw [← hsum]
    exact Finset.single_le_sum
      (fun τ _ => hterm_nonneg τ) (Finset.mem_univ σ)
  have hmul : w σ * σ.permMatrix ℝ (i, .inl k) t = 0 :=
    le_antisymm hle (hterm_nonneg σ)
  exact (mul_eq_zero.mp hmul).resolve_left hσ.ne'

/-- Project a slot permutation to an allocation of the real items. -/
noncomputable def slotPermAllocation {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m)) : Allocation n m :=
  fun g => (σ.symm (assignmentColumnEquiv n m hn (.inl g))).1

/-- Every regular slot in a supported permutation receives a real item. -/
theorem regularSlot_has_real_item {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (hσ : PermRespectsDummy hn σ)
    (i : Fin n) (k : Fin (m / n)) :
    ∃ g : Fin m,
      σ (i, .inl k) = assignmentColumnEquiv n m hn (.inl g) := by
  let c := (assignmentColumnEquiv n m hn).symm (σ (i, .inl k))
  cases hc : c with
  | inl g =>
    refine ⟨g, ?_⟩
    calc
      σ (i, .inl k) = assignmentColumnEquiv n m hn c := by
        simp [c]
      _ = assignmentColumnEquiv n m hn (.inl g) := congrArg _ hc
  | inr d =>
    have heq : σ (i, .inl k) =
        assignmentColumnEquiv n m hn (.inr d) := by
      calc
        σ (i, .inl k) = assignmentColumnEquiv n m hn c := by
          simp [c]
        _ = assignmentColumnEquiv n m hn (.inr d) := congrArg _ hc
    have hzero := hσ i k d
    have hone : σ.permMatrix ℝ (i, .inl k)
        (assignmentColumnEquiv n m hn (.inr d)) = 1 := by
      simp [Equiv.Perm.permMatrix, heq]
    rw [hone] at hzero
    norm_num at hzero

/-- An item at a regular slot belongs to that slot's agent after projection. -/
theorem slotPermAllocation_of_regular {n m : ℕ} (hn : 0 < n)
    (σ : Equiv.Perm (AssignmentSlot n m))
    (i : Fin n) (k : Fin (m / n)) (g : Fin m)
    (heq : σ (i, .inl k) = assignmentColumnEquiv n m hn (.inl g)) :
    slotPermAllocation hn σ g = i := by
  have hs : σ.symm (assignmentColumnEquiv n m hn (.inl g)) =
      (i, .inl k) := by
    rw [← heq, σ.symm_apply_apply]
  exact congrArg Prod.fst hs

end FairDivision
