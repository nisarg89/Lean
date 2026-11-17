import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_FixedDrawIntegral

/-- Conditioning on the challenger's label makes the independent draws factor.
The finite product expansion records the same conditioning argument as the paper. -/
theorem from_children (h : Needs) : Statement := by
  intro m r P c k
  let win : ℝ → Fin m → ℝ := fun s j =>
    if j=c then s else if prefers r c j then 1 else 0
  have hsum (s : ℝ) : (∑ j, P.val j*win s j) = below r P c+s*P.val c := by
    calc
      _ = ∑ j, ((if prefers r c j then P.val j else 0)+(if j=c then s*P.val c else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j=c
        · subst j
          simp [win,prefers]
          ring
        · by_cases hr : prefers r c j <;> simp [win,hj,hr]
      _ = _ := by simp [below,mass,Finset.sum_add_distrib]
  have hprod (xs : Fin k → Fin m) (s : ℝ) :
      (∏ i, win s (xs i)) = if ∀ i, r (xs i) ≤ r c then
        s^((Finset.univ.filter fun i => xs i=c).card) else 0 := by
    by_cases hall : ∀ i, r (xs i) ≤ r c
    · rw [if_pos hall]
      have heq : (∏ i, win s (xs i)) = ∏ i, if xs i=c then s else 1 := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : xs i=c
        · simp [win,hi]
        · have hlt : prefers r c (xs i) :=
            lt_of_le_of_ne (hall i) (fun he => hi (r.injective he))
          simp [win,hi,hlt]
      rw [heq,Finset.prod_ite]
      simp
    · obtain ⟨i,hi⟩ := not_forall.mp hall
      have hne : xs i ≠ c := by
        intro he
        apply hi
        simpa [he]
      have hnp : ¬ prefers r c (xs i) := fun hp => hi hp.le
      rw [if_neg hall]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [win,hne,hnp])
  have hexpand (s : ℝ) : (below r P c+s*P.val c)^k =
      ∑ xs : Fin k → Fin m, (∏ i, P.val (xs i))*
        (if ∀ i, r (xs i) ≤ r c then s^((Finset.univ.filter fun i => xs i=c).card) else 0) := by
    rw [← hsum s,Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro xs _
    rw [Finset.prod_mul_distrib,hprod]
  symm
  calc
    (∫ s in (0 : ℝ)..1, (below r P c+s*P.val c)^k) =
      ∫ s in (0 : ℝ)..1, ∑ xs : Fin k → Fin m, (∏ i, P.val (xs i))*
        (if ∀ i, r (xs i) ≤ r c then s^((Finset.univ.filter fun i => xs i=c).card) else 0) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact hexpand s
    _ = ∑ xs : Fin k → Fin m, ∫ s in (0 : ℝ)..1, (∏ i, P.val (xs i))*
        (if ∀ i, r (xs i) ≤ r c then s^((Finset.univ.filter fun i => xs i=c).card) else 0) := by
      apply intervalIntegral.integral_finsetSum
      intro xs _
      apply Continuous.intervalIntegrable
      split_ifs <;> fun_prop
    _ = fixedCompare r P c k := by
      unfold fixedCompare
      apply Finset.sum_congr rfl
      intro xs _
      by_cases hall : ∀ i, r (xs i) ≤ r c
      · simp [hall,intervalIntegral.integral_const_mul,integral_pow,Nat.cast_add,add_comm]
      · simp [hall]

#print axioms from_children
end MetricDistortion.Contracts.Comparison_FixedDrawIntegral
