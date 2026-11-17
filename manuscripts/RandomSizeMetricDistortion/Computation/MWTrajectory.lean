import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_MWTrajectory
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D σ δ hδ
  let initial : Lottery m := ⟨fun _ => 1/(m : ℝ), by
    refine ⟨fun _ => by positivity, ?_⟩
    simp [Nat.ne_of_gt hm]⟩
  let update (P : Lottery m) : Lottery m := ⟨fun c =>
      P.val c * Real.exp (4*δ*score D σ P c) /
        ∑ b, P.val b*Real.exp (4*δ*score D σ P b), by
    have hden : 0 < ∑ b, P.val b*Real.exp (4*δ*score D σ P b) := by
      have hsome : ∃ b, 0 < P.val b := by
        by_contra hnone
        push_neg at hnone
        have hz : ∑ b, P.val b = 0 := Finset.sum_eq_zero
          (fun b _ => le_antisymm (hnone b) (P.property.1 b))
        linarith [P.property.2]
      obtain ⟨b,hb⟩ := hsome
      exact Finset.sum_pos' (fun c _ => mul_nonneg (P.property.1 c) (Real.exp_nonneg _))
        ⟨b,Finset.mem_univ b,mul_pos hb (Real.exp_pos _)⟩
    refine ⟨fun c => div_nonneg (mul_nonneg (P.property.1 c) (Real.exp_nonneg _)) hden.le, ?_⟩
    rw [← Finset.sum_div, div_self (ne_of_gt hden)]⟩
  let P : ℕ → Lottery m := fun t => Nat.rec initial (fun _ P => update P) t
  have hinit : P 0 = initial := rfl
  have hstep (t : ℕ) : P (t+1) = update (P t) := rfl
  refine ⟨P, ⟨fun c => rfl, fun t c => rfl⟩, ?_⟩
  intro t
  induction t with
  | zero => intro c; change 0 < 1/(m : ℝ); positivity
  | succ t ih =>
    intro c
    rw [hstep]
    change 0 < (P t).val c * Real.exp (4*δ*score D σ (P t) c) /
      ∑ b, (P t).val b*Real.exp (4*δ*score D σ (P t) b)
    apply div_pos (mul_pos (ih c) (Real.exp_pos _))
    exact Finset.sum_pos' (fun b _ => mul_nonneg ((P t).property.1 b) (Real.exp_nonneg _))
      ⟨c,Finset.mem_univ c,mul_pos (ih c) (Real.exp_pos _)⟩
#print axioms from_children
end MetricDistortion.Contracts.Computation_MWTrajectory
