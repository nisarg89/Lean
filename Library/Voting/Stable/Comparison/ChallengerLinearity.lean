import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Comparison_ChallengerLinearity
theorem from_children (h : Needs) : Statement := by
  intro n m D σ P β
  constructor
  · intro H A
    calc
      payoff D σ A P ≤ ∑ c, A.val c*β :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (H c) (A.property.1 c)
      _ = β := by rw [← Finset.sum_mul,A.property.2,one_mul]
  · intro H c
    let A : Lottery m := ⟨(fun b => if b=c then 1 else 0),
      ⟨(fun b => by dsimp; split_ifs <;> norm_num),by simp⟩⟩
    simpa [payoff,A] using H A
#print axioms from_children
end MetricDistortion.Contracts.Comparison_ChallengerLinearity
