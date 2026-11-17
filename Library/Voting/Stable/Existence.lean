import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Stability_Existence
theorem from_children (h : Needs) : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m hn hm σ D
    exact h.child_0 n m hn hm D σ
  · intro n m hn hm σ D P hP c hc
    exact h.child_2 n m hn hm D σ P hP c hc
  · intro D β hβ
    let σ : Profile 1 1 := fun _ => Equiv.refl _
    refine ⟨1, 1, by norm_num, by norm_num, σ, ?_⟩
    intro P
    refine ⟨0, ?_⟩
    have hp : P.val 0 = 1 := by simpa using P.property.2
    have hs := h.child_1 1 1 (by norm_num) (by norm_num) D σ P
    have heq : score D σ P 0 = mu D := by simpa [payoff, hp] using hs
    exact hβ.trans_le heq.ge
#print axioms from_children
end MetricDistortion.Contracts.Stability_Existence
