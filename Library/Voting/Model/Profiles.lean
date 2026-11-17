import Voting.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_Profiles
theorem proved : Statement := by
  intro n m σ v a b
  refine ⟨?_, ?_, ?_⟩
  · exact lt_irrefl _
  · exact fun hab => not_lt_of_gt hab
  · intro hab
    have hne : σ v a ≠ σ v b := (σ v).injective.ne hab
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr h
    · exact Or.inl h
#print axioms proved
end MetricDistortion.Contracts.Model_Profiles
