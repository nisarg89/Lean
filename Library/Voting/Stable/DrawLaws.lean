import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_DrawLaws
theorem proved : Statement := by
  intro D
  refine ⟨fun k => ENNReal.toReal_nonneg, ?_⟩
  have ht : (∑' k, (D k).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => D.apply_ne_top k), D.tsum_coe]
    norm_num
  change HasSum (fun k : ℕ => (D k).toReal) 1
  have hs := ENNReal.hasSum_toReal D.tsum_coe_ne_top
  rw [ht] at hs
  exact hs
#print axioms proved
end MetricDistortion.Contracts.Model_DrawLaws
