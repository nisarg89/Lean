import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_DistortionConventions
theorem proved : Statement := by
  refine ⟨by simp [ratio], ?_, by simp [offsetRatio], ?_⟩
  · intro z hz
    simp [ratio, ne_of_gt hz]
  · intro z hz
    simp [offsetRatio, ne_of_gt hz]
#print axioms proved
end MetricDistortion.Contracts.Model_DistortionConventions
