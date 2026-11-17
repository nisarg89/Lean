import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
namespace MetricDistortion.Contracts.Numerics_Benchmark

theorem from_children (h : Needs) : Statement := by
  unfold Statement
  norm_num [phiStar,bStar,muStar,cStar]

#print axioms from_children
end MetricDistortion.Contracts.Numerics_Benchmark
