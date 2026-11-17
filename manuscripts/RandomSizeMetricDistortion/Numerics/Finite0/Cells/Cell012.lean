import RandomSizeMetricDistortion.Numerics.Finite0.Shard09
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 0
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open scoped BigOperators
open Set

namespace MetricDistortion.Contracts.Numerics_Finite0Cell012
open MetricDistortion.Contracts.Numerics_FiniteFamily0
abbrev Needs := MetricDistortion.Contracts.Numerics_FiniteFamily0.Needs
def Statement : Prop := FiniteOneSourceBounds ⟨12, by decide⟩
theorem from_children (h : Needs) : Statement := by
  exact MetricDistortion.Contracts.Numerics_Finite0Shard09.from_children h ⟨12, by decide⟩ (by decide)
#print axioms from_children
end MetricDistortion.Contracts.Numerics_Finite0Cell012
