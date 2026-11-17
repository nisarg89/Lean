import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_MetricRankCuts
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ P d hd o v
  exact ⟨h.child_0 n m σ P d hd o v,
    fun q hq => h.child_2 n m σ P d hd o v q⟩
#print axioms from_children
end MetricDistortion.Contracts.Geometry_MetricRankCuts
