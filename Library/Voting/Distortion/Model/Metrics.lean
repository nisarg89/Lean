import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Model_Metrics
theorem proved : Statement := by
  intro n m d
  letI : PseudoMetricSpace (Fin n ⊕ Fin m) := d
  exact ⟨fun a => dist_self a, fun a b => dist_comm a b,
    fun a b c => dist_triangle a b c, fun a b => dist_nonneg⟩
#print axioms proved
end MetricDistortion.Contracts.Model_Metrics
