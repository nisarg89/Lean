import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_RationalPerturbation

theorem proved : Statement := by
  intro f z hz hz1 hf hf0
  have he : ∀ᶠ y in 𝓝 z, f y < 0 := hf.eventually (gt_mem_nhds hf0)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  have hleft : max 0 (z-ε) < z := max_lt hz (by linarith)
  obtain ⟨q, hql, hqz⟩ := exists_rat_btwn hleft
  refine ⟨q, ?_, hqz, ?_⟩
  · exact_mod_cast lt_of_le_of_lt (le_max_left (0 : ℝ) (z-ε)) hql
  · apply he
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hqz)]
    have hlow := lt_of_le_of_lt (le_max_right (0 : ℝ) (z-ε)) hql
    linarith

#print axioms proved
end MetricDistortion.Contracts.Lower_RationalPerturbation
