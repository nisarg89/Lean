import Voting.Distortion.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Geometry_CrossingMeasure

theorem from_children (h : Needs) : Statement := by
  intro n m σ P d hd o v q
  let S := crossing σ P d o v q
  let L := 2*distance d (.inl v) (.inr o)
  have hS : MeasurableSet S := (h.child_1 n m σ P d o v).2.1 q
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (@dist_nonneg _ d (.inl v) (.inr o))
  have hdiam : Metric.ediam S ≤ ENNReal.ofReal L := by
    apply Metric.ediam_le_of_forall_dist_le
    intro t ht s hs
    have H := h.child_0 n m σ P d hd o v q t s ht hs
    simpa only [Real.dist_eq,abs_sub_comm] using H
  have hvolume : volume S ≤ ENNReal.ofReal L := (Real.volume_le_diam S).trans hdiam
  change (∫ t, S.indicator (fun _ => (1 : ℝ)) t ∂volume.restrict (Ioi (0 : ℝ))) ≤ L
  rw [integral_indicator_const (1 : ℝ) hS]
  simp only [smul_eq_mul,mul_one,measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hL ((Measure.restrict_apply_le _ _).trans hvolume)

#print axioms from_children
end MetricDistortion.Contracts.Geometry_CrossingMeasure
