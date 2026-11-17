import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ScoreScan
theorem from_children (h : Needs) : Statement := by
  intro n m hn hm D hD σ P c hc
  have hstar := h.child_1.2 D hD
  have hcont : Continuous (phi D) := by
    have heq : phi D = phiStar := funext hstar.1
    rw [heq]
    unfold phiStar
    fun_prop
  have he (v : Fin n) : compare D (σ v) P c =
      (PhiStar (below (σ v) P c+P.val c)-PhiStar (below (σ v) P c))/P.val c := by
    rw [(h.child_0 m D (σ v) P c).2.1 hc]
    rw [← hstar.2.1, ← hstar.2.1]
    unfold Phi
    rw [intervalIntegral.integral_interval_sub_left
      (hcont.intervalIntegrable 0 _) (hcont.intervalIntegrable 0 _)]
  unfold score avg
  simp_rw [he]
  rw [← Finset.sum_div]
  field_simp
#print axioms from_children
end MetricDistortion.Contracts.Computation_ScoreScan
