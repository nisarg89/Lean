import Voting.Stable.Contracts
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Analysis_IntegralMixture

theorem from_children (h : Needs) : Statement := by
  intro D b z hb hz hsum
  have hs : Summable (drawWeight D) := by
    simpa using (h.child_0 D 1 (by constructor <;> norm_num)).1
  have harg : ∀ s ∈ Ioc (0 : ℝ) 1, b+s*z ∈ Icc (0 : ℝ) 1 := by
    intro s hsm
    constructor
    · nlinarith [mul_nonneg hsm.1.le hz]
    · nlinarith [mul_le_mul_of_nonneg_right hsm.2 hz]
  have hi := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun k s => drawWeight D k*(b+s*z)^(k+1))
    (f := fun s => phi D (b+s*z)) (fun k _ => drawWeight D k)
    (fun k => (show Continuous (fun s : ℝ => drawWeight D k*(b+s*z)^(k+1)) by
      fun_prop).aestronglyMeasurable)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsm
      have hn := (h.child_0 D (b+s*z) (harg s hsm)).2 k
      simpa only [Real.norm_eq_abs,abs_of_nonneg hn.1] using hn.2)
    (by exact Filter.Eventually.of_forall (fun _ => hs))
    (by simpa using (integrable_const (∑' k, drawWeight D k) :
      Integrable (fun _ : ℝ => ∑' k, drawWeight D k) (volume.restrict (Ioc (0 : ℝ) 1))))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsm
      exact (h.child_0 D (b+s*z) (harg s hsm)).1.hasSum)
  calc
    (∫ s in (0 : ℝ)..1, phi D (b+s*z)) = ∫ s in Ioc (0 : ℝ) 1, phi D (b+s*z) :=
      intervalIntegral.integral_of_le zero_le_one
    _ = ∑' k, ∫ s in Ioc (0 : ℝ) 1, drawWeight D k*(b+s*z)^(k+1) := hi.tsum_eq.symm
    _ = ∑' k, drawWeight D k*(∫ s in (0 : ℝ)..1, (b+s*z)^(k+1)) := by
      apply tsum_congr
      intro k
      rw [intervalIntegral.integral_of_le zero_le_one,integral_const_mul]

#print axioms from_children
end MetricDistortion.Contracts.Analysis_IntegralMixture
