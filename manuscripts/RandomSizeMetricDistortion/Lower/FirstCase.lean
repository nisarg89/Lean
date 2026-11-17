import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_FirstCase

theorem from_children (h : Needs) : Statement := by
  intro D hd
  let f : ℝ → ℝ := fun z => z*phi D (71/125)+(1-z)*phi D 1-mu D
  have hf : f 1 < 0 := by simpa [f] using sub_neg.mpr hd
  obtain ⟨z,hz,hzlt,hfz⟩ := h.child_2 f 1 (by norm_num) (by norm_num) (by fun_prop) hf
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hz1R : (z : ℝ) ≤ 1 := hzlt.le
  have hz1 : z ≤ 1 := by exact_mod_cast hz1R
  refine ⟨z,hz,hz1,?_⟩
  intro n hn σ hσ Q hQ
  obtain ⟨P,hP⟩ := h.child_5 125 (by norm_num) 1 ⟨by norm_num,le_rfl⟩
  have hform := h.child_4.2 n 125 71 hn (by norm_num) (by norm_num)
    z ⟨hzR,hz1R⟩ D σ hσ 1 ⟨by norm_num,le_rfl⟩ P hP
  norm_num at hform
  have hscore : score D σ P 0 < mu D := by
    dsimp [f] at hfz
    linarith
  have hmass := h.child_0 n 125 71 hn (by norm_num) (by norm_num)
    z ⟨hzR,hz1R⟩ D σ hσ 1 ⟨by norm_num,le_rfl⟩ P hP hscore Q hQ
  have hlower := h.child_1 n 125 71 hn (by norm_num) (by norm_num)
    z ⟨hzR,hz1R⟩ σ hσ Q
  have hcorr : (0 : ℝ) < (1-z)/z := div_pos (sub_pos.mpr hzlt) hzR
  have hcoef : (0 : ℝ) < 71/125+(1-z)/z := by linarith
  have hproduct : (71/125 : ℝ)+(1-z)/z ≤ (1-Q.val 0)*(71/125+(1-z)/z) := by
    nlinarith
  have hstrict : (267/125 : ℝ) < 1+2*(1-Q.val 0)*((71 : ℝ)/125+(1-z)/z) := by
    nlinarith
  apply lt_of_lt_of_le ?_ hlower
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2 hstrict

#print axioms from_children
end MetricDistortion.Contracts.Lower_FirstCase
