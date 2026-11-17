import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Lower_SecondCase

theorem from_children (h : Needs) : Statement := by
  intro D hd
  let z0 : ℝ := 1625/2814
  let f : ℝ → ℝ := fun z =>
    z*(Phi D (7/26)-Phi D (1/52))+(1-z)*(mu D-Phi D (3/4))-mu D/4
  have hgap : Phi D (7/26)+(71/125-7/26)*mu D <
      Phi D (1/52)+((71/125-1/52)/(3/4))*Phi D (3/4) := by
    have ha := h.child_1 D
    have hb := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 71/125-7/26)
    linarith
  have hf : f z0 < 0 := by
    dsimp [f,z0]
    norm_num at hgap ⊢
    linarith
  obtain ⟨z,hz,hzlt,hfz⟩ := h.child_4 f z0 (by norm_num [z0])
    (by norm_num [z0]) (by fun_prop) hf
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hzlt1 : (z : ℝ) < 1 := hzlt.trans (by norm_num [z0])
  have hz1 : z ≤ 1 := by exact_mod_cast hzlt1.le
  refine ⟨z,hz,hz1,?_⟩
  intro n hn σ hσ Q hQ
  obtain ⟨P,hP⟩ := h.child_5 39 (by norm_num) (3/4) ⟨by norm_num,by norm_num⟩
  have hform := h.child_0.1 n 39 1 hn (by norm_num) (by norm_num)
    z ⟨hzR,hzlt1.le⟩ D σ hσ (3/4) ⟨by norm_num,by norm_num⟩ P hP
  norm_num at hform
  have hscore : score D σ P 0 < mu D := by
    dsimp [f] at hfz
    linarith
  have hmass := h.child_2 n 39 1 hn (by norm_num) (by norm_num)
    z ⟨hzR,hzlt1.le⟩ D σ hσ (3/4) ⟨by norm_num,by norm_num⟩ P hP hscore Q hQ
  have hlower := h.child_3 n 39 1 hn (by norm_num) (by norm_num)
    z ⟨hzR,hzlt1.le⟩ σ hσ Q
  have hcalmul : (71/125 : ℝ)*z < (3/4 : ℝ)*((1/39 : ℝ)*z+1-z) := by
    dsimp [z0] at hzlt
    nlinarith
  have hcal : (71/125 : ℝ) < (3/4 : ℝ)*((1/39 : ℝ)+(1-z)/z) := by
    have he : (3/4 : ℝ)*((1/39 : ℝ)+(1-z)/z) =
        ((3/4 : ℝ)*((1/39 : ℝ)*z+1-z))/z := by
      field_simp
      <;> ring
    rw [he]
    exact (lt_div_iff₀ hzR).2 hcalmul
  have hcoef : (0 : ℝ) < (1/39 : ℝ)+(1-z)/z := by
    nlinarith
  have hproduct : (3/4 : ℝ)*((1/39 : ℝ)+(1-z)/z) ≤
      (1-Q.val 0)*((1/39 : ℝ)+(1-z)/z) := by
    nlinarith
  have hstrict : (267/125 : ℝ) < 1+2*(1-Q.val 0)*((1 : ℝ)/39+(1-z)/z) := by
    nlinarith
  apply lt_of_lt_of_le ?_ hlower
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).2
  convert hstrict using 1 <;> norm_num

#print axioms from_children
end MetricDistortion.Contracts.Lower_SecondCase
