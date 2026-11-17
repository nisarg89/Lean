import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Results_PolynomialCorollary
theorem from_children (h : Needs) : Statement := by
  obtain ⟨prog,K,hK,hprog⟩ := h.child_0
  refine ⟨prog,K*10^10,mul_pos hK (by norm_num), ?_⟩
  intro n m hn hm σ
  obtain ⟨Q,k,out,hrun,hhalt,hout,hdist,hcost⟩ :=
    hprog n m hn hm σ (1/100000) (by norm_num)
  refine ⟨Q,k,out,hrun,hhalt,hout,?_,?_⟩
  · convert hdist using 1 <;> norm_num
  · have hbase : 0 ≤ (n : ℝ)*m^2 := by positivity
    unfold computationBound at hcost
    calc
      (k : ℝ) ≤ K*((n : ℝ)*m^2+(n : ℝ)^3*m*Real.log m/(1/100000)^2) := hcost
      _ ≤ (K*10^10)*((n : ℝ)*m^2+(n : ℝ)^3*m*Real.log m) := by
        have heq : (K*10^10)*((n : ℝ)*m^2+(n : ℝ)^3*m*Real.log m) =
            K*(10^10*((n : ℝ)*m^2)+10^10*((n : ℝ)^3*m*Real.log m)) := by ring
        rw [heq]
        apply mul_le_mul_of_nonneg_left _ hK.le
        norm_num <;> nlinarith
#print axioms from_children
end MetricDistortion.Contracts.Results_PolynomialCorollary
