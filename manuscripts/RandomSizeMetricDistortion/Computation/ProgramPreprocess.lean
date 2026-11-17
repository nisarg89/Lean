import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramPreprocess

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε
  obtain ⟨k1,s1,hr1,hpc1,hv1,hrow1,hb1,hc1,hin1,hk1⟩ := h.child_3 n m hn hm σ ε
  obtain ⟨k2,s2,hr2,hpc2,hb2,hc2,hin2,hi2,hk2⟩ :=
    h.child_4 n m hn hm σ ε s1 hpc1 hv1 hrow1 hb1 hc1 hin1
  obtain ⟨k3,s3,hr3,hpc3,hb3,hc3,hin3,hi3,hkeep3,hk3⟩ :=
    h.child_5 n m hn hm σ ε s2 hpc2 hb2 hc2 hin2 hi2
  obtain ⟨r,k4,s4,hr4,hpc4,hb4,hc4,hin4,hi4,hkeep4,hmap4,hk4⟩ :=
    h.child_6 n m hn hm σ ε s3 hpc3 hb3 hc3 hin3 hi3 hkeep3
  obtain ⟨R,k5,s5,hr5,hcount,hpre,hk5⟩ :=
    h.child_7 n m hn hm σ ε r s4 hpc4 hb4 hc4 hin4 hi4 hkeep4 hmap4
  have hr12 := h.child_2.1 metricProgram k1 k2 (inputState σ ε) s1 s2 hr1 hr2
  have hr123 := h.child_2.1 metricProgram (k1+k2) k3 (inputState σ ε) s2 s3 hr12 hr3
  have hr1234 := h.child_2.1 metricProgram (k1+k2+k3) k4 (inputState σ ε) s3 s4 hr123 hr4
  have hr12345 := h.child_2.1 metricProgram (k1+k2+k3+k4) k5 (inputState σ ε) s4 s5 hr1234 hr5
  refine ⟨R,k1+k2+k3+k4+k5,s5,hr12345,hpre,?_⟩
  have hnm : n*m ≤ n*m^2 := by
    exact Nat.mul_le_mul_left n (by nlinarith : m ≤ m^2)
  have hm0 : m ≤ n*m := by nlinarith
  nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramPreprocess
