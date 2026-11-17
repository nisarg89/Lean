import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_Program
theorem from_children (h : Needs) : Statement := by
  refine ⟨metricProgram, ?_, ?_⟩
  · intro n m hn hm σ ε hε
    obtain ⟨R,k,s,hpre,hstate,hk⟩ := h.child_6 n m hn hm σ ε
    obtain ⟨l,out,Q,hrun,hhalt,hout,halg,hl⟩ := h.child_7 n m hn hm σ ε hε R s hstate
    exact ⟨k+l,out,Q,h.child_5.1 metricProgram k l _ _ _ hpre hrun,hhalt,hout,halg⟩
  · refine ⟨2048,by norm_num,?_⟩
    intro n m hn hm σ ε hε
    obtain ⟨R,k,s,hpre,hstate,hk⟩ := h.child_6 n m hn hm σ ε
    obtain ⟨l,out,Q,hrun,hhalt,hout,halg,hl⟩ := h.child_7 n m hn hm σ ε hε R s hstate
    refine ⟨k+l,out,h.child_5.1 metricProgram k l _ _ _ hpre hrun,hhalt,?_⟩
    let N : ℕ := Nat.ceil (Real.log m/(2*(ε/(32*n))^2))
    have hm0 : 1 ≤ m := by omega
    have hn1 : 1 ≤ n := hn
    have hm2 : m ≤ m^2 := by nlinarith
    have hnm : m ≤ n*m^2 := le_trans hm2 (by nlinarith)
    have hb : k+l ≤ 2048*(n*m^2+n*m*N+1) := by
      change l ≤ 1024*(n*m*N+m+1) at hl
      nlinarith
    have hc : ((k+l : ℕ) : ℝ) ≤ (2048 : ℝ)*
        ((n : ℝ)*m^2+(n : ℝ)*m*(N : ℝ)+1) := by exact_mod_cast hb
    simpa only [loopBudget,N] using hc
#print axioms from_children
end MetricDistortion.Contracts.Computation_Program
