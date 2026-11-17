import RandomSizeMetricDistortion.Statements
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramMW

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε hε R s hpre
  by_cases hsingle : R.count=1
  · obtain ⟨k,out,Q,hr,hhalt,hout,halg,hk⟩ := h.child_6 n m hn hm σ ε R s hpre hsingle
    refine ⟨k,out,Q,hr,hhalt,hout,halg,?_⟩
    rw [hk]
    omega
  have hR2 : 2 ≤ R.count := by have := R.count_pos; omega
  have hδ : 0 < ε/(32*(n : ℝ)) := div_pos hε.1 (by positivity)
  let N := Nat.ceil (Real.log R.count/(2*(ε/(32*n))^2))
  let M := Nat.ceil (Real.log m/(2*(ε/(32*n))^2))
  have hN : 0 < N := (h.child_3 R.count hR2 (ε/(32*n)) hδ).1
  obtain ⟨D,hD,P,htraj,hpos,k,u,hinit,hinv,hk⟩ := h.child_7 n m hn hm σ ε hε R s hpre hR2
  have counter (i : ℕ) (t : MachineState) (hi : ProgramRoundInvariant R ε P i t) :
      t.naturals 18=i := hi.2.2.2.2.2.1
  let Inv : MachineState → Prop := fun t => ∃ i, i ≤ N ∧ ProgramRoundInvariant R ε P i t
  let Done : MachineState → Prop := ProgramRoundInvariant R ε P N
  let rank : MachineState → ℕ := fun t => N-t.naturals 18
  have hstep : ∀ t, Inv t → ∃ k out, Runs metricProgram k t out ∧ k ≤ 256*n*R.count ∧
      (Done out ∨ (Inv out ∧ rank out < rank t)) := by
    intro t ht
    obtain ⟨i,hi,hIt⟩ := ht
    by_cases hiN : i=N
    · refine ⟨0,t,Runs.zero t,by omega,Or.inl ?_⟩
      simpa [Done,hiN] using hIt
    have hiN' : i < N := by omega
    obtain ⟨k,out,hr,hout,hk⟩ := h.child_8 n m hn hm σ R hR2 ε hε D hD P htraj hpos i t hIt hiN'
    refine ⟨k,out,hr,hk,Or.inr ⟨⟨i+1,by omega,hout⟩,?_⟩⟩
    have hit := counter i t hIt
    have hiout := counter (i+1) out hout
    dsimp [rank]
    omega
  obtain ⟨l,v,hloop,hDone,hl⟩ :=
    h.child_0.2 metricProgram Inv Done rank (256*n*R.count) hstep u ⟨0,by omega,hinv⟩
  obtain ⟨j,out,Q,hfinish,hhalt,hout,halg,hj⟩ :=
    h.child_9 n m hn hm σ R ε D hD P htraj hN v hDone
  refine ⟨k+l+j,out,Q,?_,hhalt,hout,halg,?_⟩
  · exact h.child_0.1 metricProgram (k+l) j _ _ _
      (h.child_0.1 metricProgram k l _ _ _ hinit hloop) hfinish
  · have hrm : R.count ≤ m := hpre.2.1
    have hNM : N ≤ M := by
      apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right
      · apply Real.log_le_log
        · exact_mod_cast R.count_pos
        · exact_mod_cast hrm
      · positivity
    have hcounter := counter 0 u hinv
    have hl' : l ≤ 256*n*R.count*(N+1) := by simpa [rank,hcounter] using hl
    have hnm : n*R.count ≤ n*m := Nat.mul_le_mul_left n hrm
    have hloopbound : l ≤ 512*n*m*M := by
      calc
        l ≤ 256*(n*R.count)*(N+1) := by simpa [Nat.mul_assoc] using hl'
        _ ≤ 256*(n*m)*(2*N) := Nat.mul_le_mul (Nat.mul_le_mul_left 256 hnm) (by omega)
        _ = 512*n*m*N := by ring
        _ ≤ 512*n*m*M := Nat.mul_le_mul_left _ hNM
    have hnmpos : 0 < n*m := Nat.mul_pos hn (by omega)
    have hNbound : N ≤ n*m*M := le_trans hNM (by nlinarith)
    change k ≤ 16*(N+m+1) at hk
    change k+l+j ≤ 1024*(n*m*M+m+1)
    nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramMW
