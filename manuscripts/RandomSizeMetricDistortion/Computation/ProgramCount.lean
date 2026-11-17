import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramCount

private def chunk : ℕ → MachineState → Option MachineState
  | 0,s => some s
  | k+1,s => (step metricProgram s).bind (chunk k)

private theorem chunk_sound {k : ℕ} {s t : MachineState}
    (he : chunk k s = some t) : Runs metricProgram k s t := by
  induction k generalizing s with
  | zero => simp only [chunk,Option.some.injEq] at he; subst t; exact Runs.zero s
  | succ k ih =>
    cases hstep : step metricProgram s with
    | none => simp [chunk,hstep] at he
    | some u =>
      apply Runs.succ hstep
      apply ih
      simpa only [chunk,hstep,Option.bind_some] using he

private def advance (s : MachineState) : MachineState :=
  {s with pc := 118, naturals := Function.update s.naturals 17 (s.naturals 17+1), reals := Function.update (Function.update s.reals 9 (Real.exp (s.reals 8))) 8 (s.reals 8+s.reals 4)}
private def finish (s : MachineState) : MachineState :=
  {s with pc := 123, reals := Function.update s.reals 9 (Real.exp (s.reals 8))}

private theorem continue_trace (s : MachineState) (hpc : s.pc=118)
    (h1 : s.naturals 3=1) (htest : ¬s.reals 6 ≤ Real.exp (s.reals 8)) :
    Runs metricProgram 5 s (advance s) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,hpc,h1,htest,advance,applyRealOp]

private theorem finish_trace (s : MachineState) (hpc : s.pc=118)
    (htest : s.reals 6 ≤ Real.exp (s.reals 8)) :
    Runs metricProgram 2 s (finish s) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,hpc,htest,finish,applyRealOp]

private theorem threshold (r : ℕ) (hr : 2 ≤ r) (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    (r : ℝ) ≤ Real.exp (2*δ^2*k) ↔ Nat.ceil (Real.log r/(2*δ^2)) ≤ k := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0<r by omega)
  rw [Nat.ceil_le,div_le_iff₀ (by positivity : 0<2*δ^2),← Real.log_le_iff_le_exp hr0]
  rw [mul_comm (k : ℝ) (2*δ^2)]

theorem from_children (h : Needs) : Statement := by
  intro r hr δ hδ
  dsimp only
  let N := Nat.ceil (Real.log r/(2*δ^2))
  have run : ∀ b k : ℕ, b=N-k → k≤N → ∀ s : MachineState,
      s.pc=118 → s.naturals 3=1 → s.naturals 17=k →
      s.reals 4=2*δ^2 → s.reals 6=r → s.reals 8=2*δ^2*k →
      ∃ t, Runs metricProgram (5*b+2) s t ∧ t.pc=123 ∧ t.naturals 17=N ∧
        t.reals 8=2*δ^2*N ∧ t.naturalMemory=s.naturalMemory ∧ t.memory=s.memory ∧
        (∀ i, i≠17 → t.naturals i=s.naturals i) ∧
        (∀ i, i≠8 → i≠9 → t.reals i=s.reals i) := by
    intro b
    induction b with
    | zero =>
      intro k hb hk s hpc h1 hkreg ha hrr hz
      have hkN : k=N := by omega
      have htest : s.reals 6 ≤ Real.exp (s.reals 8) := by
        rw [hrr,hz,hkN]
        exact (threshold r hr δ hδ N).2 le_rfl
      refine ⟨finish s,finish_trace s hpc htest,rfl,?_,?_,rfl,rfl,?_,?_⟩
      · exact hkreg.trans hkN
      · simpa [finish,hkN] using hz
      · intro i hi; rfl
      · intro i hi8 hi9; simp [finish,hi9]
    | succ b ih =>
      intro k hb hk s hpc h1 hkreg ha hrr hz
      have hkN : k<N := by omega
      have htest : ¬s.reals 6 ≤ Real.exp (s.reals 8) := by
        rw [hrr,hz,threshold r hr δ hδ k]
        omega
      have htrace := continue_trace s hpc h1 htest
      have ha' : (advance s).reals 4=2*δ^2 := by simpa [advance] using ha
      have hrr' : (advance s).reals 6=(r : ℝ) := by simpa [advance] using hrr
      have hz' : (advance s).reals 8=2*δ^2*((k+1 : ℕ) : ℝ) := by
        change s.reals 8+s.reals 4=2*δ^2*((k+1 : ℕ) : ℝ)
        rw [hz,ha]
        push_cast
        ring
      obtain ⟨t,ht,hpc',hN',hzN,hnmem,hmem,hnframe,hrframe⟩ :=
        ih (k+1) (by omega) (by omega) (advance s) rfl
          (by simpa [advance] using h1) (by simp [advance,hkreg]) ha' hrr' hz'
      refine ⟨t,?_,hpc',hN',hzN,hnmem,hmem,?_,?_⟩
      · have hc := h.child_0.1 metricProgram 5 (5*b+2) s (advance s) t htrace ht
        convert hc using 1 <;> omega
      · intro i hi
        rw [hnframe i hi]
        simp [advance,hi]
      · intro i hi8 hi9
        rw [hrframe i hi8 hi9]
        simp [advance,hi8,hi9]
  intro s hpc h1 hk hzero ha hrr hz
  have hz' : s.reals 8=2*δ^2*(0 : ℕ) := by simpa using hz
  simpa only [Nat.sub_zero] using run N 0 (by omega) (by omega) s hpc h1 hk ha hrr hz'

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramCount
