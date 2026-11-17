import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramSingleton

private def chunk : ℕ → MachineState → Option MachineState
  | 0,s => some s
  | k+1,s => (step metricProgram s).bind (chunk k)
private theorem chunk_sound {k : ℕ} {s t : MachineState}
    (he : chunk k s=some t) : Runs metricProgram k s t := by
  induction k generalizing s with
  | zero => simp only [chunk,Option.some.injEq] at he; subst t; exact Runs.zero s
  | succ k ih =>
    cases hs : step metricProgram s with
    | none => simp [chunk,hs] at he
    | some u => apply Runs.succ hs; apply ih; simpa only [chunk,hs,Option.bind_some] using he

private def cleared (mem : ℕ → ℝ) (i : ℕ) : ℕ → ℝ :=
  fun a => if a < i then 0 else mem a
private theorem cleared_zero (mem : ℕ → ℝ) : cleared mem 0=mem := by
  funext a; simp [cleared]
private theorem cleared_update (mem : ℕ → ℝ) (i : ℕ) :
    Function.update (cleared mem i) i 0=cleared mem (i+1) := by
  funext a
  by_cases hai : a=i
  · subst a; simp [cleared]
  · have he : a < i+1 ↔ a < i := by omega
    simp [cleared,hai,he]
private def clearState (s : MachineState) (i : ℕ) : MachineState :=
  {s with pc := 102, naturals := Function.update s.naturals 6 i, memory := cleared s.memory i}
private def clearExit (s : MachineState) (m : ℕ) : MachineState :=
  {s with pc := 106, naturals := Function.update s.naturals 6 m, memory := cleared s.memory m}
private def finalState (s : MachineState) (m e : ℕ) : MachineState :=
  {s with pc := 226, naturals := Function.update (Function.update s.naturals 6 m) 12 e, memory := Function.update (cleared s.memory m) e 1}

private theorem clear_step (s : MachineState) (m i : ℕ) (hm : s.naturals 1=m)
    (h1 : s.naturals 3=1) (hz : s.reals 1=0) (hi : i < m) :
    Runs metricProgram 4 (clearState s i) (clearState s (i+1)) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,clearState,hm,h1,hz,not_le.mpr hi,cleared_update]
private theorem clear_done (s : MachineState) (m : ℕ) (hm : s.naturals 1=m) :
    Runs metricProgram 1 (clearState s m) (clearExit s m) := by
  apply chunk_sound
  simp [chunk,step,metricProgram,clearState,clearExit,hm]

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε R s hs hR
  rcases hs with ⟨hpc,hRm,hLayout,hConst,hMemory⟩
  rcases hLayout with ⟨hn0,hm1,hn2,hn3,hn4,hn5,hn20,hn21,hn22,hn23,hn24,hn26,hn27,hn28,hn29⟩
  rcases hConst with ⟨heps,hz,hOne,h20,h21,h22,h36,h37,h38⟩
  rcases hMemory with ⟨hkeep,hmap,hreverse,hranks⟩
  let j0 : Fin R.count := ⟨0,R.count_pos⟩
  let e : Fin m := R.embed j0
  have hload : s.naturalMemory (s.naturals 22)=e.val := by
    simpa [hn22,j0,e] using hmap j0
  have hstart : Runs metricProgram 2 s (clearState s 0) := by
    apply chunk_sound
    simp [chunk,step,metricProgram,hpc,hn5,hR,hn3,clearState,cleared_zero]
  have run : ∀ b i : ℕ, b=m-i → i ≤ m →
      Runs metricProgram (4*b+1) (clearState s i) (clearExit s m) := by
    intro b
    induction b with
    | zero =>
      intro i hb hi
      have him : i=m := by omega
      rw [him]
      exact clear_done s m hm1
    | succ b ih =>
      intro i hb hi
      have him : i < m := by omega
      have ht := clear_step s m i hm1 hn3 hz him
      have hu := ih (i+1) (by omega) (by omega)
      have hc := h.child_0.1 metricProgram 4 (4*b+1) _ _ _ ht hu
      convert hc using 1 <;> omega
  have hclear : Runs metricProgram (4*m+1) (clearState s 0) (clearExit s m) := by
    exact run m 0 (by omega) (by omega)
  have hfinish : Runs metricProgram 3 (clearExit s m) (finalState s m e.val) := by
    apply chunk_sound
    simp [chunk,step,metricProgram,clearExit,finalState,hload,hOne]
  have htrace := h.child_0.1 metricProgram (2+(4*m+1)) 3 s (clearExit s m) (finalState s m e.val)
    (h.child_0.1 metricProgram 2 (4*m+1) _ _ _ hstart hclear) hfinish
  let Q : Lottery m := ⟨Pi.single e 1, by
    refine ⟨?_,by simp⟩
    intro c
    by_cases hc : c=e
    · subst c; simp
    · simp [Pi.single_apply,hc,Ne.symm hc]⟩
  let Q' : Lottery R.count := ⟨Pi.single j0 1, by
    refine ⟨?_,by simp⟩
    intro c
    by_cases hc : c=j0
    · subst c; simp
    · simp [Pi.single_apply,hc,Ne.symm hc]⟩
  have hlift : Lifts R Q' Q := by
    constructor
    · intro j
      have hj : j=j0 := by
        apply Fin.ext
        have hjlt := j.isLt
        have hj0 : j0.val=0 := rfl
        have hjlt' : j.val < 1 := lt_of_lt_of_eq hjlt hR
        omega
      subst j
      simp [Q,Q',e]
    · intro c hc
      have hce : c≠e := by
        intro he
        apply hc
        exact ⟨j0,he.symm⟩
      simp [Q,Pi.single_apply,hce,Ne.symm hce]
  refine ⟨4*m+6,finalState s m e.val,Q,?_,?_,?_,?_,rfl⟩
  · convert htrace using 1 <;> omega
  · simp [Halted,metricProgram,finalState]
  · intro c
    change Function.update (cleared s.memory m) e.val 1 c.val= (Pi.single e (1 : ℝ) : Fin m → ℝ) c
    by_cases hc : c=e
    · subst c; simp
    · have hval : c.val≠e.val := fun he => hc (Fin.ext he)
      simp [cleared,c.isLt,hval,Q,Pi.single_apply,hc,Ne.symm hc]
  · exact ⟨R,Q',hlift,Or.inl hR⟩

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramSingleton
