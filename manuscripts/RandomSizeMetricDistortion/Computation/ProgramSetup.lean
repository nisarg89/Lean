import RandomSizeMetricDistortion.Statements
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramSetup

private theorem constants_of_reals {ε : ℝ} {s t : MachineState}
    (hr : t.reals = s.reals) (hc : ProgramConstants ε s) : ProgramConstants ε t := by
  unfold ProgramConstants at hc ⊢
  rw [hr]
  exact hc

private def chargedTick (s : MachineState) : MachineState :=
  (step metricProgram s).getD s

private def chargedReplay : ℕ → MachineState → MachineState
  | 0,s => s
  | k+1,s => chargedReplay k (chargedTick s)

private theorem chargedReplay_trace (k : ℕ) (s : MachineState)
    (hs : ∀ j < k, ∃ t, step metricProgram (chargedReplay j s) = some t) :
    Runs metricProgram k s (chargedReplay k s) := by
  induction k generalizing s with
  | zero => exact Runs.zero s
  | succ k ih =>
    obtain ⟨t,ht⟩ := hs 0 (by omega)
    change step metricProgram s = some t at ht
    have he : chargedTick s = t := by simp [chargedTick,ht]
    change Runs metricProgram (k+1) s (chargedReplay k (chargedTick s))
    apply Runs.succ (show step metricProgram s = some (chargedTick s) by simpa [he] using ht)
    apply ih
    intro j hj
    exact hs (j+1) (by omega)

private theorem startup_trace (n m : ℕ) (σ : Profile n m) (ε : ℝ) :
    Runs metricProgram 12 (inputState σ ε) (chargedReplay 12 (inputState σ ε)) := by
  apply chargedReplay_trace
  intro j hj
  interval_cases j <;>
    simp [chargedReplay,chargedTick,step,metricProgram,inputState]

private theorem startup_spec (n m : ℕ) (σ : Profile n m) (ε : ℝ) :
    let s := chargedReplay 12 (inputState σ ε)
    s.pc = 12 ∧ s.naturals 0 = n ∧ s.naturals 1 = m ∧
      s.naturals 2 = 0 ∧ s.naturals 3 = 1 ∧ s.naturals 4 = 0 ∧
      s.naturals 8 = 0 ∧ ProgramConstants ε s ∧
      s.memory = (inputState σ ε).memory ∧
      s.naturalMemory = (inputState σ ε).naturalMemory := by
  norm_num [chargedReplay,chargedTick,step,metricProgram,inputState,ProgramConstants]

private def LengthInvariant (n m : ℕ) (reference s : MachineState) : Prop :=
  s.pc = 12 ∧ s.naturals 0 = n ∧ s.naturals 1 = m ∧
  s.naturals 2 = 0 ∧ s.naturals 3 = 1 ∧ s.naturals 8 ≤ n ∧
  s.naturals 4 = s.naturals 8*m ∧ s.reals = reference.reals ∧
  s.memory = reference.memory ∧ s.naturalMemory = reference.naturalMemory ∧
  ∀ a, a ≠ 4 → a ≠ 8 → s.naturals a = reference.naturals a

private def LengthDone (n m : ℕ) (reference s : MachineState) : Prop :=
  s.pc = 16 ∧ s.naturals 4 = n*m ∧ s.naturals 8 = n ∧
  s.reals = reference.reals ∧ s.memory = reference.memory ∧
  s.naturalMemory = reference.naturalMemory ∧
  ∀ a, a ≠ 4 → a ≠ 8 → s.naturals a = reference.naturals a

private theorem length_loop (hloop : Computation_RunRules.Statement)
    (n m : ℕ) (reference s : MachineState) (hs : LengthInvariant n m reference s) :
    ∃ k t, Runs metricProgram k s t ∧ LengthDone n m reference t ∧
      k ≤ 4*(n-s.naturals 8+1) := by
  apply hloop.2 metricProgram (LengthInvariant n m reference)
    (LengthDone n m reference) (fun u => n-u.naturals 8) 4 ?_ s hs
  intro u hu
  obtain ⟨hpc,hn,hm,hz,ho,hbound,hL,hr,hmem,hnmem,hframe⟩ := hu
  by_cases hstop : n ≤ u.naturals 8
  · have heq : u.naturals 8 = n := le_antisymm hbound hstop
    let t : MachineState := {u with pc := 16}
    have hstep : step metricProgram u = some t := by
      simp [step,metricProgram,hpc,hn,hstop,t]
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by norm_num,Or.inl ?_⟩
    exact ⟨rfl,hL.trans (congrArg (fun x => x*m) heq),heq,hr,hmem,hnmem,hframe⟩
  · have hgo : u.naturals 8 < n := Nat.lt_of_not_ge hstop
    let t : MachineState :=
      { u with
        pc := 12
        naturals := Function.update (Function.update u.naturals 4 (u.naturals 4+m))
          8 (u.naturals 8+1) }
    have hreplay : chargedReplay 4 u = t := by
      simp [chargedReplay,chargedTick,step,metricProgram,hpc,hn,hm,ho,hstop,t]
    have hrun : Runs metricProgram 4 u t := by
      rw [← hreplay]
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;>
        simp [chargedReplay,chargedTick,step,metricProgram,hpc,hn,hstop]
    refine ⟨4,t,hrun,le_rfl,Or.inr ⟨?_,?_⟩⟩
    · refine ⟨rfl,?_,?_,?_,?_,?_,?_,hr,hmem,hnmem,?_⟩
      · simpa [t] using hn
      · simpa [t] using hm
      · simpa [t] using hz
      · simpa [t] using ho
      · change u.naturals 8+1 ≤ n
        omega
      · simp [t,hL,Nat.add_mul]
      · intro a ha4 ha8
        simpa [t,ha4,ha8] using hframe a ha4 ha8
    · change n-(u.naturals 8+1) < n-u.naturals 8
      omega

private theorem length_from_startup (hloop : Computation_RunRules.Statement)
    (n m : ℕ) (σ : Profile n m) (ε : ℝ) :
    ∃ k t, Runs metricProgram k (inputState σ ε) t ∧
      LengthDone n m (chargedReplay 12 (inputState σ ε)) t ∧
      k ≤ 12+4*(n+1) := by
  let s := chargedReplay 12 (inputState σ ε)
  have hstart := startup_spec n m σ ε
  change s.pc = 12 ∧ _ at hstart
  obtain ⟨hpc,hn,hm,hz,ho,hL,hv,hconst,hmem,hnmem⟩ := hstart
  have hinv : LengthInvariant n m s s := by
    refine ⟨hpc,hn,hm,hz,ho,?_,?_,rfl,rfl,rfl,?_⟩
    · rw [hv]
      omega
    · rw [hL,hv,zero_mul]
    · intro a ha4 ha8
      rfl
  obtain ⟨k,t,hk,hdone,hcost⟩ := length_loop hloop n m s s hinv
  refine ⟨12+k,t,hloop.1 metricProgram 12 k (inputState σ ε) s t
    (startup_trace n m σ ε) hk,hdone,?_⟩
  have hcost' : k ≤ 4*(n+1) := hcost.trans
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.sub_le n (s.naturals 8)) 1))
  omega

private theorem input_rank {n m : ℕ} (hm : 0 < m) (σ : Profile n m) (ε : ℝ)
    (v : Fin n) (c : Fin m) :
    (inputState σ ε).naturalMemory (v.val*m+c.val) = ((σ v) c).val := by
  have hdiv : (v.val*m+c.val)/m = v.val := by
    rw [Nat.mul_comm v.val m,Nat.mul_add_div hm,Nat.div_eq_of_lt c.isLt,Nat.add_zero]
  have hmod : (v.val*m+c.val)%m = c.val := by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt c.isLt]
  simp [inputState,hm,hdiv,hmod,v.isLt]

private theorem setup_bases (n m : ℕ) (σ : Profile n m) (ε : ℝ)
    (s : MachineState)
    (hs : LengthDone n m (chargedReplay 12 (inputState σ ε)) s) :
    let t := chargedReplay 11 s
    Runs metricProgram 11 s t ∧ t.pc = 27 ∧ t.naturals 8 = 0 ∧ t.naturals 10 = 0 ∧
      ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t := by
  let reference := chargedReplay 12 (inputState σ ε)
  obtain ⟨hpc,hL,hv,hr,hmem,hnmem,hframe⟩ := hs
  have hstart := startup_spec n m σ ε
  obtain ⟨hpc0,hn0,hm0,hz0,ho0,hL0,hv0,hconst0,hmem0,hnmem0⟩ := hstart
  have hn : s.naturals 0 = n := (hframe 0 (by norm_num) (by norm_num)).trans hn0
  have hm : s.naturals 1 = m := (hframe 1 (by norm_num) (by norm_num)).trans hm0
  have hz : s.naturals 2 = 0 := (hframe 2 (by norm_num) (by norm_num)).trans hz0
  have ho : s.naturals 3 = 1 := (hframe 3 (by norm_num) (by norm_num)).trans ho0
  let t := chargedReplay 11 s
  have ht : Runs metricProgram 11 s t := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hpc]
  refine ⟨ht,?_,?_,?_,?_,?_,?_⟩
  · norm_num [t,chargedReplay,chargedTick,step,metricProgram,hpc]
  · norm_num [t,chargedReplay,chargedTick,step,metricProgram,hpc]
  · norm_num [t,chargedReplay,chargedTick,step,metricProgram,hpc]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals norm_num [t,chargedReplay,chargedTick,step,metricProgram,hpc,hn,hm,hz,ho,hL] <;> ring
  · have htR : t.reals = s.reals := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hpc]
    have hconst : ProgramConstants ε s := by
      exact constants_of_reals hr hconst0
    exact constants_of_reals htR hconst
  · intro v c
    have htM : t.naturalMemory = (inputState σ ε).naturalMemory := by
      have htM' : t.naturalMemory = s.naturalMemory := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hpc]
      exact htM'.trans (hnmem.trans hnmem0)
    rw [htM]
    exact input_rank (Nat.zero_lt_of_lt c.isLt) σ ε v c

private theorem setup_complete (hloop : Computation_RunRules.Statement)
    (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m) (σ : Profile n m) (ε : ℝ) :
    ∃ k t, Runs metricProgram k (inputState σ ε) t ∧
      t.pc = 27 ∧ t.naturals 8 = 0 ∧ t.naturals 10 = 0 ∧
      ProgramBases n m t ∧ ProgramConstants ε t ∧ ProgramRanks σ t ∧
      k ≤ 32*n*m := by
  obtain ⟨k,s,hk,hdone,hcost⟩ := length_from_startup hloop n m σ ε
  have hbase := setup_bases n m σ ε s hdone
  let t := chargedReplay 11 s
  obtain ⟨ht,hpc,hv,hrow,hbases,hconst,hranks⟩ := hbase
  refine ⟨k+11,t,hloop.1 metricProgram k 11 (inputState σ ε) s t hk ht,
    hpc,hv,hrow,hbases,hconst,hranks,?_⟩
  have hnm : n*2 ≤ n*m := Nat.mul_le_mul_left n hm
  nlinarith

theorem from_children (h : Needs) : Statement := by
  exact setup_complete h.child_0

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramSetup
