import RandomSizeMetricDistortion.Statements
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramInverse

@[ext] private theorem state_ext {s t : MachineState}
    (hpc : s.pc = t.pc) (hn : s.naturals = t.naturals)
    (hr : s.reals = t.reals) (hm : s.memory = t.memory)
    (hnm : s.naturalMemory = t.naturalMemory) : s = t := by
  cases s
  cases t
  simp_all

private def chargedTick (s : MachineState) : MachineState := (step metricProgram s).getD s
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

private theorem row_address_lt {n m : ℕ} (v : Fin n) (c : Fin m) :
    v.val*m+c.val < n*m := by
  have hh : v.val*m+m ≤ n*m := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m (Nat.succ_le_of_lt v.isLt)
  omega

private structure Core {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) : Prop where
  bases : ProgramBases n m s
  constants : ProgramConstants ε s
  ranks : ProgramRanks σ s

private def Part {n m : ℕ} (σ : Profile n m) (v : Fin n) (cut : ℕ)
    (s : MachineState) : Prop :=
  ∀ c : Fin m, c.val < cut → s.naturalMemory (n*m+v.val*m+((σ v) c).val) = c.val
private def Rows {n m : ℕ} (σ : Profile n m) (cut : ℕ) (s : MachineState) : Prop :=
  ∀ v : Fin n, v.val < cut → Part σ v m s

private structure InnerInv {n m : ℕ} (σ : Profile n m) (ε : ℝ) (v : Fin n)
    (s : MachineState) : Prop where
  pc : s.pc = 29
  core : Core σ ε s
  voter : s.naturals 8 = v.val
  row : s.naturals 10 = v.val*m
  bound : s.naturals 6 ≤ m
  rows : Rows σ v.val s
  part : Part σ v (s.naturals 6) s
private structure InnerDone {n m : ℕ} (σ : Profile n m) (ε : ℝ) (v : Fin n)
    (s : MachineState) : Prop where
  pc : s.pc = 37
  core : Core σ ε s
  voter : s.naturals 8 = v.val
  row : s.naturals 10 = v.val*m
  candidate : s.naturals 6 = m
  rows : Rows σ v.val s
  part : Part σ v m s

private theorem inverse_inner_body {n m : ℕ} (σ : Profile n m) (ε : ℝ) (v : Fin n)
    (s : MachineState) (hs : InnerInv σ ε v s) (hc : s.naturals 6 < m) :
    ∃ t, Runs metricProgram 8 s t ∧ InnerInv σ ε v t ∧
      t.naturals 6 = s.naturals 6+1 := by
  let c : Fin m := ⟨s.naturals 6,hc⟩
  let r := ((σ v) c).val
  let w := n*m+v.val*m+r
  let t : MachineState :=
    { s with
      pc := 29
      naturals := Function.update (Function.update (Function.update s.naturals 11 w) 13 r)
        6 (s.naturals 6+1)
      naturalMemory := Function.update s.naturalMemory w (s.naturals 6) }
  obtain ⟨hn,hM,hZ,hO,hL,hI,hK,hMap,hRev,hOrd,hPB,hTB,hAB,hSB⟩ := hs.core.bases
  have hnot : ¬ s.naturals 1 ≤ s.naturals 6 := by rw [hM]; omega
  have hnotM : ¬ m ≤ s.naturals 6 := by omega
  have hrank : s.naturalMemory (s.naturals 10+s.naturals 6) = r := by
    rw [hs.row]
    exact hs.core.ranks v c
  have hrank' : s.naturalMemory (v.val*m+s.naturals 6) = r := hs.core.ranks v c
  have hreplay : chargedReplay 8 s = t := by
    apply state_ext
    · simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnotM,hM,hO,hI,
        hs.row,hrank,hrank',c,r,w,t]
    · funext a
      by_cases h6 : a = 6 <;> by_cases h11 : a = 11 <;> by_cases h13 : a = 13 <;>
        simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnotM,hM,hO,hI,
          hs.row,hrank,hrank',c,r,w,t,Function.update_apply,h6,h11,h13]
    · simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnotM,hM,hO,hI,
        hs.row,hrank,hrank',c,r,w,t]
    · simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnotM,hM,hO,hI,
        hs.row,hrank,hrank',c,r,w,t]
    · simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnotM,hM,hO,hI,
        hs.row,hrank,hrank',c,r,w,t]
  have hrun : Runs metricProgram 8 s t := by
    rw [← hreplay]
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hnot]
  have hcore : Core σ ε t := by
    refine ⟨?_,hs.core.constants,?_⟩
    · simpa [ProgramBases,t] using hs.core.bases
    · intro u d
      have hsmall := row_address_lt u d
      have hne : u.val*m+d.val ≠ w := by dsimp [w]; omega
      change Function.update s.naturalMemory w (s.naturals 6) (u.val*m+d.val) = _
      rw [Function.update_of_ne hne]
      exact hs.core.ranks u d
  refine ⟨t,hrun,?_,by simp [t]⟩
  refine ⟨rfl,hcore,by simpa [t] using hs.voter,by simpa [t] using hs.row,?_,?_,?_⟩
  · change s.naturals 6+1 ≤ m
    omega
  · intro u hu d hd
    have hsmall : u.val*m+((σ u) d).val < v.val*m :=
      row_address_lt (n := v.val) ⟨u.val,hu⟩ ((σ u) d)
    have hne : n*m+u.val*m+((σ u) d).val ≠ w := by dsimp [w]; omega
    change Function.update s.naturalMemory w (s.naturals 6)
      (n*m+u.val*m+((σ u) d).val) = d.val
    rw [Function.update_of_ne hne]
    exact hs.rows u hu d hd
  · intro d hd
    have hd' : d.val < s.naturals 6+1 := by simpa [t] using hd
    by_cases heq : d.val = s.naturals 6
    · have hdc : d = c := Fin.ext heq
      subst d
      change Function.update s.naturalMemory w (s.naturals 6) w = c.val
      simp [c]
    · have hprev : d.val < s.naturals 6 := by omega
      have hne : n*m+v.val*m+((σ v) d).val ≠ w := by
        intro he
        have hr : ((σ v) d).val = ((σ v) c).val := by dsimp [w,r] at he; omega
        have hdc : d = c := (σ v).injective (Fin.ext hr)
        have hval := congrArg Fin.val hdc
        dsimp [c] at hval
        omega
      change Function.update s.naturalMemory w (s.naturals 6)
        (n*m+v.val*m+((σ v) d).val) = d.val
      rw [Function.update_of_ne hne]
      exact hs.part d hprev

private theorem inverse_inner_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (v : Fin n)
    (s : MachineState) (hs : InnerInv σ ε v s) :
    ∃ k t, Runs metricProgram k s t ∧ InnerDone σ ε v t ∧
      k ≤ 8*(m-s.naturals 6+1) := by
  apply hloop.2 metricProgram (InnerInv σ ε v) (InnerDone σ ε v)
    (fun u => m-u.naturals 6) 8 ?_ s hs
  intro u hu
  have hM : u.naturals 1 = m := hu.core.bases.2.1
  by_cases hstop : m ≤ u.naturals 6
  · have heq : u.naturals 6 = m := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 37}
    have hstep : step metricProgram u = some t := by
      simp [step,metricProgram,hu.pc,hM,hstop,t]
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by norm_num,Or.inl ?_⟩
    exact ⟨rfl,⟨hu.core.bases,hu.core.constants,hu.core.ranks⟩,
      hu.voter,hu.row,heq,hu.rows,by simpa only [Part,heq,t] using hu.part⟩
  · have hgo : u.naturals 6 < m := Nat.lt_of_not_ge hstop
    obtain ⟨t,ht,hinv,hinc⟩ := inverse_inner_body σ ε v u hu hgo
    refine ⟨8,t,ht,le_rfl,Or.inr ⟨hinv,?_⟩⟩
    change m-t.naturals 6 < m-u.naturals 6
    rw [hinc]
    omega

private structure OuterInv {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s : MachineState) : Prop where
  pc : s.pc = 27
  core : Core σ ε s
  bound : s.naturals 8 ≤ n
  row : s.naturals 10 = s.naturals 8*m
  rows : Rows σ (s.naturals 8) s
private structure OuterDone {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s : MachineState) : Prop where
  pc : s.pc = 40
  core : Core σ ε s
  inverse : ProgramInverse σ s

private theorem inverse_outer_body (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState)
    (hs : OuterInv σ ε s) (hv : s.naturals 8 < n) :
    ∃ k t, Runs metricProgram k s t ∧ k ≤ 8*(m+1)+5 ∧
      OuterInv σ ε t ∧ t.naturals 8 = s.naturals 8+1 := by
  let v : Fin n := ⟨s.naturals 8,hv⟩
  let u : MachineState := {s with pc := 29,naturals := Function.update s.naturals 6 0}
  have hN : s.naturals 0 = n := hs.core.bases.1
  have hnot : ¬ s.naturals 0 ≤ s.naturals 8 := by rw [hN]; omega
  have hstep1 : step metricProgram s = some {s with pc := 28} := by
    simp [step,metricProgram,hs.pc,hnot]
  have hstep2 : step metricProgram {s with pc := 28} = some u := by
    simp [step,metricProgram,u]
  have huRun : Runs metricProgram 2 s u := Runs.succ hstep1 (Runs.succ hstep2 (Runs.zero u))
  have hu : InnerInv σ ε v u := by
    refine ⟨rfl,⟨?_,hs.core.constants,hs.core.ranks⟩,?_,?_,?_,hs.rows,?_⟩
    · simpa [ProgramBases,u] using hs.core.bases
    · simp [u,v]
    · simpa [u,v] using hs.row
    · simp [u]
    · intro c hc
      simp [u] at hc
  obtain ⟨ki,q,hqi,hq,hcost⟩ := inverse_inner_loop hloop σ ε v u hu
  have hcost' : ki ≤ 8*(m+1) := by simpa [u] using hcost
  let t : MachineState :=
    { q with
      pc := 27
      naturals := Function.update (Function.update q.naturals 10 (q.naturals 10+m))
        8 (q.naturals 8+1) }
  have hM : q.naturals 1 = m := hq.core.bases.2.1
  have hO : q.naturals 3 = 1 := hq.core.bases.2.2.2.1
  have hreplay : chargedReplay 3 q = t := by
    ext a <;> simp [chargedReplay,chargedTick,step,metricProgram,hq.pc,hM,hO,t,
      Function.update_apply]
    all_goals (try split_ifs) <;> simp_all
  have htRun : Runs metricProgram 3 q t := by
    rw [← hreplay]
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have hcore : Core σ ε t := by
    refine ⟨?_,hq.core.constants,hq.core.ranks⟩
    simpa [ProgramBases,t] using hq.core.bases
  have ht : OuterInv σ ε t := by
    refine ⟨rfl,hcore,?_,?_,?_⟩
    · change q.naturals 8+1 ≤ n
      rw [hq.voter]
      exact Nat.succ_le_of_lt v.isLt
    · change q.naturals 10+m = (q.naturals 8+1)*m
      rw [hq.row,hq.voter]
      ring
    · intro w hw
      have hw' : w.val < v.val+1 := by simpa [t,hq.voter] using hw
      by_cases heq : w.val = v.val
      · have hwv : w = v := Fin.ext heq
        subst w
        exact hq.part
      · have hprev : w.val < v.val := by omega
        exact hq.rows w hprev
  have hr1 := hloop.1 metricProgram 2 ki s u q huRun hqi
  have hr2 := hloop.1 metricProgram (2+ki) 3 s q t hr1 htRun
  refine ⟨2+ki+3,t,hr2,by omega,ht,?_⟩
  simpa [t,v] using congrArg (fun a : ℕ => a+1) hq.voter

private theorem inverse_outer_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) (hs : OuterInv σ ε s) :
    ∃ k t, Runs metricProgram k s t ∧ OuterDone σ ε t ∧
      k ≤ (8*(m+1)+5)*(n-s.naturals 8+1) := by
  apply hloop.2 metricProgram (OuterInv σ ε) (OuterDone σ ε)
    (fun u => n-u.naturals 8) (8*(m+1)+5) ?_ s hs
  intro u hu
  have hN : u.naturals 0 = n := hu.core.bases.1
  by_cases hstop : n ≤ u.naturals 8
  · have heq : u.naturals 8 = n := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 40}
    have hstep : step metricProgram u = some t := by
      simp [step,metricProgram,hu.pc,hN,hstop,t]
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by omega,Or.inl ?_⟩
    refine ⟨rfl,⟨hu.core.bases,hu.core.constants,hu.core.ranks⟩,?_⟩
    intro v c
    exact hu.rows v (by simpa [heq] using v.isLt) c c.isLt
  · have hgo : u.naturals 8 < n := Nat.lt_of_not_ge hstop
    obtain ⟨k,t,ht,hcost,hinv,hinc⟩ := inverse_outer_body hloop σ ε u hu hgo
    refine ⟨k,t,ht,hcost,Or.inr ⟨hinv,?_⟩⟩
    change n-t.naturals 8 < n-u.naturals 8
    rw [hinc]
    omega

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε s hpc hv hrow hb hc hranks
  have hs : OuterInv σ ε s := by
    refine ⟨hpc,⟨hb,hc,hranks⟩,?_,?_,?_⟩
    · rw [hv]
      omega
    · rw [hrow,hv,zero_mul]
    · intro v hv'
      rw [hv] at hv'
      omega
  obtain ⟨k,t,hk,ht,hcost⟩ := inverse_outer_loop h.child_0 σ ε s hs
  refine ⟨k,t,hk,ht.pc,ht.core.bases,ht.core.constants,ht.core.ranks,ht.inverse,?_⟩
  have hcost' : k ≤ (8*(m+1)+5)*(n+1) := by simpa [hv] using hcost
  have hN : n+1 ≤ 2*n := by omega
  have hprod := Nat.mul_le_mul_left (8*(m+1)+5) hN
  have hNM : n*2 ≤ n*m := Nat.mul_le_mul_left n hm
  nlinarith

#print axioms from_children
#print axioms inverse_inner_loop
end MetricDistortion.Contracts.Computation_ProgramInverse
