import RandomSizeMetricDistortion.Statements
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramPrune

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

private def KeepBefore {n m : ℕ} (σ : Profile n m) (cut : ℕ) (s : MachineState) : Prop :=
  ∀ c : Fin m, c.val < cut →
    s.naturalMemory (2*n*m+c.val) = if Dominated σ c then 0 else 1
private structure Core {n m : ℕ} (σ : Profile n m) (ε : ℝ) (cut : ℕ)
    (s : MachineState) : Prop where
  bases : ProgramBases n m s
  constants : ProgramConstants ε s
  ranks : ProgramRanks σ s
  inverse : ProgramInverse σ s
  keep : KeepBefore σ cut s

private theorem core_frame {n m : ℕ} (σ : Profile n m) (ε : ℝ) (cut : ℕ)
    (s t : MachineState) (hs : Core σ ε cut s) (hb : ProgramBases n m t)
    (hr : t.reals = s.reals) (hmem : t.naturalMemory = s.naturalMemory) : Core σ ε cut t := by
  refine ⟨hb,?_,?_,?_,?_⟩
  · simpa only [ProgramConstants,hr] using hs.constants
  · simpa only [ProgramRanks,hmem] using hs.ranks
  · simpa only [ProgramInverse,hmem] using hs.inverse
  · simpa only [KeepBefore,hmem] using hs.keep

private structure VoterInv {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c b : Fin m)
    (s : MachineState) : Prop where
  pc : s.pc = 47
  core : Core σ ε c.val s
  candidate : s.naturals 6 = c.val
  opponent : s.naturals 7 = b.val
  flag : s.naturals 19 = 1
  bound : s.naturals 8 ≤ n
  row : s.naturals 10 = s.naturals 8*m
  previous : ∀ v : Fin n, v.val < s.naturals 8 → prefers (σ v) b c
private structure VoterDone {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c b : Fin m)
    (s : MachineState) : Prop where
  core : Core σ ε c.val s
  candidate : s.naturals 6 = c.val
  opponent : s.naturals 7 = b.val
  outcome :
    (s.pc = 56 ∧ s.naturals 19 = 1 ∧ ¬ ∀ v, prefers (σ v) b c) ∨
    (s.pc = 59 ∧ s.naturals 19 = 0 ∧ ∀ v, prefers (σ v) b c)

private theorem voter_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c b : Fin m)
    (s : MachineState) (hs : VoterInv σ ε c b s) :
    ∃ k t, Runs metricProgram k s t ∧ VoterDone σ ε c b t ∧
      k ≤ 9*(n-s.naturals 8+1) := by
  apply hloop.2 metricProgram (VoterInv σ ε c b) (VoterDone σ ε c b)
    (fun u => n-u.naturals 8) 9 ?_ s hs
  intro u hu
  obtain ⟨hN,hM,hZ,hO,hL,hI,hK,hMap,hRev,hOrd,hPB,hTB,hAB,hSB⟩ := hu.core.bases
  by_cases hstop : n ≤ u.naturals 8
  · have hveq : u.naturals 8 = n := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 59,naturals := Function.update u.naturals 19 0}
    have hstep1 : step metricProgram u = some {u with pc := 58} := by
      simp [step,metricProgram,hu.pc,hN,hstop]
    have hstep2 : step metricProgram {u with pc := 58} = some t := by
      simp [step,metricProgram,t]
    have hb : ProgramBases n m t := by simpa [ProgramBases,t] using hu.core.bases
    have hc : Core σ ε c.val t := core_frame σ ε c.val u t hu.core hb rfl rfl
    have hall : ∀ v, prefers (σ v) b c := by
      intro v
      exact hu.previous v (by rw [hveq]; exact v.isLt)
    refine ⟨2,t,Runs.succ hstep1 (Runs.succ hstep2 (Runs.zero t)),by norm_num,Or.inl ?_⟩
    exact ⟨hc,by simpa [t] using hu.candidate,by simpa [t] using hu.opponent,
      Or.inr ⟨rfl,by simp [t],hall⟩⟩
  · have hv : u.naturals 8 < n := Nat.lt_of_not_ge hstop
    let v : Fin n := ⟨u.naturals 8,hv⟩
    have hrc : u.naturalMemory (v.val*m+c.val) = ((σ v) c).val := hu.core.ranks v c
    have hrb : u.naturalMemory (v.val*m+b.val) = ((σ v) b).val := hu.core.ranks v b
    by_cases hcmp : ((σ v) b).val ≤ ((σ v) c).val
    · let t := chargedReplay 6 u
      have hrun : Runs metricProgram 6 u t := by
        apply chargedReplay_trace
        intro j hj
        interval_cases j <;>
          simp [chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
            hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hb : ProgramBases n m t := by
        simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.core.bases
      have hr : t.reals = u.reals := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hmem : t.naturalMemory = u.naturalMemory := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hc : Core σ ε c.val t := core_frame σ ε c.val u t hu.core hb hr hmem
      have hpc : t.pc = 56 := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hC : t.naturals 6 = c.val := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.candidate
      have hB : t.naturals 7 = b.val := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.opponent
      have hF : t.naturals 19 = 1 := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.flag
      have hnot : ¬ ∀ w, prefers (σ w) b c := by
        intro hall
        exact (not_lt_of_ge hcmp) (hall v)
      exact ⟨6,t,hrun,by norm_num,Or.inl ⟨hc,hC,hB,Or.inl ⟨hpc,hF,hnot⟩⟩⟩
    · let t := chargedReplay 9 u
      have hrun : Runs metricProgram 9 u t := by
        apply chargedReplay_trace
        intro j hj
        interval_cases j <;>
          simp [chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
            hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hb : ProgramBases n m t := by
        simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.core.bases
      have hr : t.reals = u.reals := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hmem : t.naturalMemory = u.naturalMemory := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hc : Core σ ε c.val t := core_frame σ ε c.val u t hu.core hb hr hmem
      have hpc : t.pc = 47 := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hC : t.naturals 6 = c.val := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.candidate
      have hB : t.naturals 7 = b.val := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.opponent
      have hF : t.naturals 19 = 1 := by
        simpa [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v] using hu.flag
      have hV : t.naturals 8 = u.naturals 8+1 := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hM,hO,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v]
      have hRow : t.naturals 10 = t.naturals 8*m := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hu.pc,hN,hM,hO,hstop,
          hu.row,hu.candidate,hu.opponent,hrc,hrb,hcmp,v,Nat.add_mul]
      have hprevious : ∀ w : Fin n, w.val < t.naturals 8 → prefers (σ w) b c := by
        intro w hw
        rw [hV] at hw
        by_cases heq : w.val = u.naturals 8
        · have hwv : w = v := Fin.ext heq
          subst w
          exact Nat.lt_of_not_ge hcmp
        · exact hu.previous w (by omega)
      refine ⟨9,t,hrun,le_rfl,Or.inr ⟨⟨hpc,hc,hC,hB,hF,?_,hRow,hprevious⟩,?_⟩⟩
      · rw [hV]
        omega
      · change n-t.naturals 8 < n-u.naturals 8
        rw [hV]
        omega

private structure OpponentInv {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c : Fin m)
    (s : MachineState) : Prop where
  pc : s.pc = 44
  core : Core σ ε c.val s
  candidate : s.naturals 6 = c.val
  flag : s.naturals 19 = 1
  bound : s.naturals 7 ≤ m
  previous : ∀ b : Fin m, b.val < s.naturals 7 → ¬ ∀ v, prefers (σ v) b c
private structure OpponentDone {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c : Fin m)
    (s : MachineState) : Prop where
  pc : s.pc = 59
  core : Core σ ε c.val s
  candidate : s.naturals 6 = c.val
  flag : s.naturals 19 = if Dominated σ c then 0 else 1

private theorem opponent_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (c : Fin m)
    (s : MachineState) (hs : OpponentInv σ ε c s) :
    ∃ k t, Runs metricProgram k s t ∧ OpponentDone σ ε c t ∧
      k ≤ (9*(n+1)+5)*(m-s.naturals 7+1) := by
  apply hloop.2 metricProgram (OpponentInv σ ε c) (OpponentDone σ ε c)
    (fun u => m-u.naturals 7) (9*(n+1)+5) ?_ s hs
  intro u hu
  have hM : u.naturals 1 = m := hu.core.bases.2.1
  by_cases hstop : m ≤ u.naturals 7
  · have hbeq : u.naturals 7 = m := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 59}
    have hstep : step metricProgram u = some t := by simp [step,metricProgram,hu.pc,hM,hstop,t]
    have hnot : ¬ Dominated σ c := by
      rintro ⟨b,hb⟩
      exact hu.previous b (by rw [hbeq]; exact b.isLt) hb
    have hc : Core σ ε c.val t :=
      ⟨hu.core.bases,hu.core.constants,hu.core.ranks,hu.core.inverse,hu.core.keep⟩
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by omega,Or.inl ?_⟩
    exact ⟨rfl,hc,hu.candidate,by simpa only [if_neg hnot] using hu.flag⟩
  · have hb : u.naturals 7 < m := Nat.lt_of_not_ge hstop
    let b : Fin m := ⟨u.naturals 7,hb⟩
    let u0 := chargedReplay 3 u
    have huRun : Runs metricProgram 3 u u0 := by
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
    have huBase : ProgramBases n m u0 := by
      simpa [ProgramBases,u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop] using hu.core.bases
    have huR : u0.reals = u.reals := by
      simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
    have huMem : u0.naturalMemory = u.naturalMemory := by
      simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
    have huCore : Core σ ε c.val u0 := core_frame σ ε c.val u u0 hu.core huBase huR huMem
    have hV0 : u0.naturals 8 = 0 := by
      simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
    have huInv : VoterInv σ ε c b u0 := by
      refine ⟨?_,huCore,?_,?_,?_,?_,?_,?_⟩
      · simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
      · simpa [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop] using hu.candidate
      · simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop,b]
      · simpa [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop] using hu.flag
      · rw [hV0]
        omega
      · simp [u0,chargedReplay,chargedTick,step,metricProgram,hu.pc,hM,hstop]
      · intro v hv
        rw [hV0] at hv
        omega
    obtain ⟨kv,q,hqrun,hq,hqcost⟩ := voter_loop hloop σ ε c b u0 huInv
    have hqcost' : kv ≤ 9*(n+1) := by simpa only [hV0,Nat.sub_zero] using hqcost
    have hqRun := hloop.1 metricProgram 3 kv u u0 q huRun hqrun
    rcases hq.outcome with ⟨hpc,hflag,hnot⟩ | ⟨hpc,hflag,hall⟩
    · let t := chargedReplay 2 q
      have hO : q.naturals 3 = 1 := hq.core.bases.2.2.2.1
      have htRun : Runs metricProgram 2 q t := by
        apply chargedReplay_trace
        intro j hj
        interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hpc]
      have htBase : ProgramBases n m t := by
        simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hpc] using hq.core.bases
      have htR : t.reals = q.reals := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hpc]
      have htMem : t.naturalMemory = q.naturalMemory := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hpc]
      have htCore : Core σ ε c.val t := core_frame σ ε c.val q t hq.core htBase htR htMem
      have hB : t.naturals 7 = u.naturals 7+1 := by
        simp [t,chargedReplay,chargedTick,step,metricProgram,hpc,hO,hq.opponent,b]
      have ht : OpponentInv σ ε c t := by
        refine ⟨?_,htCore,?_,?_,?_,?_⟩
        · simp [t,chargedReplay,chargedTick,step,metricProgram,hpc]
        · simpa [t,chargedReplay,chargedTick,step,metricProgram,hpc] using hq.candidate
        · simpa [t,chargedReplay,chargedTick,step,metricProgram,hpc] using hflag
        · rw [hB]
          omega
        · intro d hd
          rw [hB] at hd
          by_cases heq : d.val = u.naturals 7
          · have hdb : d = b := Fin.ext heq
            subst d
            exact hnot
          · exact hu.previous d (by omega)
      refine ⟨3+kv+2,t,hloop.1 metricProgram (3+kv) 2 u q t hqRun htRun,
        by omega,Or.inr ⟨ht,?_⟩⟩
      change m-t.naturals 7 < m-u.naturals 7
      rw [hB]
      omega
    · have hdom : Dominated σ c := ⟨b,hall⟩
      refine ⟨3+kv,q,hqRun,by omega,Or.inl ⟨hpc,hq.core,hq.candidate,?_⟩⟩
      rw [if_pos hdom]
      exact hflag

private theorem row_address_lt {n m : ℕ} (v : Fin n) (c : Fin m) :
    v.val*m+c.val < n*m := by
  have hh : v.val*m+m ≤ n*m := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m (Nat.succ_le_of_lt v.isLt)
  omega
private structure CandidateInv {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s : MachineState) : Prop where
  pc : s.pc = 41
  core : Core σ ε (s.naturals 6) s
  bound : s.naturals 6 ≤ m
private structure CandidateDone {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s : MachineState) : Prop where
  pc : s.pc = 63
  bases : ProgramBases n m s
  constants : ProgramConstants ε s
  ranks : ProgramRanks σ s
  inverse : ProgramInverse σ s
  keep : ProgramKeep σ s

private theorem candidate_body (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState)
    (hs : CandidateInv σ ε s) (hc : s.naturals 6 < m) :
    ∃ k t, Runs metricProgram k s t ∧ k ≤ (9*(n+1)+5)*(m+1)+7 ∧
      CandidateInv σ ε t ∧ t.naturals 6 = s.naturals 6+1 := by
  let c : Fin m := ⟨s.naturals 6,hc⟩
  have hM : s.naturals 1 = m := hs.core.bases.2.1
  have hnot : ¬ m ≤ s.naturals 6 := by omega
  let u := chargedReplay 3 s
  have huRun : Runs metricProgram 3 s u := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
  have huBase : ProgramBases n m u := by
    simpa [ProgramBases,u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot] using hs.core.bases
  have huR : u.reals = s.reals := by
    simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
  have huMem : u.naturalMemory = s.naturalMemory := by
    simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
  have huCore : Core σ ε c.val u := core_frame σ ε c.val s u hs.core huBase huR huMem
  have hB0 : u.naturals 7 = 0 := by
    simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
  have huInv : OpponentInv σ ε c u := by
    refine ⟨?_,huCore,?_,?_,?_,?_⟩
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot,c]
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hnot]
    · rw [hB0]
      omega
    · intro b hb
      rw [hB0] at hb
      omega
  obtain ⟨kb,q,hqRun,hq,hqcost⟩ := opponent_loop hloop σ ε c u huInv
  have hqcost' : kb ≤ (9*(n+1)+5)*(m+1) := by simpa only [hB0,Nat.sub_zero] using hqcost
  have hK : q.naturals 21 = 2*n*m := hq.core.bases.2.2.2.2.2.2.1
  have hO : q.naturals 3 = 1 := hq.core.bases.2.2.2.1
  let t := chargedReplay 4 q
  let w := 2*n*m+c.val
  have htRun : Runs metricProgram 4 q t := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have hC : t.naturals 6 = s.naturals 6+1 := by
    simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc,hO,hq.candidate,c]
  have htMem : t.naturalMemory = Function.update q.naturalMemory w (q.naturals 19) := by
    simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc,hK,hq.candidate,w]
  have htBase : ProgramBases n m t := by
    simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hq.pc] using hq.core.bases
  have htR : t.reals = q.reals := by
    simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
  have hdouble : 2*n*m = n*m+n*m := by ring
  have htCore : Core σ ε (t.naturals 6) t := by
    refine ⟨htBase,?_,?_,?_,?_⟩
    · simpa only [ProgramConstants,htR] using hq.core.constants
    · intro v d
      have hsmall := row_address_lt v d
      have hne : v.val*m+d.val ≠ w := by dsimp [w]; rw [hdouble]; omega
      rw [htMem,Function.update_of_ne hne]
      exact hq.core.ranks v d
    · intro v d
      have hsmall := row_address_lt v ((σ v) d)
      have hne : n*m+v.val*m+((σ v) d).val ≠ w := by dsimp [w]; rw [hdouble]; omega
      rw [htMem,Function.update_of_ne hne]
      exact hq.core.inverse v d
    · intro d hd
      rw [hC] at hd
      by_cases heq : d.val = c.val
      · have hdc : d = c := Fin.ext heq
        subst d
        rw [htMem]
        change Function.update q.naturalMemory w (q.naturals 19) w = _
        rw [Function.update_self]
        exact hq.flag
      · have hprev : d.val < c.val := by dsimp [c] at *; omega
        have hne : 2*n*m+d.val ≠ w := by dsimp [w]; omega
        rw [htMem,Function.update_of_ne hne]
        exact hq.core.keep d hprev
  have ht : CandidateInv σ ε t := by
    refine ⟨?_,htCore,?_⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hq.pc]
    · rw [hC]
      omega
  have hr1 := hloop.1 metricProgram 3 kb s u q huRun hqRun
  refine ⟨3+kb+4,t,hloop.1 metricProgram (3+kb) 4 s q t hr1 htRun,
    by omega,ht,hC⟩

private theorem candidate_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) (hs : CandidateInv σ ε s) :
    ∃ k t, Runs metricProgram k s t ∧ CandidateDone σ ε t ∧
      k ≤ ((9*(n+1)+5)*(m+1)+7)*(m-s.naturals 6+1) := by
  apply hloop.2 metricProgram (CandidateInv σ ε) (CandidateDone σ ε)
    (fun u => m-u.naturals 6) ((9*(n+1)+5)*(m+1)+7) ?_ s hs
  intro u hu
  have hM : u.naturals 1 = m := hu.core.bases.2.1
  by_cases hstop : m ≤ u.naturals 6
  · have heq : u.naturals 6 = m := le_antisymm hu.bound hstop
    let t : MachineState := {u with pc := 63}
    have hstep : step metricProgram u = some t := by simp [step,metricProgram,hu.pc,hM,hstop,t]
    refine ⟨1,t,Runs.succ hstep (Runs.zero t),by omega,Or.inl ?_⟩
    refine ⟨rfl,hu.core.bases,hu.core.constants,hu.core.ranks,hu.core.inverse,?_⟩
    intro c
    exact hu.core.keep c (by rw [heq]; exact c.isLt)
  · have hgo : u.naturals 6 < m := Nat.lt_of_not_ge hstop
    obtain ⟨k,t,ht,hcost,hinv,hinc⟩ := candidate_body hloop σ ε u hu hgo
    refine ⟨k,t,ht,hcost,Or.inr ⟨hinv,?_⟩⟩
    change m-t.naturals 6 < m-u.naturals 6
    rw [hinc]
    omega

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε s hpc hb hc hranks hinverse
  let u : MachineState := {s with pc := 41,naturals := Function.update s.naturals 6 0}
  have hstep : step metricProgram s = some u := by simp [step,metricProgram,hpc,u]
  have huRun : Runs metricProgram 1 s u := Runs.succ hstep (Runs.zero u)
  have huBase : ProgramBases n m u := by simpa [ProgramBases,u] using hb
  have hu : CandidateInv σ ε u := by
    refine ⟨rfl,⟨huBase,hc,hranks,hinverse,?_⟩,?_⟩
    · intro c hc'
      simp [u] at hc'
    · simp [u]
  obtain ⟨k,t,hk,ht,hcost⟩ := candidate_loop h.child_0 σ ε u hu
  have hcost' : k ≤ ((9*(n+1)+5)*(m+1)+7)*(m+1) := by simpa [u] using hcost
  refine ⟨1+k,t,h.child_0.1 metricProgram 1 k s u t huRun hk,
    ht.pc,ht.bases,ht.constants,ht.ranks,ht.inverse,ht.keep,?_⟩
  have hn1 : 1 ≤ n := hn
  have hm2 : 2*m ≤ m^2 := by nlinarith
  have hm3 : 3 ≤ m^2 := by nlinarith
  have hm4 : 4 ≤ m^2 := by nlinarith
  have hmn : m^2 ≤ n*m^2 := by nlinarith [Nat.mul_le_mul_right (m^2) hn1]
  have hnm : 2*n*m ≤ n*m^2 := by nlinarith [Nat.mul_le_mul_left n hm2]
  have hn3 : 3*n ≤ n*m^2 := by nlinarith [Nat.mul_le_mul_left n hm3]
  have hn4 : 4 ≤ n*m^2 := by nlinarith
  nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramPrune
