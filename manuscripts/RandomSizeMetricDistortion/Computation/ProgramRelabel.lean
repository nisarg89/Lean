import RandomSizeMetricDistortion.Statements
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramRelabel

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

private structure Prefix {n m : ℕ} (σ : Profile n m) (c r : ℕ)
    (f g : ℕ → ℕ) : Prop where
  count : r ≤ c
  bound : ∀ j, j < r → f j < c
  injective : ∀ i, i < r → ∀ j, j < r → f i = f j → i = j
  cover : ∀ d : Fin m, d.val < c → (¬ Dominated σ d ↔ ∃ j, j < r ∧ f j = d.val)
  reverse : ∀ j, j < r → g (f j) = j

private theorem Prefix.skip {n m r : ℕ} {σ : Profile n m} {c : Fin m} {f g : ℕ → ℕ}
    (h : Prefix σ c.val r f g) (hdom : Dominated σ c) : Prefix σ (c.val+1) r f g := by
  refine ⟨by have := h.count; omega,fun j hj => (h.bound j hj).trans (Nat.lt_succ_self _),
    h.injective,?_,h.reverse⟩
  intro d hd
  by_cases heq : d.val = c.val
  · have hdc : d = c := Fin.ext heq
    subst d
    constructor
    · exact fun hn => (hn hdom).elim
    · rintro ⟨j,hj,hjc⟩
      have := h.bound j hj
      omega
  · exact h.cover d (by omega)

private theorem Prefix.keep {n m r : ℕ} {σ : Profile n m} {c : Fin m} {f g : ℕ → ℕ}
    (h : Prefix σ c.val r f g) (hret : ¬ Dominated σ c) :
    Prefix σ (c.val+1) (r+1) (fun j => if j = r then c.val else f j)
      (fun d => if d = c.val then r else g d) := by
  refine ⟨by have := h.count; omega,?_,?_,?_,?_⟩
  · intro j hj
    by_cases heq : j = r
    · simp [heq]
    · have hjr : j < r := by omega
      simpa only [if_neg heq] using (h.bound j hjr).trans (Nat.lt_succ_self _)
  · intro i hi j hj he
    by_cases hiEq : i = r <;> by_cases hjEq : j = r
    · omega
    · have hjr : j < r := by omega
      simp only [if_pos hiEq,if_neg hjEq] at he
      have := h.bound j hjr
      omega
    · have hir : i < r := by omega
      simp only [if_neg hiEq,if_pos hjEq] at he
      have := h.bound i hir
      omega
    · simp only [if_neg hiEq,if_neg hjEq] at he
      exact h.injective i (by omega) j (by omega) he
  · intro d hd
    by_cases heq : d.val = c.val
    · have hdc : d = c := Fin.ext heq
      subst d
      exact ⟨fun _ => ⟨r,by omega,by simp⟩,fun _ => hret⟩
    · have hprev : d.val < c.val := by omega
      constructor
      · intro hD
        obtain ⟨j,hj,hjd⟩ := (h.cover d hprev).1 hD
        refine ⟨j,by omega,?_⟩
        rw [if_neg (by omega : j ≠ r)]
        exact hjd
      · rintro ⟨j,hj,hjd⟩
        have hjr : j < r := by
          by_contra hnot
          have hjEq : j = r := by omega
          simp only [if_pos hjEq] at hjd
          omega
        have hjne : j ≠ r := by omega
        rw [if_neg hjne] at hjd
        exact (h.cover d hprev).2 ⟨j,hjr,hjd⟩
  · intro j hj
    by_cases heq : j = r
    · simp [heq]
    · have hjr : j < r := by omega
      have hfne : f j ≠ c.val := by have := h.bound j hjr; omega
      simp only [if_neg heq,if_neg hfne]
      exact h.reverse j hjr

private theorem Prefix.congr {n m c r : ℕ} {σ : Profile n m} {f g f' g' : ℕ → ℕ}
    (h : Prefix σ c r f g) (hf : ∀ j, j < r → f j = f' j)
    (hg : ∀ d, d < c → g d = g' d) : Prefix σ c r f' g' := by
  refine ⟨h.count,?_,?_,?_,?_⟩
  · intro j hj
    rw [← hf j hj]
    exact h.bound j hj
  · intro i hi j hj he
    apply h.injective i hi j hj
    rwa [hf i hi,hf j hj]
  · intro d hd
    constructor
    · intro hret
      obtain ⟨j,hj,hjd⟩ := (h.cover d hd).1 hret
      exact ⟨j,hj,(hf j hj).symm.trans hjd⟩
    · rintro ⟨j,hj,hjd⟩
      exact (h.cover d hd).2 ⟨j,hj,(hf j hj).trans hjd⟩
  · intro j hj
    rw [← hf j hj,← hg (f j) (h.bound j hj)]
    exact h.reverse j hj

private theorem constants_of_reals {ε : ℝ} {s t : MachineState}
    (hr : t.reals = s.reals) (hc : ProgramConstants ε s) : ProgramConstants ε t := by
  unfold ProgramConstants at hc ⊢
  rw [hr]
  exact hc

private def F (n m : ℕ) (s : MachineState) (j : ℕ) : ℕ :=
  s.naturalMemory (2*n*m+m+j)
private def G (n m : ℕ) (s : MachineState) (d : ℕ) : ℕ :=
  s.naturalMemory (2*n*m+2*m+d)
private structure Core {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) : Prop where
  bases : ProgramBases n m s
  constants : ProgramConstants ε s
  ranks : ProgramRanks σ s
  inverse : ProgramInverse σ s
  keep : ProgramKeep σ s
private theorem core_frame {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s t : MachineState) (hs : Core σ ε s) (hb : ProgramBases n m t)
    (hr : t.reals = s.reals) (hmem : t.naturalMemory = s.naturalMemory) : Core σ ε t := by
  refine ⟨hb,?_,?_,?_,?_⟩
  · simpa only [ProgramConstants,hr] using hs.constants
  · simpa only [ProgramRanks,hmem] using hs.ranks
  · simpa only [ProgramInverse,hmem] using hs.inverse
  · simpa only [ProgramKeep,hmem] using hs.keep
private theorem row_address_lt {n m : ℕ} (v : Fin n) (c : Fin m) :
    v.val*m+c.val < n*m := by
  have hh : v.val*m+m ≤ n*m := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right m (Nat.succ_le_of_lt v.isLt)
  omega
private structure MapInv {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) : Prop where
  pc : s.pc = 65
  core : Core σ ε s
  bound : s.naturals 6 ≤ m
  data : Prefix σ (s.naturals 6) (s.naturals 5) (F n m s) (G n m s)
private structure MapDone {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) : Prop where
  pc : s.pc = 76
  core : Core σ ε s
  data : Prefix σ m (s.naturals 5) (F n m s) (G n m s)

private theorem map_body {n m : ℕ} (σ : Profile n m) (ε : ℝ)
    (s : MachineState) (hs : MapInv σ ε s) (hc : s.naturals 6 < m) :
    ∃ k t, Runs metricProgram k s t ∧ k ≤ 11 ∧ MapInv σ ε t ∧
      t.naturals 6 = s.naturals 6+1 := by
  let c : Fin m := ⟨s.naturals 6,hc⟩
  obtain ⟨hN,hM,hZ,hO,hL,hI,hK,hMap,hRev,hOrd,hPB,hTB,hAB,hSB⟩ := hs.core.bases
  have hstop : ¬ m ≤ s.naturals 6 := by omega
  by_cases hdom : Dominated σ c
  · have hread : s.naturalMemory (2*n*m+s.naturals 6) = 0 := by
      simpa only [if_pos hdom] using hs.core.keep c
    let t := chargedReplay 6 s
    have htRun : Runs metricProgram 6 s t := by
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have htBase : ProgramBases n m t := by
      simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread] using hs.core.bases
    have htR : t.reals = s.reals := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have htMem : t.naturalMemory = s.naturalMemory := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have htCore : Core σ ε t := core_frame σ ε s t hs.core htBase htR htMem
    have hC : t.naturals 6 = s.naturals 6+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hK,hstop,hread]
    have hR : t.naturals 5 = s.naturals 5 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have htData : Prefix σ (t.naturals 6) (t.naturals 5) (F n m t) (G n m t) := by
      rw [hC,hR]
      have hd := hs.data.skip hdom
      unfold F G at hd ⊢
      rw [htMem]
      exact hd
    refine ⟨6,t,htRun,by norm_num,⟨?_,htCore,?_,htData⟩,hC⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    · rw [hC]
      omega
  · have hread : s.naturalMemory (2*n*m+s.naturals 6) = 1 := by
      simpa only [if_neg hdom] using hs.core.keep c
    let t := chargedReplay 11 s
    let wm := 2*n*m+m+s.naturals 5
    let wr := 2*n*m+2*m+s.naturals 6
    have htRun : Runs metricProgram 11 s t := by
      apply chargedReplay_trace
      intro j hj
      interval_cases j <;>
        simp [chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have htBase : ProgramBases n m t := by
      simpa [ProgramBases,t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread] using hs.core.bases
    have htR : t.reals = s.reals := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    have hC : t.naturals 6 = s.naturals 6+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hK,hstop,hread]
    have hR : t.naturals 5 = s.naturals 5+1 := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hO,hK,hstop,hread]
    have htMem : t.naturalMemory = Function.update
        (Function.update s.naturalMemory wm (s.naturals 6)) wr (s.naturals 5) := by
      simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hMap,hRev,hstop,hread,wm,wr]
    have hrm : s.naturals 5 < m := hs.data.count.trans_lt hc
    have hMapRead (j : ℕ) (hj : j < s.naturals 5+1) :
        F n m t j = if j = s.naturals 5 then s.naturals 6 else F n m s j := by
      unfold F
      rw [htMem]
      have hneR : 2*n*m+m+j ≠ wr := by dsimp [wr]; omega
      rw [Function.update_of_ne hneR]
      by_cases heq : j = s.naturals 5
      · subst j
        simp [wm]
      · have hneM : 2*n*m+m+j ≠ wm := by dsimp [wm]; omega
        rw [Function.update_of_ne hneM,if_neg heq]
    have hRevRead (d : ℕ) (hd : d < s.naturals 6+1) :
        G n m t d = if d = s.naturals 6 then s.naturals 5 else G n m s d := by
      unfold G
      rw [htMem]
      by_cases heq : d = s.naturals 6
      · subst d
        simp [wr]
      · have hneR : 2*n*m+2*m+d ≠ wr := by dsimp [wr]; omega
        have hneM : 2*n*m+2*m+d ≠ wm := by dsimp [wm]; omega
        rw [Function.update_of_ne hneR,Function.update_of_ne hneM,if_neg heq]
    have hUntouched (a : ℕ) (ha : a < 2*n*m+m) : t.naturalMemory a = s.naturalMemory a := by
      rw [htMem]
      have hneR : a ≠ wr := by dsimp [wr]; omega
      have hneM : a ≠ wm := by dsimp [wm]; omega
      rw [Function.update_of_ne hneR,Function.update_of_ne hneM]
    have hdouble : 2*n*m = n*m+n*m := by ring
    have htCore : Core σ ε t := by
      refine ⟨htBase,?_,?_,?_,?_⟩
      · exact constants_of_reals htR hs.core.constants
      · intro v d
        rw [hUntouched _ (by have hh := row_address_lt v d; rw [hdouble]; omega)]
        exact hs.core.ranks v d
      · intro v d
        rw [hUntouched _ (by have hh := row_address_lt v ((σ v) d); rw [hdouble]; omega)]
        exact hs.core.inverse v d
      · intro d
        rw [hUntouched _ (by omega)]
        exact hs.core.keep d
    have htData : Prefix σ (t.naturals 6) (t.naturals 5) (F n m t) (G n m t) := by
      rw [hC,hR]
      apply (hs.data.keep hdom).congr
      · intro j hj
        exact (hMapRead j hj).symm
      · intro d hd
        exact (hRevRead d hd).symm
    refine ⟨11,t,htRun,le_rfl,⟨?_,htCore,?_,htData⟩,hC⟩
    · simp [t,chargedReplay,chargedTick,step,metricProgram,hs.pc,hM,hZ,hK,hstop,hread]
    · rw [hC]
      omega

private theorem map_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} (σ : Profile n m) (ε : ℝ) (s : MachineState) (hs : MapInv σ ε s) :
    ∃ k t, Runs metricProgram k s t ∧ MapDone σ ε t ∧ k ≤ 11*(m-s.naturals 6)+1 := by
  have loop : ∀ d : ℕ, ∀ u, m-u.naturals 6 = d → MapInv σ ε u →
      ∃ k t, Runs metricProgram k u t ∧ MapDone σ ε t ∧ k ≤ 11*d+1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro u hrem hu
      have hM : u.naturals 1 = m := hu.core.bases.2.1
      by_cases hstop : m ≤ u.naturals 6
      · have heq : u.naturals 6 = m := le_antisymm hu.bound hstop
        let t : MachineState := {u with pc := 76}
        have hstep : step metricProgram u = some t := by
          simp [step,metricProgram,hu.pc,hM,hstop,t]
        have hcore : Core σ ε t :=
          ⟨hu.core.bases,hu.core.constants,hu.core.ranks,hu.core.inverse,hu.core.keep⟩
        have hdata : Prefix σ m (t.naturals 5) (F n m t) (G n m t) := by
          have hd := hu.data
          rw [heq] at hd
          unfold F G at hd ⊢
          exact hd
        exact ⟨1,t,Runs.succ hstep (Runs.zero t),⟨rfl,hcore,hdata⟩,by omega⟩
      · have hgo : u.naturals 6 < m := Nat.lt_of_not_ge hstop
        obtain ⟨k,v,hk,hcost,hv,hinc⟩ := map_body σ ε u hu hgo
        have hlt : m-v.naturals 6 < d := by rw [hinc]; omega
        obtain ⟨l,t,hl,ht,hlcost⟩ := ih (m-v.naturals 6) hlt v rfl hv
        refine ⟨k+l,t,hloop.1 metricProgram k l u v t hk hl,ht,?_⟩
        have heq : m-v.naturals 6+1 = d := by rw [hinc]; omega
        omega
  exact loop (m-s.naturals 6) s rfl hs

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε s hpc hb hc hranks hinverse hkeep
  let u := chargedReplay 2 s
  have huRun : Runs metricProgram 2 s u := by
    apply chargedReplay_trace
    intro j hj
    interval_cases j <;> simp [chargedReplay,chargedTick,step,metricProgram,hpc]
  have huBase : ProgramBases n m u := by
    simpa [ProgramBases,u,chargedReplay,chargedTick,step,metricProgram,hpc] using hb
  have huR : u.reals = s.reals := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have huMem : u.naturalMemory = s.naturalMemory := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have hcore : Core σ ε u := core_frame σ ε s u ⟨hb,hc,hranks,hinverse,hkeep⟩ huBase huR huMem
  have hC0 : u.naturals 6 = 0 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have hR0 : u.naturals 5 = 0 := by simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
  have hu : MapInv σ ε u := by
    refine ⟨?_,hcore,?_,?_⟩
    · simp [u,chargedReplay,chargedTick,step,metricProgram,hpc]
    · rw [hC0]
      omega
    · refine ⟨?_,?_,?_,?_,?_⟩
      · rw [hC0,hR0]
      · intro j hj
        rw [hR0] at hj
        omega
      · intro i hi
        rw [hR0] at hi
        omega
      · intro c hc'
        rw [hC0] at hc'
        omega
      · intro j hj
        rw [hR0] at hj
        omega
  obtain ⟨k,t,hk,ht,hcost⟩ := map_loop h.child_0 σ ε u hu
  let r := t.naturals 5
  obtain ⟨R0,hR0min⟩ := h.child_1 n m hn (by omega) σ
  let j0 : Fin R0.count := ⟨0,R0.count_pos⟩
  have hret0 : ¬ Dominated σ (R0.embed j0) := by
    have hh : R0.embed j0 ∈ Set.range R0.embed := ⟨j0,rfl⟩
    rw [R0.range_eq] at hh
    exact hh
  obtain ⟨j,hj,hjeq⟩ := (ht.data.cover (R0.embed j0) (R0.embed j0).isLt).1 hret0
  have hrpos : 0 < r := Nat.zero_lt_of_lt hj
  have hmaps : ProgramMaps σ r t := by
    refine ⟨rfl,hrpos,ht.data.count,?_,?_,?_,?_⟩
    · intro i
      exact ht.data.bound i.val i.isLt
    · intro i j he
      exact Fin.ext (ht.data.injective i.val i.isLt j.val j.isLt he)
    · intro c
      constructor
      · intro hret
        obtain ⟨j,hj,hjc⟩ := (ht.data.cover c c.isLt).1 hret
        exact ⟨⟨j,hj⟩,hjc⟩
      · rintro ⟨j,hjc⟩
        exact (ht.data.cover c c.isLt).2 ⟨j.val,j.isLt,hjc⟩
    · intro i
      exact ht.data.reverse i.val i.isLt
  refine ⟨r,2+k,t,h.child_0.1 metricProgram 2 k s u t huRun hk,
    ht.pc,ht.core.bases,ht.core.constants,ht.core.ranks,ht.core.inverse,ht.core.keep,hmaps,?_⟩
  have hcost' : k ≤ 11*m+1 := by simpa only [hC0,Nat.sub_zero] using hcost
  omega

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramRelabel
