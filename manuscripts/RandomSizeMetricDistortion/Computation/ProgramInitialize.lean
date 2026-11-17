import RandomSizeMetricDistortion.Statements
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace MetricDistortion.Contracts.Computation_ProgramInitialize

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

private theorem code100 : metricProgram[100]?=some (.leNat 5 3 101 109) := by rfl
private theorem code109 : metricProgram[109]?=some (.castNat 7 0) := by rfl
private theorem code110 : metricProgram[110]?=some (.real .mul 10 36 7) := by rfl
private theorem code111 : metricProgram[111]?=some (.real .div 3 0 10) := by rfl
private theorem code112 : metricProgram[112]?=some (.real .mul 33 3 3) := by rfl
private theorem code113 : metricProgram[113]?=some (.real .mul 4 37 33) := by rfl
private theorem code114 : metricProgram[114]?=some (.real .mul 5 38 3) := by rfl
private theorem code115 : metricProgram[115]?=some (.castNat 6 5) := by rfl
private theorem code116 : metricProgram[116]?=some (.natConst 17 0) := by rfl
private theorem code117 : metricProgram[117]?=some (.real .add 8 1 1) := by rfl
private theorem code123 : metricProgram[123]?=some (.real .div 35 2 6) := by rfl
private theorem code124 : metricProgram[124]?=some (.natConst 15 0) := by rfl
private theorem code125 : metricProgram[125]?=some (.leNat 5 15 132 126) := by rfl
private theorem code126 : metricProgram[126]?=some (.natAdd 11 26 15) := by rfl
private theorem code127 : metricProgram[127]?=some (.store 11 35) := by rfl
private theorem code128 : metricProgram[128]?=some (.natAdd 11 28 15) := by rfl
private theorem code129 : metricProgram[129]?=some (.store 11 1) := by rfl
private theorem code130 : metricProgram[130]?=some (.natAdd 15 15 3) := by rfl
private theorem code131 : metricProgram[131]?=some (.jump 125) := by rfl
private theorem code132 : metricProgram[132]?=some (.natConst 18 0) := by rfl
attribute [local simp] code100 code109 code110 code111 code112 code113 code114 code115 code116 code117 code123 code124 code125 code126 code127 code128 code129 code130 code131 code132

private structure InitCore {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (N : ℕ) (s : MachineState) : Prop where
  layout : ProgramLayout n m R.count s
  constants : ProgramConstants ε s
  reduction : ProgramReductionMemory R s
  count : s.naturals 17=N
  delta : s.reals 3=ε/(32*n)
  scale : s.reals 4=2*(ε/(32*n))^2
  eta : s.reals 5=4*(ε/(32*n))
  card : s.reals 6=R.count
  voters : s.reals 7=n

private theorem core_count_frame {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (K N : ℕ) (s t : MachineState) (h : InitCore R ε K s)
    (hc : t.naturals 17=N) (hnm : t.naturalMemory=s.naturalMemory)
    (hnat : ∀ i, i≠17 → t.naturals i=s.naturals i)
    (hreal : ∀ i, i≠8 → i≠9 → t.reals i=s.reals i) : InitCore R ε N t := by
  refine ⟨?_,?_,?_,hc,?_,?_,?_,?_,?_⟩
  · simpa only [ProgramLayout, hnat 0 (by decide), hnat 1 (by decide), hnat 2 (by decide), hnat 3 (by decide), hnat 4 (by decide), hnat 5 (by decide), hnat 20 (by decide), hnat 21 (by decide), hnat 22 (by decide), hnat 23 (by decide), hnat 24 (by decide), hnat 26 (by decide), hnat 27 (by decide), hnat 28 (by decide), hnat 29 (by decide)] using h.layout
  · simpa only [ProgramConstants, hreal 0 (by decide) (by decide), hreal 1 (by decide) (by decide), hreal 2 (by decide) (by decide), hreal 20 (by decide) (by decide), hreal 21 (by decide) (by decide), hreal 22 (by decide) (by decide), hreal 36 (by decide) (by decide), hreal 37 (by decide) (by decide), hreal 38 (by decide) (by decide)] using h.constants
  · simpa only [ProgramReductionMemory,hnm] using h.reduction
  · rw [hreal 3 (by decide) (by decide)]; exact h.delta
  · rw [hreal 4 (by decide) (by decide)]; exact h.scale
  · rw [hreal 5 (by decide) (by decide)]; exact h.eta
  · rw [hreal 6 (by decide) (by decide)]; exact h.card
  · rw [hreal 7 (by decide) (by decide)]; exact h.voters

private theorem parameters {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ)
    (s : MachineState) (hs : ProgramPreprocessed σ ε R s) (hr : 2 ≤ R.count) :
    ∃ t, Runs metricProgram 10 s t ∧ t.pc=118 ∧ InitCore R ε 0 t ∧ t.reals 8=0 := by
  rcases hs with ⟨hpc,hrm,hL,hC,hM⟩
  have hLayout := hL
  have hConstants := hC
  rcases hL with ⟨hn0,hm1,hn2,hn3,hn4,hn5,hn20,hn21,hn22,hn23,hn24,hn26,hn27,hn28,hn29⟩
  rcases hC with ⟨heps,hz,hOne,h20,h21,h22,h36,h37,h38⟩
  let δ := ε/(32*(n : ℝ))
  let t : MachineState :=
    {s with pc := 118, naturals := Function.update s.naturals 17 0, reals := Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update s.reals 7 (n : ℝ)) 10 (32*n)) 3 δ) 33 (δ^2)) 4 (2*δ^2)) 5 (4*δ)) 6 (R.count : ℝ)) 8 0}
  have hgo : ¬R.count ≤ 1 := by omega
  refine ⟨t,?_,rfl,?_,?_⟩
  · apply chunk_sound
    simp (config := {maxSteps := 1000000}) [chunk,step,hpc,hn5,hn3,hgo,hn0,heps,hz,h36,h37,h38,t,δ,applyRealOp,pow_two]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [ProgramLayout,t] using hLayout
    · simpa [ProgramConstants,t] using hConstants
    · exact hM
    · simp [t]
    · simp [t,δ]
    · simp [t,δ]
    · simp [t,δ]
    · simp [t]
    · simp [t]
  · simp [t]

private structure UniformData {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (N i : ℕ) (t : MachineState) : Prop where
  core : InitCore R ε N t
  uniform : t.reals 35=1/(R.count : ℝ)
  index : t.naturals 15=i
  probabilities : ∀ c : Fin R.count, c.val < i → t.memory (m+c.val)=1/(R.count : ℝ)
  accumulated : ∀ c : Fin R.count, c.val < i → t.memory (3*m+c.val)=0

private theorem uniform_pc {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (N i : ℕ) (t : MachineState) (pc : ℕ) (h : UniformData R ε N i t) :
    UniformData R ε N i {t with pc := pc} := by
  exact ⟨⟨h.core.layout,h.core.constants,h.core.reduction,h.core.count,h.core.delta,h.core.scale,h.core.eta,h.core.card,h.core.voters⟩,h.uniform,h.index,h.probabilities,h.accumulated⟩

private theorem uniform_start {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (N : ℕ) (s : MachineState) (hpc : s.pc=123) (h : InitCore R ε N s) :
    ∃ t, Runs metricProgram 2 s t ∧ t.pc=125 ∧ UniformData R ε N 0 t := by
  let t : MachineState := {s with pc := 125, naturals := Function.update s.naturals 15 0, reals := Function.update s.reals 35 (1/(R.count : ℝ))}
  have hone : s.reals 2=1 := h.constants.2.2.1
  refine ⟨t,?_,rfl,?_,?_,?_,?_,?_⟩
  · apply chunk_sound
    simp (config := {maxSteps := 1000000}) [chunk,step,hpc,hone,h.card,t,applyRealOp]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [t,ProgramLayout] using h.layout
    · simpa [t,ProgramConstants] using h.constants
    · exact h.reduction
    · simpa [t] using h.count
    · simpa [t] using h.delta
    · simpa [t] using h.scale
    · simpa [t] using h.eta
    · simpa [t] using h.card
    · simpa [t] using h.voters
  · simp [t]
  · simp [t]
  · intro c hc; omega
  · intro c hc; omega

private theorem uniform_step {n m : ℕ} {σ : Profile n m} (R : Reduction σ)
    (ε : ℝ) (N i : ℕ) (s : MachineState) (hpc : s.pc=125)
    (h : UniformData R ε N i s) (hm : 0 < m) (hi : i < R.count) :
    ∃ t, Runs metricProgram 7 s t ∧ t.pc=125 ∧ UniformData R ε N (i+1) t := by
  let t : MachineState := {s with pc := 125, naturals := Function.update (Function.update s.naturals 11 (3*m+i)) 15 (i+1), memory := Function.update (Function.update s.memory (m+i) (1/(R.count : ℝ))) (3*m+i) 0}
  have hone : s.naturals 3=1 := h.core.layout.2.2.2.1
  have hcard : s.naturals 5=R.count := h.core.layout.2.2.2.2.2.1
  have hbase : s.naturals 26=m := h.core.layout.2.2.2.2.2.2.2.2.2.2.2.1
  have haccum : s.naturals 28=3*m := h.core.layout.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hz : s.reals 1=0 := h.core.constants.2.1
  have hrm : R.count ≤ m := by simpa using Fintype.card_le_of_injective R.embed R.embed.injective
  refine ⟨t,?_,rfl,?_,?_,?_,?_,?_⟩
  · apply chunk_sound
    simp (config := {maxSteps := 1000000}) [chunk,step,hpc,hone,hcard,hbase,haccum,hz,h.uniform,h.index,not_le.mpr hi,t]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [ProgramLayout,t] using h.core.layout
    · exact h.core.constants
    · exact h.core.reduction
    · simpa [t] using h.core.count
    · exact h.core.delta
    · exact h.core.scale
    · exact h.core.eta
    · exact h.core.card
    · exact h.core.voters
  · exact h.uniform
  · simp [t]
  · intro c hc
    have hbank : m+c.val≠3*m+i := by have := c.isLt; omega
    by_cases hci : c.val=i
    · change Function.update (Function.update s.memory (m+i) (1/(R.count : ℝ))) (3*m+i) 0 (m+c.val)=1/(R.count : ℝ)
      rw [Function.update_of_ne hbank,hci,Function.update_self]
    · have hkey : m+c.val≠m+i := by omega
      have hprev : c.val < i := by omega
      change Function.update (Function.update s.memory (m+i) (1/(R.count : ℝ))) (3*m+i) 0 (m+c.val)=1/(R.count : ℝ)
      rw [Function.update_of_ne hbank,Function.update_of_ne hkey]
      exact h.probabilities c hprev
  · intro c hc
    by_cases hci : c.val=i
    · change Function.update (Function.update s.memory (m+i) (1/(R.count : ℝ))) (3*m+i) 0 (3*m+c.val)=0
      rw [hci,Function.update_self]
    · have hnew : 3*m+c.val≠3*m+i := by omega
      have hold : 3*m+c.val≠m+i := by omega
      have hprev : c.val < i := by omega
      change Function.update (Function.update s.memory (m+i) (1/(R.count : ℝ))) (3*m+i) 0 (3*m+c.val)=0
      rw [Function.update_of_ne hnew,Function.update_of_ne hold]
      exact h.accumulated c hprev

private theorem uniform_loop (hloop : Computation_RunRules.Statement)
    {n m : ℕ} {σ : Profile n m} (R : Reduction σ) (ε : ℝ) (N : ℕ)
    (s : MachineState) (hpc : s.pc=125) (h : UniformData R ε N 0 s) (hm : 0 < m) :
    ∃ k t, Runs metricProgram k s t ∧ t.pc=132 ∧ UniformData R ε N R.count t ∧
      k ≤ 7*(R.count+1) := by
  let Inv : MachineState → Prop := fun t => t.pc=125 ∧ ∃ i, i ≤ R.count ∧ UniformData R ε N i t
  let Done : MachineState → Prop := fun t => t.pc=132 ∧ UniformData R ε N R.count t
  let rank : MachineState → ℕ := fun t => R.count-t.naturals 15
  have body : ∀ t, Inv t → ∃ k out, Runs metricProgram k t out ∧ k ≤ 7 ∧
      (Done out ∨ (Inv out ∧ rank out < rank t)) := by
    intro t ht
    obtain ⟨htpc,i,hi,hd⟩ := ht
    by_cases hir : i=R.count
    · let out : MachineState := {t with pc := 132}
      have hcard : t.naturals 5=R.count := hd.core.layout.2.2.2.2.2.1
      have hr : Runs metricProgram 1 t out := by
        apply chunk_sound
        simp (config := {maxSteps := 1000000}) [chunk,step,htpc,hcard,hd.index,hir,out]
      have hdf : UniformData R ε N R.count t := by simpa [hir] using hd
      exact ⟨1,out,hr,by norm_num,Or.inl ⟨rfl,uniform_pc R ε N R.count t 132 hdf⟩⟩
    · have hir' : i < R.count := by omega
      obtain ⟨out,hrun,houtpc,hout⟩ := uniform_step R ε N i t htpc hd hm hir'
      refine ⟨7,out,hrun,le_rfl,Or.inr ⟨⟨houtpc,i+1,by omega,hout⟩,?_⟩⟩
      have hi0 := hd.index
      have hi1 := hout.index
      dsimp [rank]
      omega
  obtain ⟨k,t,hrun,hdone,hcost⟩ := hloop.2 metricProgram Inv Done rank 7 body s ⟨hpc,0,by omega,h⟩
  exact ⟨k,t,hrun,hdone.1,hdone.2,by simpa [rank,h.index] using hcost⟩

theorem from_children (h : Needs) : Statement := by
  intro n m hn hm σ ε hε R s hpre hR2
  let δ : ℝ := ε/(32*n)
  let N : ℕ := Nat.ceil (Real.log R.count/(2*δ^2))
  have hδ : 0 < δ := div_pos hε.1 (by positivity)
  have hrR : (1 : ℝ) < R.count := by exact_mod_cast (show 1 < R.count by omega)
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos (Real.log_pos hrR) (by positivity))
  obtain ⟨D,hD⟩ := h.child_3.1
  obtain ⟨P,htraj,hpos⟩ := h.child_2 n R.count hn R.count_pos D R.profile δ hδ
  obtain ⟨p,hparam,hpcp,hcorep,hzero⟩ := parameters R ε s hpre hR2
  obtain ⟨q,hcount,hpcq,hNq,hzq,hnm,hmem,hnat,hreal⟩ :=
    h.child_1 R.count hR2 δ hδ p hpcp hcorep.layout.2.2.2.1 hcorep.count
      hcorep.constants.2.1 hcorep.scale hcorep.card hzero
  have hcoreq : InitCore R ε N q := core_count_frame R ε 0 N p q hcorep hNq hnm hnat hreal
  obtain ⟨u,hstart,hpcu,hdatau⟩ := uniform_start R ε N q hpcq hcoreq
  obtain ⟨k,z,hloop,hpcz,hdataz,hk⟩ := uniform_loop h.child_0 R ε N u hpcu hdatau (by omega)
  let out : MachineState := {z with pc := 133, naturals := Function.update z.naturals 18 0}
  have hlast : Runs metricProgram 1 z out := by
    apply chunk_sound
    simp [chunk,step,hpcz,out]
  have hc : InitCore R ε N out := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [ProgramLayout,out] using hdataz.core.layout
    · exact hdataz.core.constants
    · exact hdataz.core.reduction
    · simpa [out] using hdataz.core.count
    · exact hdataz.core.delta
    · exact hdataz.core.scale
    · exact hdataz.core.eta
    · exact hdataz.core.card
    · exact hdataz.core.voters
  have hround : ProgramRoundInvariant R ε P 0 out := by
    refine ⟨rfl,hc.layout,hc.constants,hc.reduction,hc.count,?_,?_,hc.delta,hc.scale,hc.eta,hc.card,hc.voters,?_,?_⟩
    · simp [out]
    · simp [out]
    · intro c
      exact (hdataz.probabilities c c.isLt).trans (htraj.1 c).symm
    · intro c
      simpa [out] using hdataz.accumulated c c.isLt
  refine ⟨D,hD,P,htraj,hpos,10+(5*N+2)+2+k+1,out,?_,hround,?_⟩
  · apply h.child_0.1 metricProgram (10+(5*N+2)+2+k) 1 _ _ _ _ hlast
    apply h.child_0.1 metricProgram (10+(5*N+2)+2) k _ _ _ _ hloop
    apply h.child_0.1 metricProgram (10+(5*N+2)) 2 _ _ _ _ hstart
    exact h.child_0.1 metricProgram 10 (5*N+2) _ _ _ hparam hcount
  · have hrm : R.count ≤ m := hpre.2.1
    change 10+(5*N+2)+2+k+1 ≤ 16*(N+m+1)
    nlinarith

#print axioms from_children
end MetricDistortion.Contracts.Computation_ProgramInitialize
